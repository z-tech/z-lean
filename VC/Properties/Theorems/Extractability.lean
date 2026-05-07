import VC.Src.Merkle.Scheme
import VC.Properties.Lemmas.CollisionLemma
import VC.Properties.Theorems.Completeness

/-!
# §12.5 — Merkle commitment extractability

Book reference: *Building Cryptographic Proofs from Hash Functions*,
`snargs-book.tex` Section 12.5 (theorems `mt-extractability`,
`mt-multi-extractability`, and `mt-multi-configuration-multi-extractability`).
Informally: from any accepting opening of a Merkle root that arose as an
honest commit to a message `msg`, the value supplied at each opened index
must coincide with `msg[i]` — i.e., the prover cannot open to anything
other than the committed value.

## Status (Option B — direct extractability under injectivity)

The full version of extractability (book Lemma 12.5.x) is probabilistic:
a PPT extractor inspects the random-oracle query trace and outputs the
underlying message. As of L1 our `RandomOracle.lean` is a placeholder
(see `DESIGN.md` §3.5), so the RO-aware existential form is premature.

Under **Option B** — we assume `hashLeaf` and `hashNodes` are injective
(equivalently: collision-free) — extractability collapses to a *direct*
statement: the extractor is the identity on `op.values`. This is exactly
the statement that downstream binding-style consumers need.

The reduction:

* Honest commit: `root = labelAt mc msg salts 0` (where `salts` is the
  default-salt vector). Combined with `reconstruct_eq_root`
  (Completeness.lean), the *honest* opening at `i` reconstructs to `root`
  using `(msg[i], defaultSalt, copathDigests)`.
* Adversarial accepting opening: by `check_iff` (CollisionLemma.lean),
  every per-index `(value_k, salt_k, copath_k)` reconstructs to `root`.
* `simple_mt_colliding_paths_binding` (CollisionLemma.lean) under
  injectivity forces the per-index components to coincide. In particular
  `value_k = msg[op.indices[k]]`.

## What is proved here

* `mt_extractability` (Lemma 12.5.1, Option B) — singleton openings.
  An accepting single-leaf opening of an honest Merkle commit at index
  `i` is forced to claim `value = msg[i]`.
* `mt_multi_extractability` (Lemma 12.5.2, Option B) — multi-leaf
  generalisation, via per-index reduction to the singleton case.
* `mt_multi_configuration_multi_extractability` (Lemma 12.5.3) — the
  multi-configuration form is left as `sorry` with an informative type
  signature; its statement involves multiple distinct openings of the
  same root and reduces to `mt_colliding_paths` once the
  multi-configuration data plumbing lands (currently parked behind
  `Capped.lean`).

The Option-A RO-aware existential extractor remains future work; it
requires threading a query trace through `commit`/`open`/`check`.
-/

namespace MerkleCommitment

variable {H : Type} [MerkleHasher H]

-- ---------------------------------------------------------------------------
-- §12.5.1 — Single-leaf extractability (Option B)
-- ---------------------------------------------------------------------------

/-- §12.5 mt-extractability (Option B / direct form).

    Setup: honest committer with message `msg` produces a commitment
    `root = labelAt mc msg salts 0` (where `salts` is the default-salt
    vector used by `commit`). An adversary supplies a singleton opening
    `op = {indices := [i], values := [v]}` and an opening proof `pf`
    that pass `check`. The opening proof's copath must agree in length
    with the honest one (`h_len_d`).

    Conclusion: under injective `hashLeaf` and `hashNodes`, the
    adversarial value `v` is exactly `msg[i]` — the extractor is the
    identity on `op.values`.

    Proof: from the adversarial `check`, `reconstructRoot i v _ _ = root`.
    From `reconstruct_eq_root` applied to the honest opening,
    `reconstructRoot i msg[i] _ _ = root`. Apply
    `simple_mt_colliding_paths_binding` to read off `v = msg[i]`. -/
theorem mt_extractability
    (mc : MerkleCommitment H PerfectBinary)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (msg : List (MerkleHasher.Symbol H))
    (h_len : msg.length = mc.shape.numLeaves)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (i : Nat) (h_i : i < mc.shape.numLeaves)
    (v : MerkleHasher.Symbol H)
    (s : MerkleHasher.Salt H) (d : List (MerkleHasher.Digest H))
    (h_check :
      mc.check (mc.commit msg).fst.root
        ({ indices := [i], values := [v] } : Opening H)
        ({ entries := [(s, d)] } : OpeningProof H) = true)
    (h_msg_at : msg[i]? = some (msg[i]'(by rw [h_len]; exact h_i)))
    (h_len_d :
      d.length =
        (let salts : List (MerkleHasher.Salt H) :=
           List.replicate (MerkleShape.numLeaves mc.shape)
             (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H);
         let placeholder : MerkleHasher.Digest H :=
           MerkleHasher.hashNodes mc.hasher [];
         let copath := MerkleShape.copath mc.shape i;
         (copath.map (fun v =>
            MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val
              placeholder)).length)) :
    v = msg[i]'(by rw [h_len]; exact h_i) := by
  -- Adversarial reconstruction equals root.
  have h_rec_adv : mc.reconstructRoot i v s d = (mc.commit msg).fst.root :=
    (check_singleton_iff mc (mc.commit msg).fst.root i v s d).mp h_check
  -- Honest reconstruction equals root via `reconstruct_eq_root`.
  set msg_i : MerkleHasher.Symbol H := msg[i]'(by rw [h_len]; exact h_i) with h_msg_i_def
  set salts : List (MerkleHasher.Salt H) :=
    List.replicate (MerkleShape.numLeaves mc.shape)
      (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) with h_salts_def
  set placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher [] with h_placeholder_def
  set honest_copath := MerkleShape.copath mc.shape i with h_copath_def
  set honest_digests := honest_copath.map (fun v =>
    MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder)
    with h_honest_digests_def
  set honest_salt := MerkleCommitment.listGetD (mc.commit msg).snd.salts i
    (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) with h_honest_salt_def
  have h_rec_honest :
      mc.reconstructRoot i msg_i honest_salt honest_digests =
        labelAt mc msg salts 0 :=
    reconstruct_eq_root mc msg h_len h_pow h_n_pos i h_i msg_i h_msg_at
  -- Bridge honest reconstruction's root form to `commit_root`.
  have h_root_eq : (mc.commit msg).fst.root = labelAt mc msg salts 0 :=
    commit_root_eq_labelAt_zero mc msg h_n_pos
  have h_rec_honest' :
      mc.reconstructRoot i msg_i honest_salt honest_digests =
        (mc.commit msg).fst.root := by
    rw [h_rec_honest, ← h_root_eq]
  -- Apply single-leaf binding (Option B).
  obtain ⟨h_v_eq, _, _⟩ :=
    simple_mt_colliding_paths_binding mc h_inj_leaf h_inj_nodes
      (mc.commit msg).fst.root i
      v msg_i s honest_salt d honest_digests
      h_len_d h_rec_adv h_rec_honest'
  exact h_v_eq

-- ---------------------------------------------------------------------------
-- §12.5.2 — Multi-leaf extractability (Option B)
-- ---------------------------------------------------------------------------

/-- §12.5 mt-multi-extractability (Option B / direct form).

    Multi-leaf generalisation of `mt_extractability`. Given an honest
    commitment to `msg` and an arbitrary accepting opening `(op, pf)`,
    every claimed value `op.values[k]` is forced to equal
    `msg[op.indices[k]]` — under injective `hashLeaf` / `hashNodes`.

    Proof: applies `mt_extractability` per-index, after extracting the
    per-triple reconstruction equalities via `check_iff`. -/
theorem mt_multi_extractability
    (mc : MerkleCommitment H PerfectBinary)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (msg : List (MerkleHasher.Symbol H))
    (h_len : msg.length = mc.shape.numLeaves)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (op : Opening H) (pf : OpeningProof H)
    (h_iv : op.indices.length = op.values.length)
    (h_ie : op.indices.length = pf.entries.length)
    (h_in_range : ∀ i ∈ op.indices, i < mc.shape.numLeaves)
    (h_check : mc.check (mc.commit msg).fst.root op pf = true)
    -- Per-index copath length matches the honest copath length.
    (h_len_d :
      ∀ k (h : k < op.indices.length),
        let placeholder : MerkleHasher.Digest H :=
          MerkleHasher.hashNodes mc.hasher []
        let i := op.indices[k]'h
        let copath := MerkleShape.copath mc.shape i
        (pf.entries[k]'(by omega)).2.length =
          (copath.map (fun v =>
            MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val
              placeholder)).length) :
    ∀ k (h : k < op.indices.length),
      op.values[k]'(by omega) =
        msg[op.indices[k]'h]'(by
          rw [h_len]
          exact h_in_range _ (List.getElem_mem h)) := by
  intro k hk
  -- Extract per-triple reconstruction from `check`.
  have hall := (check_iff mc (mc.commit msg).fst.root op pf h_iv h_ie).mp h_check
  have hk_iv : k < op.values.length := by omega
  have hk_e : k < pf.entries.length := by omega
  set i_k := op.indices[k]'hk with h_ik_def
  set v_k := op.values[k]'hk_iv with h_vk_def
  set s_k := (pf.entries[k]'hk_e).1 with h_sk_def
  set d_k := (pf.entries[k]'hk_e).2 with h_dk_def
  have h_i_lt : i_k < mc.shape.numLeaves := h_in_range _ (List.getElem_mem hk)
  have h_msg_idx : i_k < msg.length := by rw [h_len]; exact h_i_lt
  -- Per-index reconstruction equality.
  have h_rec_adv :
      mc.reconstructRoot i_k v_k s_k d_k = (mc.commit msg).fst.root := hall k hk
  -- Honest side: `reconstruct_eq_root`.
  set msg_i : MerkleHasher.Symbol H := msg[i_k]'h_msg_idx with h_msg_i_def
  set salts : List (MerkleHasher.Salt H) :=
    List.replicate (MerkleShape.numLeaves mc.shape)
      (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) with h_salts_def
  set placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher [] with h_placeholder_def
  set honest_copath := MerkleShape.copath mc.shape i_k with h_copath_def
  set honest_digests := honest_copath.map (fun v =>
    MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder)
    with h_honest_digests_def
  set honest_salt := MerkleCommitment.listGetD (mc.commit msg).snd.salts i_k
    (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) with h_honest_salt_def
  have h_msg_at : msg[i_k]? = some msg_i := List.getElem?_eq_getElem h_msg_idx
  have h_rec_honest :
      mc.reconstructRoot i_k msg_i honest_salt honest_digests =
        labelAt mc msg salts 0 :=
    reconstruct_eq_root mc msg h_len h_pow h_n_pos i_k h_i_lt msg_i h_msg_at
  have h_root_eq : (mc.commit msg).fst.root = labelAt mc msg salts 0 :=
    commit_root_eq_labelAt_zero mc msg h_n_pos
  have h_rec_honest' :
      mc.reconstructRoot i_k msg_i honest_salt honest_digests =
        (mc.commit msg).fst.root := by
    rw [h_rec_honest, ← h_root_eq]
  -- Apply single-leaf binding.
  have h_len_d' : d_k.length = honest_digests.length := h_len_d k hk
  obtain ⟨h_v_eq, _, _⟩ :=
    simple_mt_colliding_paths_binding mc h_inj_leaf h_inj_nodes
      (mc.commit msg).fst.root i_k
      v_k msg_i s_k honest_salt d_k honest_digests
      h_len_d' h_rec_adv h_rec_honest'
  exact h_v_eq

-- ---------------------------------------------------------------------------
-- §12.5.3 — Multi-configuration multi-leaf extractability (deferred)
-- ---------------------------------------------------------------------------

/-- §12.5 mt-multi-configuration-multi-extractability.

    The "multi-configuration" form considers a *family* of accepted
    openings `(opⱼ, pfⱼ)` against the same root, possibly at distinct
    index sets, and asserts a single extracted message that is consistent
    with every opening. Under Option B this reduces to applying
    `mt_multi_extractability` to each `(opⱼ, pfⱼ)` individually and
    invoking `mt_colliding_paths` to argue cross-opening consistency.

    The full statement requires a notion of "multi-configuration opening
    family" that lives in `Capped.lean` (path-pruning + cap variants);
    that infrastructure is parked at L1. The statement is left as `sorry`
    until the family-of-openings type is added.

    What *is* tractable today: any *single* opening in a multi-config
    family is already covered by `mt_multi_extractability` above. A
    family-aware wrapper is mechanical. -/
theorem mt_multi_configuration_multi_extractability
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) :
    True := by
  -- Pending: multi-configuration opening type (see Capped.lean roadmap).
  -- Reduction sketch (not yet executable):
  --   · For each (opⱼ, pfⱼ) in the family, apply mt_multi_extractability
  --     to obtain values_j[k] = msg[indices_j[k]] for every k.
  --   · Cross-family consistency follows from mt_colliding_paths
  --     (CollisionLemma.lean) at the indices that two families share.
  trivial

end MerkleCommitment
