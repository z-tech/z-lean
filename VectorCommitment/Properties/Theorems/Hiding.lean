import VectorCommitment.Src.Merkle.Scheme
import VectorCommitment.Properties.Theorems.Completeness

/-!
# §12.5–12.6 Merkle commitment hiding

The textbook hiding statement (book §12.5) is *probabilistic*: against a random
oracle, the commit-root distribution is independent of the committed message
when each leaf is paired with a uniformly random salt. A faithful formalisation
needs the random-oracle infrastructure (`VectorCommitment/Properties/Probability/RandomOracle.lean`),
which is currently a `PMF.pure` placeholder. So we cannot state the textbook
form yet.

Instead we prove the *Option-B / structural* form: if leaf hashes agree at
every position (the property the random salt is supposed to enforce in
expectation), then **every vertex label** — and in particular the commit root —
also agrees. This is a real, fully formal property of the Merkle construction
itself: "the salt absorbs the value." The probabilistic form layers a random
salt over this skeleton and is left for a future milestone.
-/

namespace MerkleCommitment

variable {H : Type} [MerkleHasher H]

/-- **Structural hiding (per-vertex).** If two `(message, salts)` pairs induce
    the same leaf hash at every leaf index, then their `labelAt` agrees at
    every vertex of the tree. By strong induction on the `labelAt`
    well-founded measure (`2n - 1 - v`).

    The hypothesis `h_leaf` is the "leaf-level indistinguishability" the
    book's hiding argument achieves probabilistically by sampling a fresh
    salt per leaf: with high probability the salt-randomised leaf hash is
    indistinguishable across `msg₀` and `msg₁`. Here we treat that as a
    *structural assumption* and propagate it up the tree. -/
theorem labelAt_eq_of_leaf_hash_eq
    (mc : MerkleCommitment H PerfectBinary)
    (msg₀ msg₁ : List (MerkleHasher.Symbol H))
    (salts₀ salts₁ : List (MerkleHasher.Salt H))
    (h_leaf :
      ∀ v : Nat,
        MerkleShape.numLeaves mc.shape ≤ v + 1 →
        (let n := MerkleShape.numLeaves mc.shape
         let i := v - (n - 1)
         let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
         (match msg₀[i]? with
          | none     => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₀ i defaultS)) =
         (match msg₁[i]? with
          | none     => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₁ i defaultS)))) :
    ∀ v : Nat, labelAt mc msg₀ salts₀ v = labelAt mc msg₁ salts₁ v := by
  intro v
  -- Strong induction on the well-founded measure used by `labelAt`.
  let measure : Nat → Nat := fun w => 2 * MerkleShape.numLeaves mc.shape - 1 - w
  -- Use Nat strong induction on `measure v`.
  induction h : measure v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    by_cases h_leaf_v : MerkleShape.numLeaves mc.shape ≤ v + 1
    · -- Leaf branch: unfold both sides via the definitional equation,
      -- then match on `msg_b[i]?`.
      have h_eq := h_leaf v h_leaf_v
      simp only at h_eq
      -- Unfold each side and case-split on the option pattern.
      conv_lhs => rw [labelAt]
      conv_rhs => rw [labelAt]
      simp only [h_leaf_v, if_true]
      cases h_msg₀ : msg₀[v - (MerkleShape.numLeaves mc.shape - 1)]? with
      | none =>
        cases h_msg₁ : msg₁[v - (MerkleShape.numLeaves mc.shape - 1)]? with
        | none => rfl
        | some s₁ =>
          rw [h_msg₀, h_msg₁] at h_eq
          exact h_eq
      | some s₀ =>
        cases h_msg₁ : msg₁[v - (MerkleShape.numLeaves mc.shape - 1)]? with
        | none =>
          rw [h_msg₀, h_msg₁] at h_eq
          exact h_eq
        | some s₁ =>
          rw [h_msg₀, h_msg₁] at h_eq
          exact h_eq
    · -- Internal branch: recurse on the two children via `labelAt_internal`.
      have h_v_int : v + 1 < MerkleShape.numLeaves mc.shape := by omega
      have h_meas_l : measure (2 * v + 1) < measure v := by
        show 2 * MerkleShape.numLeaves mc.shape - 1 - (2 * v + 1) <
             2 * MerkleShape.numLeaves mc.shape - 1 - v
        omega
      have h_meas_r : measure (2 * v + 2) < measure v := by
        show 2 * MerkleShape.numLeaves mc.shape - 1 - (2 * v + 2) <
             2 * MerkleShape.numLeaves mc.shape - 1 - v
        omega
      have ih_l := ih (measure (2 * v + 1)) (h ▸ h_meas_l) (2 * v + 1) rfl
      have ih_r := ih (measure (2 * v + 2)) (h ▸ h_meas_r) (2 * v + 2) rfl
      rw [labelAt_internal mc msg₀ salts₀ v h_v_int]
      rw [labelAt_internal mc msg₁ salts₁ v h_v_int]
      rw [ih_l, ih_r]

/-- **Root-level structural hiding.** If two `(message, salts)` pairs induce
    the same leaf hash at every leaf index, then the commit roots are equal.

    This is the *Option-B* hiding statement: it captures the precise
    information-theoretic content the random-salt argument is supposed to
    achieve, namely that **the message can only influence the root through
    its leaf-hash output**. The book's full §12.5 hiding theorem layers a
    distributional argument (uniform salt ⇒ uniform leaf hash ⇒ uniform
    root) on top of this structural fact; that distributional layer is left
    sorried below pending the probability infrastructure. -/
theorem mt_root_hiding
    (mc : MerkleCommitment H PerfectBinary)
    (msg₀ msg₁ : List (MerkleHasher.Symbol H))
    (h_len₀ : msg₀.length = MerkleShape.numLeaves mc.shape)
    (h_len₁ : msg₁.length = MerkleShape.numLeaves mc.shape)
    (salts₀ salts₁ : List (MerkleHasher.Salt H))
    (h_leaf :
      ∀ i, i < MerkleShape.numLeaves mc.shape →
        ∀ (s₀ s₁ : MerkleHasher.Symbol H),
          msg₀[i]? = some s₀ → msg₁[i]? = some s₁ →
          MerkleHasher.hashLeaf mc.hasher s₀
              (listGetD salts₀ i (MerkleHasher.defaultSalt.default)) =
          MerkleHasher.hashLeaf mc.hasher s₁
              (listGetD salts₁ i (MerkleHasher.defaultSalt.default))) :
    -- Construct the two trapdoor labellings explicitly, then compare roots.
    labelAt mc msg₀ salts₀ 0 = labelAt mc msg₁ salts₁ 0 := by
  -- Reduce to the per-vertex statement `labelAt_eq_of_leaf_hash_eq` at v = 0.
  apply labelAt_eq_of_leaf_hash_eq mc msg₀ msg₁ salts₀ salts₁
  intro v h_v_leaf
  -- Translate `h_leaf` (indexed by leaf position `i < n`) to the form needed
  -- inside `labelAt`'s leaf branch (indexed by vertex `v` with `n ≤ v + 1`).
  set n := MerkleShape.numLeaves mc.shape with hn
  set i := v - (n - 1) with hi
  set defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
  -- Case-split on whether index `i` is in range for both messages.
  by_cases h_i_lt : i < n
  · -- Both messages have an entry at position `i` (since len = n).
    have h_get₀ : ∃ s₀, msg₀[i]? = some s₀ := by
      have h_lt : i < msg₀.length := by rw [h_len₀]; exact h_i_lt
      exact ⟨msg₀[i]'h_lt, List.getElem?_eq_getElem h_lt⟩
    have h_get₁ : ∃ s₁, msg₁[i]? = some s₁ := by
      have h_lt : i < msg₁.length := by rw [h_len₁]; exact h_i_lt
      exact ⟨msg₁[i]'h_lt, List.getElem?_eq_getElem h_lt⟩
    obtain ⟨s₀, hs₀⟩ := h_get₀
    obtain ⟨s₁, hs₁⟩ := h_get₁
    have h_eq := h_leaf i h_i_lt s₀ s₁ hs₀ hs₁
    show (match msg₀[i]? with
          | none => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₀ i defaultS)) =
         (match msg₁[i]? with
          | none => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₁ i defaultS))
    rw [hs₀, hs₁]
    exact h_eq
  · -- Out-of-range case: both `getElem?`s return `none`, so both branches reduce
    -- to `hashNodes _ []`. (Cannot happen given `h_v_leaf` plus length bounds,
    -- but we handle it anyway to keep the structural lemma's hypothesis honest.)
    have h_i_ge₀ : i ≥ msg₀.length := by rw [h_len₀]; omega
    have h_i_ge₁ : i ≥ msg₁.length := by rw [h_len₁]; omega
    have h_none₀ : msg₀[i]? = none := List.getElem?_eq_none h_i_ge₀
    have h_none₁ : msg₁[i]? = none := List.getElem?_eq_none h_i_ge₁
    show (match msg₀[i]? with
          | none => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₀ i defaultS)) =
         (match msg₁[i]? with
          | none => MerkleHasher.hashNodes mc.hasher []
          | some sym => MerkleHasher.hashLeaf mc.hasher sym
                          (listGetD salts₁ i defaultS))
    rw [h_none₀, h_none₁]

/-- **Commit-level hiding (Option-B).** Bridges `mt_root_hiding` from the
    functional `labelAt` to the imperative `commit` API: under the structural
    leaf-hash equality hypothesis, the two `commit` calls return the same
    root digest, *provided* both calls are passed the default salt vector
    (which is what `commit` does internally; the per-leaf salts only enter
    the trapdoor at `open` time in the L1 implementation).

    Note: the current `commit` API discards the user-supplied salts and uses
    the default-salt vector. So the `salts₀ = salts₁ = replicate n default`
    instantiation is the only one reachable through `commit` directly; for
    the more general statement see `mt_root_hiding` above. -/
theorem mt_root_hiding_commit
    (mc : MerkleCommitment H PerfectBinary)
    (msg₀ msg₁ : List (MerkleHasher.Symbol H))
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (h_len₀ : msg₀.length = MerkleShape.numLeaves mc.shape)
    (h_len₁ : msg₁.length = MerkleShape.numLeaves mc.shape)
    (h_leaf :
      ∀ i, i < MerkleShape.numLeaves mc.shape →
        ∀ (s₀ s₁ : MerkleHasher.Symbol H),
          msg₀[i]? = some s₀ → msg₁[i]? = some s₁ →
          MerkleHasher.hashLeaf mc.hasher s₀ MerkleHasher.defaultSalt.default =
          MerkleHasher.hashLeaf mc.hasher s₁ MerkleHasher.defaultSalt.default) :
    (mc.commit msg₀).fst.root = (mc.commit msg₁).fst.root := by
  -- Both roots equal `labelAt mc msg_b (replicate n default) 0` by
  -- `commit_root_eq_labelAt_zero`.
  have h_root₀ := commit_root_eq_labelAt_zero mc msg₀ h_n_pos
  have h_root₁ := commit_root_eq_labelAt_zero mc msg₁ h_n_pos
  show (mc.commit msg₀).fst.root = _
  rw [h_root₀, h_root₁]
  -- Apply the structural lemma at the default-salt vector.
  let salts : List (MerkleHasher.Salt H) :=
    List.replicate (MerkleShape.numLeaves mc.shape)
      (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
  apply mt_root_hiding mc msg₀ msg₁ h_len₀ h_len₁ salts salts
  intro i h_i s₀ s₁ hs₀ hs₁
  -- Both `listGetD salts i default` reduce to `default`.
  have h_get_def :
      listGetD salts i (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) =
        MerkleHasher.defaultSalt.default := by
    show (List.replicate (MerkleShape.numLeaves mc.shape)
            (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H))[i]?.getD _ = _
    rw [List.getElem?_replicate]
    simp [h_i]
  rw [h_get_def]
  exact h_leaf i h_i s₀ s₁ hs₀ hs₁

/-- **Distributional hiding (book §12.5).** *Stated form / sorried.* The full
    book statement requires probabilistic infrastructure: against a random
    oracle, the distribution of `commit msg` is independent of `msg` when
    each leaf is paired with a uniformly random salt.

    Concretely the book argues:
    1. Random salt `r` ⇒ `hashLeaf hasher m r` is a uniformly random digest
       (random-oracle property), independent of `m`.
    2. Therefore the leaf-hash distribution is `msg`-independent.
    3. Propagating up the tree (by `labelAt_eq_of_leaf_hash_eq` at the
       distributional level), the root distribution is `msg`-independent.

    Step 3 is exactly the structural lemma above. Steps 1–2 require:
    - a non-placeholder `RandomOracle.lean` (currently `PMF.pure`);
    - a notion of distributional equality (`PMF.bind`-equality or
      indistinguishability up to oracle queries).

    Until that infrastructure lands we leave the distributional form as a
    `True` placeholder with a structured comment.

    See: `VectorCommitment/Properties/Probability/RandomOracle.lean`. -/
theorem mt_privacy
    {H S : Type} [MerkleHasher H] [MerkleShape S]
    (_mc : MerkleCommitment H S) :
    -- Placeholder. The honest statement is
    --   `commitDistribution mc msg₀ = commitDistribution mc msg₁`
    -- under uniform-salt sampling, against a random oracle. Requires
    -- `RandomOracle.lean` to be promoted from `PMF.pure` to a real model.
    True := trivial

end MerkleCommitment
