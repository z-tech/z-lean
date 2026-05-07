import VC.Src.Merkle.Scheme
import VC.Properties.Probability.RandomOracle

/-!
# §12.3 — Merkle commitment collision lemmas

Book reference: *Building Cryptographic Proofs from Hash Functions*,
`snargs-book.tex` Section 12.3 (Lemmas `simple-mt-colliding-paths` and
`mt-colliding-paths`). Informally: two distinct accepted openings of the
same Merkle root must induce a collision in the random oracle.

## Status (Option B — contrapositive / binding form)

The book's statements are existential — they exhibit two random-oracle
queries that collide. Our `RandomOracle.lean` is presently a placeholder
(see DESIGN.md §3.5; the lazy-sampling distribution arrives in L5/L8), so
quantifying over an RO query trace is premature.

Instead, we adopt the **contrapositive / binding** form: under injectivity
hypotheses on `hashLeaf` / `hashNodes` (passed as theorem parameters), two
distinct accepted single-leaf openings of the same root cannot exist. This
is the form most extractability/binding proofs need anyway, and it is
exactly what the book's Case-1/Case-2 analysis collapses to once the
"otherwise we have a collision" branch is closed by the injectivity
assumption.

The full RO-aware existential remains available as future work; it requires
threading a query trace through `check`. The first lemma below
(`reconstructed_roots_eq`) is the algebraic core that any such proof will
need.

## What is proved

* `reconstructed_roots_eq` — both accepted openings reconstruct to the same
  digest. Trivial-but-load-bearing equality used by every downstream proof.
* `walkCopath_inj` — single-leaf cascade: if `walkCopath` on two
  (acc, sibling-list) pairs of equal length lands on the same digest, then
  under `hashNodes` injectivity the inputs were pairwise equal.
* `simple_mt_colliding_paths_binding` (Lemma 12.3.1, Option B) — under
  `hashLeaf` and `hashNodes` injectivity, two accepted single-leaf openings
  at the same index are forced to be identical. Equivalent to: distinct
  accepted single-leaf openings of the same root → False.
* `mt_colliding_paths_binding` (Lemma 12.3.2, Option B) — multi-leaf
  generalisation; reduces per-index to the single-leaf case.

The Option-A existential-collision forms (book's literal statements) are
left as `sorry` with informative type signatures; they require an RO query
trace which is currently a stub.
-/

namespace MerkleCommitment

variable {H : Type} [MerkleHasher H]

-- ---------------------------------------------------------------------------
-- Algebraic core: shared root ⇒ shared `walkCopath` value
-- ---------------------------------------------------------------------------

/-- Both accepted openings yield the same reconstructed digest. Direct
    consequence of `check` succeeding: `reconstructRoot ... = root` for each
    branch, so the two reconstructions are equal to one another. -/
theorem reconstructed_roots_eq
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (i : Nat)
    (v₀ v₁ : MerkleHasher.Symbol H)
    (s₀ s₁ : MerkleHasher.Salt H)
    (d₀ d₁ : List (MerkleHasher.Digest H))
    (h₀ : mc.reconstructRoot i v₀ s₀ d₀ = root)
    (h₁ : mc.reconstructRoot i v₁ s₁ d₁ = root) :
    mc.reconstructRoot i v₀ s₀ d₀ = mc.reconstructRoot i v₁ s₁ d₁ := by
  rw [h₀, h₁]

-- ---------------------------------------------------------------------------
-- Cascade lemma: `walkCopath` is injective in (acc, siblings) under
-- `hashNodes` injectivity
-- ---------------------------------------------------------------------------

/-- Under injectivity of `hashNodes`, the `walkCopath` accumulator is
    injective in the pair `(acc, sib)` at every step: if two walks of equal
    sibling-list length agree on their final digest, they agreed on the
    initial accumulator and on every sibling along the way.

    Proved by induction on the (shared) sibling-list length, peeling one
    `combineUp` step per recursion. -/
theorem walkCopath_inj
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj : Function.Injective (MerkleHasher.hashNodes mc.hasher)) :
    ∀ (sibs₀ sibs₁ : List (MerkleHasher.Digest H))
      (pos : Nat) (acc₀ acc₁ : MerkleHasher.Digest H),
      sibs₀.length = sibs₁.length →
      mc.walkCopath pos acc₀ sibs₀ = mc.walkCopath pos acc₁ sibs₁ →
      acc₀ = acc₁ ∧ sibs₀ = sibs₁ := by
  intro sibs₀
  induction sibs₀ with
  | nil =>
    intro sibs₁ pos acc₀ acc₁ h_len h_walk
    -- sibs₁ is also nil by length.
    have h₁ : sibs₁ = [] := List.length_eq_zero_iff.mp h_len.symm
    subst h₁
    -- Both walks are `acc` themselves.
    simp [walkCopath] at h_walk
    exact ⟨h_walk, rfl⟩
  | cons sib₀ rest₀ ih =>
    intro sibs₁ pos acc₀ acc₁ h_len h_walk
    -- sibs₁ must be cons of equal length.
    cases sibs₁ with
    | nil => simp at h_len
    | cons sib₁ rest₁ =>
      have h_len' : rest₀.length = rest₁.length := by
        simpa [List.length_cons] using h_len
      -- Unfold one step of `walkCopath` on each side.
      have h_walk' :
          mc.walkCopath ((pos - 1) / 2)
            (mc.combineUp pos acc₀ sib₀) rest₀ =
          mc.walkCopath ((pos - 1) / 2)
            (mc.combineUp pos acc₁ sib₁) rest₁ := by
        simpa [walkCopath] using h_walk
      -- Apply IH at the next level.
      obtain ⟨h_acc_eq, h_rest_eq⟩ :=
        ih rest₁ ((pos - 1) / 2)
          (mc.combineUp pos acc₀ sib₀)
          (mc.combineUp pos acc₁ sib₁)
          h_len' h_walk'
      -- `combineUp pos acc₀ sib₀ = combineUp pos acc₁ sib₁` and `hashNodes`
      -- injective ⇒ equal underlying pair `[left, right]`.
      have h_combine_eq : mc.combineUp pos acc₀ sib₀ = mc.combineUp pos acc₁ sib₁ :=
        h_acc_eq
      -- Unfold `combineUp`, apply hashNodes injectivity.
      have h_pair_eq :
          (if pos % 2 = 1 then ([acc₀, sib₀] : List (MerkleHasher.Digest H))
                          else [sib₀, acc₀]) =
          (if pos % 2 = 1 then [acc₁, sib₁] else [sib₁, acc₁]) := by
        unfold combineUp at h_combine_eq
        by_cases hp : pos % 2 = 1
        · simp [hp] at h_combine_eq
          have := h_inj h_combine_eq
          simp [hp, this]
        · simp [hp] at h_combine_eq
          have := h_inj h_combine_eq
          simp [hp, this]
      -- Read off `acc₀ = acc₁` and `sib₀ = sib₁` from the pair equality.
      by_cases hp : pos % 2 = 1
      · simp [hp] at h_pair_eq
        exact ⟨h_pair_eq.1, by simp [h_pair_eq.2, h_rest_eq]⟩
      · simp [hp] at h_pair_eq
        exact ⟨h_pair_eq.2, by simp [h_pair_eq.1, h_rest_eq]⟩

-- ---------------------------------------------------------------------------
-- §12.3.1 — Simple (single-leaf) case, Option B (binding form)
-- ---------------------------------------------------------------------------

/-- §12.3 simple-mt-colliding-paths (Option B / binding form).

    Two single-leaf openings of the *same index* that both pass `check` for
    the same root are forced to be identical, given collision-free
    `hashLeaf` and `hashNodes`. Equivalent to: distinct accepted openings
    of the same single leaf cannot coexist under injective hashes.

    Book's statement (Lemma 12.3.1) gives an existential collision; under
    injectivity the existential branch is impossible, so the antecedent
    "distinct openings" is itself impossible. -/
theorem simple_mt_colliding_paths_binding
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (root : MerkleHasher.Digest H) (i : Nat)
    (v₀ v₁ : MerkleHasher.Symbol H)
    (s₀ s₁ : MerkleHasher.Salt H)
    (d₀ d₁ : List (MerkleHasher.Digest H))
    (h_len : d₀.length = d₁.length)
    (h₀ : mc.reconstructRoot i v₀ s₀ d₀ = root)
    (h₁ : mc.reconstructRoot i v₁ s₁ d₁ = root) :
    v₀ = v₁ ∧ s₀ = s₁ ∧ d₀ = d₁ := by
  -- Both reconstructions are equal.
  have h_rec : mc.reconstructRoot i v₀ s₀ d₀ = mc.reconstructRoot i v₁ s₁ d₁ :=
    reconstructed_roots_eq mc root i v₀ v₁ s₀ s₁ d₀ d₁ h₀ h₁
  -- `reconstructRoot = walkCopath leafPos (hashLeaf v s) d`. Apply walk
  -- injectivity to peel off the copath, then leaf injectivity to peel
  -- off `(v, s)`.
  unfold reconstructRoot at h_rec
  obtain ⟨h_leaf_eq, h_d_eq⟩ :=
    walkCopath_inj mc h_inj_nodes d₀ d₁
      (MerkleShape.numLeaves mc.shape - 1 + i)
      (MerkleHasher.hashLeaf mc.hasher v₀ s₀)
      (MerkleHasher.hashLeaf mc.hasher v₁ s₁)
      h_len h_rec
  obtain ⟨hv, hs⟩ := h_inj_leaf h_leaf_eq
  exact ⟨hv, hs, h_d_eq⟩

/-- Helper: for a single-index opening, `check = true` reduces to the
    per-triple equality `reconstructRoot ... = root`.

    The proof unfolds `check` and reduces the (single-iteration) `Id.run`
    `for` loop. The decidable equality on `Digest` is fetched from the
    `MerkleHasher` instance. -/
theorem check_singleton_iff
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (i : Nat) (v : MerkleHasher.Symbol H) (s : MerkleHasher.Salt H)
    (d : List (MerkleHasher.Digest H)) :
    mc.check root
        ({ indices := [i], values := [v] } : Opening H)
        ({ entries := [(s, d)] } : OpeningProof H) = true ↔
      mc.reconstructRoot i v s d = root := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  unfold check
  -- The two early-return guards are both false (lengths match), and the
  -- loop has a single iteration.
  simp [Id.run, List.zip]
  by_cases h : mc.reconstructRoot i v s d = root
  · simp [h]; rfl
  · simp [h]

/-- §12.3 simple-mt-colliding-paths (Option B / binding form, lifted to
    `Opening`/`OpeningProof` API).

    For single-element openings (one index), if two openings at the same
    index pass `check` against the same root, then under injective hashes
    the openings agree. -/
theorem simple_mt_colliding_paths
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (root : MerkleHasher.Digest H) (i : Nat)
    (v₀ v₁ : MerkleHasher.Symbol H)
    (s₀ s₁ : MerkleHasher.Salt H)
    (d₀ d₁ : List (MerkleHasher.Digest H))
    (h_len : d₀.length = d₁.length)
    (h_check₀ :
      mc.check root
        ({ indices := [i], values := [v₀] } : Opening H)
        ({ entries := [(s₀, d₀)] } : OpeningProof H) = true)
    (h_check₁ :
      mc.check root
        ({ indices := [i], values := [v₁] } : Opening H)
        ({ entries := [(s₁, d₁)] } : OpeningProof H) = true) :
    v₀ = v₁ ∧ s₀ = s₁ ∧ d₀ = d₁ := by
  have h₀ : mc.reconstructRoot i v₀ s₀ d₀ = root :=
    (check_singleton_iff mc root i v₀ s₀ d₀).mp h_check₀
  have h₁ : mc.reconstructRoot i v₁ s₁ d₁ = root :=
    (check_singleton_iff mc root i v₁ s₁ d₁).mp h_check₁
  exact simple_mt_colliding_paths_binding mc h_inj_leaf h_inj_nodes root i
    v₀ v₁ s₀ s₁ d₀ d₁ h_len h₀ h₁

-- ---------------------------------------------------------------------------
-- §12.3.2 — General multi-leaf case, Option B (binding form)
-- ---------------------------------------------------------------------------

/-- Auxiliary: the imperative loop body inside `check`, expressed as a
    pure recursive function on the list of triples. Returns `true` iff
    every triple's reconstruction equals `root`.

    This is the tail of `check` after the two length guards have passed;
    extracting it as a definition gives us a clean induction target. -/
private def checkLoop {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H) :
    List ((Nat × MerkleHasher.Symbol H) ×
          (MerkleHasher.Salt H × List (MerkleHasher.Digest H))) → Bool
  | [] => true
  | ((i, value), (salt, copath)) :: rest =>
    letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
    if mc.reconstructRoot i value salt copath = root then
      checkLoop mc root rest
    else
      false

/-- `checkLoop` on a triple list returns `true` iff every triple
    reconstructs to `root`. -/
private theorem checkLoop_eq_true_iff
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (triples : List ((Nat × MerkleHasher.Symbol H) ×
                     (MerkleHasher.Salt H × List (MerkleHasher.Digest H)))) :
    mc.checkLoop root triples = true ↔
      ∀ k (h : k < triples.length),
        let t := triples[k]
        mc.reconstructRoot t.1.1 t.1.2 t.2.1 t.2.2 = root := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  induction triples with
  | nil =>
    simp [checkLoop]
  | cons hd tl ih =>
    obtain ⟨⟨i, value⟩, salt, copath⟩ := hd
    constructor
    · intro hloop k hk
      by_cases h : mc.reconstructRoot i value salt copath = root
      · simp [checkLoop, h] at hloop
        match k, hk with
        | 0, _ => simpa using h
        | k+1, hk' =>
          have hk'' : k < tl.length := by simpa [List.length_cons] using hk'
          exact (ih.mp hloop) k hk''
      · simp [checkLoop, h] at hloop
    · intro hall
      have h0 : mc.reconstructRoot i value salt copath = root := by
        have := hall 0 (by simp [List.length_cons])
        simpa using this
      have hrest :
          ∀ k (h : k < tl.length),
            let t := tl[k]
            mc.reconstructRoot t.1.1 t.1.2 t.2.1 t.2.2 = root := by
        intro k hk
        have := hall (k+1) (by simp [List.length_cons]; omega)
        simpa using this
      simp [checkLoop, h0]
      exact ih.mpr hrest

/-- Bridge: the simplified `forIn`-form that `simp [Id.run]` produces from
    the `check` loop body equals our `checkLoop`. We state the lemma in
    the exact `forIn`-shape that `simp` leaves behind, so the rewrite
    step in `check_iff` matches without unification surprises. -/
private theorem checkLoop_eq_forIn
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (triples : List ((Nat × MerkleHasher.Symbol H) ×
                     (MerkleHasher.Salt H × List (MerkleHasher.Digest H)))) :
    (Id.run do
      let r ← forIn triples (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit)
        (fun triple r =>
          have r := r.snd
          letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
          if mc.reconstructRoot triple.1.1 triple.1.2 triple.2.1 triple.2.2 = root then
            (pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _)
          else pure (ForInStep.done ⟨some false, PUnit.unit⟩))
      match r.fst with
      | none => pure true
      | some a => pure a) =
    mc.checkLoop root triples := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  induction triples with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨⟨i, value⟩, salt, copath⟩ := hd
    by_cases h : mc.reconstructRoot i value salt copath = root
    · simp only [checkLoop, h, if_true, List.forIn_cons]
      simpa [Id.run] using ih
    · simp only [checkLoop, h, if_false, List.forIn_cons]
      rfl

/-- Multi-leaf bridge: under matching list-length preconditions,
    `check root op pf = true` iff every per-index reconstruction matches
    `root`. Generalises `check_singleton_iff` to arbitrary opening lengths.

    The length-match hypotheses are passed as preconditions so that the
    indexing into `op.values[k]` and `pf.entries[k]` is well-typed. -/
theorem check_iff
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (op : Opening H) (pf : OpeningProof H)
    (h_iv : op.indices.length = op.values.length)
    (h_ie : op.indices.length = pf.entries.length) :
    mc.check root op pf = true ↔
      ∀ k (h : k < op.indices.length),
        mc.reconstructRoot
          (op.indices[k])
          (op.values[k]'(by omega))
          (pf.entries[k]'(by omega)).1
          (pf.entries[k]'(by omega)).2 = root := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  -- Re-express `check` as: lengths-match AND `checkLoop = true` on the
  -- zipped triple list. Both length-guards in `check` are false here.
  have hne_iv : ¬ op.indices.length ≠ op.values.length := by simp [h_iv]
  have hne_ie : ¬ op.indices.length ≠ pf.entries.length := by simp [h_ie]
  have hcheck_eq :
      mc.check root op pf =
        mc.checkLoop root ((op.indices.zip op.values).zip pf.entries) := by
    unfold check
    simp [Id.run, hne_iv, hne_ie]
    exact checkLoop_eq_forIn mc root _
  rw [hcheck_eq]
  -- Length facts on the zipped list.
  have hlen_zip₁ : (op.indices.zip op.values).length = op.indices.length := by
    simp [List.length_zip, ← h_iv]
  have hlen_zip₂ :
      ((op.indices.zip op.values).zip pf.entries).length = op.indices.length := by
    simp [List.length_zip, hlen_zip₁, ← h_ie]
  rw [checkLoop_eq_true_iff]
  -- Now translate the universal quantifier indexing.
  constructor
  · intro hloop k hk
    have hk_iv : k < op.values.length := by rw [← h_iv]; exact hk
    have hk_e  : k < pf.entries.length := by rw [← h_ie]; exact hk
    have hk_zip : k < ((op.indices.zip op.values).zip pf.entries).length := by
      rw [hlen_zip₂]; exact hk
    have htk := hloop k hk_zip
    have h1 : k < (op.indices.zip op.values).length := by rw [hlen_zip₁]; exact hk
    have hgetzip :
        ((op.indices.zip op.values).zip pf.entries)[k]'hk_zip =
          ((op.indices[k], op.values[k]'hk_iv), pf.entries[k]'hk_e) := by
      rw [List.getElem_zip (h := hk_zip)]
      have : (op.indices.zip op.values)[k]'h1 = (op.indices[k], op.values[k]'hk_iv) :=
        List.getElem_zip (h := h1)
      rw [this]
    rw [hgetzip] at htk
    simpa using htk
  · intro hall k hk
    have hk' : k < op.indices.length := by rw [hlen_zip₂] at hk; exact hk
    have hk_iv : k < op.values.length := by rw [← h_iv]; exact hk'
    have hk_e  : k < pf.entries.length := by rw [← h_ie]; exact hk'
    have h1 : k < (op.indices.zip op.values).length := by rw [hlen_zip₁]; exact hk'
    have hgetzip :
        ((op.indices.zip op.values).zip pf.entries)[k]'hk =
          ((op.indices[k], op.values[k]'hk_iv), pf.entries[k]'hk_e) := by
      rw [List.getElem_zip (h := hk)]
      have : (op.indices.zip op.values)[k]'h1 = (op.indices[k], op.values[k]'hk_iv) :=
        List.getElem_zip (h := h1)
      rw [this]
    rw [hgetzip]
    simpa using hall k hk'

/-- §12.3 mt-colliding-paths (Option B / binding form, multi-leaf version).

    Whenever two general openings agree on their queried indices and both
    accept against the same root, every per-index value/salt/copath
    component coincides — under injectivity of the hash primitives.
    Specialisation of the single-leaf result to each index in turn.

    Statement: for any index `i ∈ op.indices`, the corresponding
    `(value, salt, copath)` triples in the two openings agree. -/
theorem mt_colliding_paths
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (root : MerkleHasher.Digest H)
    (op : Opening H) (pf₀ pf₁ : OpeningProof H)
    (h_len_iv  : op.indices.length = op.values.length)
    (h_len_e₀  : op.indices.length = pf₀.entries.length)
    (h_len_e₁  : op.indices.length = pf₁.entries.length)
    (h_len_d   :
      ∀ k (h : k < op.indices.length),
        ((pf₀.entries[k]'(by omega)).2.length =
         (pf₁.entries[k]'(by omega)).2.length))
    (h_check₀ : mc.check root op pf₀ = true)
    (h_check₁ : mc.check root op pf₁ = true) :
    -- For every queried position, salt + copath digests agree.
    ∀ k (h : k < op.indices.length),
      (pf₀.entries[k]'(by omega)).1 = (pf₁.entries[k]'(by omega)).1 ∧
      (pf₀.entries[k]'(by omega)).2 = (pf₁.entries[k]'(by omega)).2 := by
  -- Strategy: extract per-index `reconstructRoot ... = root` from each
  -- accepted opening via `check_iff`, then apply the single-leaf binding
  -- lemma to read off salt/copath equality (the values agree definitionally
  -- because both openings share the same `op`).
  intro k hk
  have hall₀ := (check_iff mc root op pf₀ h_len_iv h_len_e₀).mp h_check₀
  have hall₁ := (check_iff mc root op pf₁ h_len_iv h_len_e₁).mp h_check₁
  have hk_iv : k < op.values.length := by omega
  have hk_e₀ : k < pf₀.entries.length := by omega
  have hk_e₁ : k < pf₁.entries.length := by omega
  -- Per-index reconstruction equalities.
  have hrec₀ :
      mc.reconstructRoot (op.indices[k])
        (op.values[k]'hk_iv)
        (pf₀.entries[k]'hk_e₀).1
        (pf₀.entries[k]'hk_e₀).2 = root := hall₀ k hk
  have hrec₁ :
      mc.reconstructRoot (op.indices[k])
        (op.values[k]'hk_iv)
        (pf₁.entries[k]'hk_e₁).1
        (pf₁.entries[k]'hk_e₁).2 = root := hall₁ k hk
  -- Apply single-leaf binding with v₀ = v₁ = op.values[k].
  have hd_len :
      (pf₀.entries[k]'hk_e₀).2.length = (pf₁.entries[k]'hk_e₁).2.length :=
    h_len_d k hk
  obtain ⟨_, hs, hd⟩ :=
    simple_mt_colliding_paths_binding mc h_inj_leaf h_inj_nodes root
      (op.indices[k])
      (op.values[k]'hk_iv) (op.values[k]'hk_iv)
      (pf₀.entries[k]'hk_e₀).1 (pf₁.entries[k]'hk_e₁).1
      (pf₀.entries[k]'hk_e₀).2 (pf₁.entries[k]'hk_e₁).2
      hd_len hrec₀ hrec₁
  exact ⟨hs, hd⟩

end MerkleCommitment
