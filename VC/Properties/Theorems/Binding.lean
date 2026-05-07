import VC.Src.Merkle.Scheme
import Mathlib.Logic.Function.Basic

/-!
# §12.4 — Merkle commitment binding

Book reference: *Building Cryptographic Proofs from Hash Functions*,
`snargs-book.tex` Section 12.4 (theorems `mt-binding` and
`mt-other-binding`).

Both statements are corollaries of the §12.3 collision lemmas, in their
Option-B (binding / contrapositive) form: under collision-freeness of
`hashLeaf` and `hashNodes`, two distinct accepted openings of the same
root cannot exist.

## Note on dependencies

The §12.3 collision lemma `simple_mt_colliding_paths_binding` lives in
`VC/Properties/Lemmas/CollisionLemma.lean`. To keep this file
self-contained (and to avoid coupling to the in-progress multi-leaf
section of `CollisionLemma.lean`), the building blocks we need are
re-derived here in a `private` namespace at the top:

* `walkCopath_inj_local` — cascade injectivity of `walkCopath` under
  injective `hashNodes`.
* `simple_binding_core` — single-leaf binding at the
  `reconstructRoot` level.
* `check_singleton_iff_local` — bridge from `check = true` (singleton
  opening) to `reconstructRoot ... = root`.

These are direct copies of the corresponding helpers in
`CollisionLemma.lean`; both files agree on their statements.
-/

namespace MerkleCommitment

variable {H : Type} [MerkleHasher H]

-- ---------------------------------------------------------------------------
-- Local helpers (mirroring CollisionLemma.lean)
-- ---------------------------------------------------------------------------

/-- Cascade injectivity: under injective `hashNodes`, `walkCopath` is
    injective in the pair `(acc, sib-list)` at every step. -/
private theorem walkCopath_inj_local
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
    have h₁ : sibs₁ = [] := List.length_eq_zero_iff.mp h_len.symm
    subst h₁
    simp [walkCopath] at h_walk
    exact ⟨h_walk, rfl⟩
  | cons sib₀ rest₀ ih =>
    intro sibs₁ pos acc₀ acc₁ h_len h_walk
    cases sibs₁ with
    | nil => simp at h_len
    | cons sib₁ rest₁ =>
      have h_len' : rest₀.length = rest₁.length := by
        simpa [List.length_cons] using h_len
      have h_walk' :
          mc.walkCopath ((pos - 1) / 2)
            (mc.combineUp pos acc₀ sib₀) rest₀ =
          mc.walkCopath ((pos - 1) / 2)
            (mc.combineUp pos acc₁ sib₁) rest₁ := by
        simpa [walkCopath] using h_walk
      obtain ⟨h_acc_eq, h_rest_eq⟩ :=
        ih rest₁ ((pos - 1) / 2)
          (mc.combineUp pos acc₀ sib₀)
          (mc.combineUp pos acc₁ sib₁)
          h_len' h_walk'
      have h_combine_eq : mc.combineUp pos acc₀ sib₀ = mc.combineUp pos acc₁ sib₁ :=
        h_acc_eq
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
      by_cases hp : pos % 2 = 1
      · simp [hp] at h_pair_eq
        exact ⟨h_pair_eq.1, by simp [h_pair_eq.2, h_rest_eq]⟩
      · simp [hp] at h_pair_eq
        exact ⟨h_pair_eq.2, by simp [h_pair_eq.1, h_rest_eq]⟩

/-- Single-leaf binding at the `reconstructRoot` level: under injective
    `hashLeaf` / `hashNodes`, two reconstructions yielding the same root
    must have come from identical `(value, salt, copath)` triples. -/
private theorem simple_binding_core
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
  have h_rec : mc.reconstructRoot i v₀ s₀ d₀ = mc.reconstructRoot i v₁ s₁ d₁ := by
    rw [h₀, h₁]
  unfold reconstructRoot at h_rec
  obtain ⟨h_leaf_eq, h_d_eq⟩ :=
    walkCopath_inj_local mc h_inj_nodes d₀ d₁
      (MerkleShape.numLeaves mc.shape - 1 + i)
      (MerkleHasher.hashLeaf mc.hasher v₀ s₀)
      (MerkleHasher.hashLeaf mc.hasher v₁ s₁)
      h_len h_rec
  obtain ⟨hv, hs⟩ := h_inj_leaf h_leaf_eq
  exact ⟨hv, hs, h_d_eq⟩

/-- Bridge: for a singleton opening, `check = true` reduces to the
    per-triple equality `reconstructRoot ... = root`. -/
private theorem check_singleton_iff_local
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
  simp [Id.run, List.zip]
  by_cases h : mc.reconstructRoot i v s d = root
  · simp [h]; rfl
  · simp [h]

-- ---------------------------------------------------------------------------
-- §12.4 — main binding theorems
-- ---------------------------------------------------------------------------

/-- §12.4 mt-binding (Option B / contrapositive form). Single-leaf
    version: under collision-free `hashLeaf` and `hashNodes`, two
    accepted single-leaf openings of the same Merkle root at the same
    index must coincide as `Opening`/`OpeningProof` records.

    The length-of-copath premise (`h_len_d`) reflects the fact that the
    two opening proofs must agree on tree depth. In the §20 path-pruned
    formulation this is automatic; here in the L1 plain-copath layout
    it is a structural hypothesis on the input proofs. -/
theorem mt_binding
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (root : MerkleHasher.Digest H) (i : Nat)
    (op₀ op₁ : Opening H) (pf₀ pf₁ : OpeningProof H)
    (h₀ : mc.check root op₀ pf₀ = true)
    (h₁ : mc.check root op₁ pf₁ = true)
    (h_idx₀ : op₀.indices = [i]) (h_idx₁ : op₁.indices = [i])
    (h_len_d : ∀ (s₀ s₁ : MerkleHasher.Salt H)
        (d₀ d₁ : List (MerkleHasher.Digest H)),
        pf₀.entries = [(s₀, d₀)] → pf₁.entries = [(s₁, d₁)] →
        d₀.length = d₁.length) :
    op₀ = op₁ ∧ pf₀ = pf₁ := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  -- Both `check = true` force length agreement: the singleton
  -- `indices` list propagates to `values` and `entries`.
  have h₀' := h₀
  have h₁' := h₁
  have h_iv₀ : op₀.indices.length = op₀.values.length := by
    by_contra hne
    unfold check at h₀'
    simp [Id.run, pure, hne] at h₀'
  have h_ie₀ : op₀.indices.length = pf₀.entries.length := by
    by_contra hne
    have hne' : op₀.values.length ≠ pf₀.entries.length := by
      intro h; exact hne (h_iv₀.trans h)
    unfold check at h₀'
    simp [Id.run, pure, h_iv₀, hne'] at h₀'
  have h_iv₁ : op₁.indices.length = op₁.values.length := by
    by_contra hne
    unfold check at h₁'
    simp [Id.run, pure, hne] at h₁'
  have h_ie₁ : op₁.indices.length = pf₁.entries.length := by
    by_contra hne
    have hne' : op₁.values.length ≠ pf₁.entries.length := by
      intro h; exact hne (h_iv₁.trans h)
    unfold check at h₁'
    simp [Id.run, pure, h_iv₁, hne'] at h₁'
  have hlen_idx₀ : op₀.indices.length = 1 := by rw [h_idx₀]; simp
  have hlen_idx₁ : op₁.indices.length = 1 := by rw [h_idx₁]; simp
  have hlen_v₀ : op₀.values.length = 1 := by rw [← h_iv₀]; exact hlen_idx₀
  have hlen_v₁ : op₁.values.length = 1 := by rw [← h_iv₁]; exact hlen_idx₁
  have hlen_e₀ : pf₀.entries.length = 1 := by rw [← h_ie₀]; exact hlen_idx₀
  have hlen_e₁ : pf₁.entries.length = 1 := by rw [← h_ie₁]; exact hlen_idx₁
  -- Destructure the singleton lists.
  obtain ⟨v₀, hv₀⟩ : ∃ v, op₀.values = [v] :=
    List.length_eq_one_iff.mp hlen_v₀
  obtain ⟨v₁, hv₁⟩ : ∃ v, op₁.values = [v] :=
    List.length_eq_one_iff.mp hlen_v₁
  obtain ⟨e₀, he₀⟩ : ∃ e, pf₀.entries = [e] :=
    List.length_eq_one_iff.mp hlen_e₀
  obtain ⟨e₁, he₁⟩ : ∃ e, pf₁.entries = [e] :=
    List.length_eq_one_iff.mp hlen_e₁
  obtain ⟨s₀, d₀⟩ := e₀
  obtain ⟨s₁, d₁⟩ := e₁
  -- Repackage the `check`s into the singleton form expected by the helper.
  have h_check₀ :
      mc.check root
        ({ indices := [i], values := [v₀] } : Opening H)
        ({ entries := [(s₀, d₀)] } : OpeningProof H) = true := by
    have hop : op₀ = { indices := [i], values := [v₀] } := by
      cases op₀ with
      | mk idx vals =>
        simp only at h_idx₀ hv₀
        subst h_idx₀; subst hv₀; rfl
    have hpf : pf₀ = { entries := [(s₀, d₀)] } := by
      cases pf₀ with
      | mk es =>
        simp only at he₀
        subst he₀; rfl
    rw [hop, hpf] at h₀; exact h₀
  have h_check₁ :
      mc.check root
        ({ indices := [i], values := [v₁] } : Opening H)
        ({ entries := [(s₁, d₁)] } : OpeningProof H) = true := by
    have hop : op₁ = { indices := [i], values := [v₁] } := by
      cases op₁ with
      | mk idx vals =>
        simp only at h_idx₁ hv₁
        subst h_idx₁; subst hv₁; rfl
    have hpf : pf₁ = { entries := [(s₁, d₁)] } := by
      cases pf₁ with
      | mk es =>
        simp only at he₁
        subst he₁; rfl
    rw [hop, hpf] at h₁; exact h₁
  -- Length condition for the helper.
  have h_len : d₀.length = d₁.length := h_len_d s₀ s₁ d₀ d₁ he₀ he₁
  -- Apply the §12.3 single-leaf binding lemma (local copy).
  have hr₀ : mc.reconstructRoot i v₀ s₀ d₀ = root :=
    (check_singleton_iff_local mc root i v₀ s₀ d₀).mp h_check₀
  have hr₁ : mc.reconstructRoot i v₁ s₁ d₁ = root :=
    (check_singleton_iff_local mc root i v₁ s₁ d₁).mp h_check₁
  obtain ⟨hv_eq, hs_eq, hd_eq⟩ :=
    simple_binding_core mc h_inj_leaf h_inj_nodes root i
      v₀ v₁ s₀ s₁ d₀ d₁ h_len hr₀ hr₁
  -- Reassemble the original records.
  refine ⟨?_, ?_⟩
  · cases op₀ with
    | mk idx₀ vals₀ =>
      cases op₁ with
      | mk idx₁ vals₁ =>
        simp only at h_idx₀ h_idx₁ hv₀ hv₁
        subst h_idx₀; subst h_idx₁; subst hv₀; subst hv₁
        simp [hv_eq]
  · cases pf₀ with
    | mk es₀ =>
      cases pf₁ with
      | mk es₁ =>
        simp only at he₀ he₁
        subst he₀; subst he₁
        simp [hs_eq, hd_eq]

/-- §12.4 mt-other-binding (Option B / contrapositive form). For two
    accepted single-leaf openings of the same root at the same index
    that already agree on their *value*, the salt and copath digests
    must also coincide. This is the form the book uses to argue that
    the *opening proof* itself is uniquely determined by `(root, i, v)`
    under collision-free hashes. -/
theorem mt_other_binding
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S)
    (h_inj_leaf  : Function.Injective2 (MerkleHasher.hashLeaf  mc.hasher))
    (h_inj_nodes : Function.Injective  (MerkleHasher.hashNodes mc.hasher))
    (root : MerkleHasher.Digest H) (i : Nat)
    (v : MerkleHasher.Symbol H)
    (s₀ s₁ : MerkleHasher.Salt H)
    (d₀ d₁ : List (MerkleHasher.Digest H))
    (h_len : d₀.length = d₁.length)
    (h_check₀ :
      mc.check root
        ({ indices := [i], values := [v] } : Opening H)
        ({ entries := [(s₀, d₀)] } : OpeningProof H) = true)
    (h_check₁ :
      mc.check root
        ({ indices := [i], values := [v] } : Opening H)
        ({ entries := [(s₁, d₁)] } : OpeningProof H) = true) :
    s₀ = s₁ ∧ d₀ = d₁ := by
  have hr₀ : mc.reconstructRoot i v s₀ d₀ = root :=
    (check_singleton_iff_local mc root i v s₀ d₀).mp h_check₀
  have hr₁ : mc.reconstructRoot i v s₁ d₁ = root :=
    (check_singleton_iff_local mc root i v s₁ d₁).mp h_check₁
  obtain ⟨_, hs, hd⟩ :=
    simple_binding_core mc h_inj_leaf h_inj_nodes root i
      v v s₀ s₁ d₀ d₁ h_len hr₀ hr₁
  exact ⟨hs, hd⟩

end MerkleCommitment
