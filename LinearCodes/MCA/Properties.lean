/-
# Properties of MCA, CA, and zero-evading

Structural properties of the §3 BCGM25 predicates:

* Trivial-error cases (`ε = 1`): every generator vacuously satisfies the
  predicate, since seed-probability is bounded by 1.
* Unfold-form lemmas for definitional rewriting.

These trivial-bound lemmas are useful as base cases in inductive
arguments and as sanity checks on the definitions.
-/

import LinearCodes.MCA.Definitions
import LinearCodes.MCA.SeedProbLemmas


namespace LinearCodes

/-! ### Trivial-error cases -/

/-- Every generator is zero-evading with error one. -/
theorem ZeroEvading_one {F : Type*} [Field F] {S : Type*} [Fintype S] [Nonempty S]
    {ℓ : ℕ} (G : Generator F S ℓ) :
    ZeroEvading G 1 := by
  intro v _
  exact seedProb_le_one _

/-- Every generator has MCA with the constant-one error function. -/
theorem MutualCorrelatedAgreement_one {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] [Nonempty S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F)) :
    MutualCorrelatedAgreement G c (fun _ => 1) := by
  intro us γ _ _
  exact seedProb_le_one _

/-- Every generator has CA with the constant-one error function. -/
theorem CorrelatedAgreement_one {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] [Nonempty S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F)) :
    CorrelatedAgreement G c (fun _ _ => 1) := by
  intro e t _ _ _ us _
  exact seedProb_le_one _

/-! ### Unfold lemmas -/

/-- Unfold-form for `ZeroEvading`. -/
theorem ZeroEvading_iff {F : Type*} [Field F] {S : Type*} [Fintype S] {ℓ : ℕ}
    (G : Generator F S ℓ) (ε : ℚ) :
    ZeroEvading G ε ↔ ∀ v : Fin ℓ → F, v ≠ 0 →
      seedProb (S := S) (fun x => ∑ j, G x j * v j = 0) ≤ ε := Iff.rfl

/-! ### Bound-relaxation lemmas -/

/-- Relaxing the zero-evading error bound preserves the property. -/
theorem ZeroEvading.mono {F : Type*} [Field F] {S : Type*} [Fintype S] {ℓ : ℕ}
    {G : Generator F S ℓ} {ε ε' : ℚ} (h : ε ≤ ε') (hZE : ZeroEvading G ε) :
    ZeroEvading G ε' := by
  intro v hv
  exact (hZE v hv).trans h

/-- Relaxing the MCA error bound (pointwise) preserves the property. -/
theorem MutualCorrelatedAgreement.mono {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    {εMCA εMCA' : ℚ → ℚ} (h : ∀ γ, εMCA γ ≤ εMCA' γ)
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    MutualCorrelatedAgreement G c εMCA' := by
  intro us γ hγ0 hγ1
  exact (hMCA us γ hγ0 hγ1).trans (h γ)

/-- Relaxing the CA error bound (pointwise) preserves the property. -/
theorem CorrelatedAgreement.mono {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    {εCA εCA' : ℕ → ℕ → ℚ} (h : ∀ e t, εCA e t ≤ εCA' e t)
    (hCA : CorrelatedAgreement G c εCA) :
    CorrelatedAgreement G c εCA' := by
  intro e t ht1 ht2 he us hus
  exact (hCA e t ht1 ht2 he us hus).trans (h e t)

/-! ### BCGM25 Lemma 3.18 (forward direction)

The relationship `ε_MCA(0) ≥ ε_ZE`: if `G` has MCA for a *proper* subcode `c ⊊ ⊤`
with error `εMCA`, then `G` is zero-evading with error `εMCA 0`.

**Proof sketch (BCGM25 page 19):**

Let `v ∈ F^ℓ` be nonzero. We want to bound the probability that
`∑ⱼ G(x)ⱼ · vⱼ = 0`.

* Pick a witness `u ∈ Fⁿ` with `u ∉ c` (exists because `c < ⊤`).
* Pick `j₀` with `v j₀ ≠ 0` (exists because `v ≠ 0`).
* Set `Uⱼ := vⱼ • u`. Then by `Generator.combine_smul_const`:
  `G.combine x U = (∑ⱼ G(x)ⱼ · vⱼ) • u`.
* If the seed `x` satisfies `∑ⱼ G(x)ⱼ · vⱼ = 0`, then `G.combine x U = 0 ∈ c`.
  At `γ = 0`, the agreement set `T` must be all of `[n]`, and:
  - `(G.combine x U)|T ∈ c|T` reduces to `G.combine x U ∈ c` via
    `inRestrictedCode_univ_iff` — holds.
  - `U_{j₀}|T = U_{j₀}` and `U_{j₀} = v_{j₀} • u`.
    If this lay in `c`, scaling by `(v j₀)⁻¹` (using `v j₀ ≠ 0`) would give
    `u ∈ c`, contradicting our choice of `u`.
* So the bad event of MCA at `γ = 0` is implied by `G(x) · v = 0`. By
  `seedProb_mono` and `hMCA U 0`, the conclusion follows.

**Mathlib lemmas likely needed:**
* `Submodule.eq_top_iff'` — `c = ⊤ ↔ ∀ x, x ∈ c`
* `Submodule.zero_mem`, `Submodule.smul_mem`
* `Finset.card_univ`, `Fintype.card_fin`
* `inv_mul_cancel₀`, `smul_smul`, `zero_smul`
-/

/-- Helper: scaling a non-zero submodule-non-member by a nonzero scalar
preserves non-membership. -/
theorem smul_not_mem_of_ne_zero_of_not_mem {F : Type*} [Field F] {n : ℕ} {c : Submodule F (Fin n → F)} {a : F} {u : Fin n → F} : a ≠ 0 → u ∉ c → a • u ∉ c := by
  intro ha hu hau
  apply hu
  have h := c.smul_mem a⁻¹ hau
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h

/-- See also `MutualCorrelatedAgreement_zero_simplify` in
`LinearCodes/MCA/CAImplications.lean` for a related simplification at `γ = 0`. -/
theorem MCA_implies_ZeroEvading_at_zero {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    (h_proper : c < ⊤)
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    ZeroEvading G (εMCA 0) := by
  intro v hv
  obtain ⟨u, hu_not⟩ : ∃ u : Fin n → F, u ∉ c := by
    by_contra h
    push_neg at h
    exact h_proper.ne (Submodule.eq_top_iff'.2 h)
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin ℓ, v j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  refine le_trans (seedProb_mono ?_) (hMCA (fun j => v j • u) 0 ?_ ?_)
  · intro x hx
    refine ⟨Finset.univ, ?_, ?_, ?_⟩
    · simpa only [Finset.card_univ, Fintype.card_fin, sub_zero, mul_one] using (show (n : ℚ) ≥ n by exact le_rfl)
    · rw [Generator.combine_smul_const G x v u, hx, zero_smul]
      exact inRestrictedCode_zero c Finset.univ
    · exact ⟨j₀, by
        rw [inRestrictedCode_univ_iff]
        exact smul_not_mem_of_ne_zero_of_not_mem hj₀ hu_not⟩
  · norm_num
  · norm_num


end LinearCodes
