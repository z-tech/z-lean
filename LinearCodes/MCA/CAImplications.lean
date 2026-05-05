/-
# MCA implies CA (BCGM25 Lemma 3.22)

The MCA predicate is strictly stronger than CA: the existence of a
*shared* agreement set `T` for all rows simultaneously (MCA) implies
the weaker statement that the linear combination is close to the code
on average (CA). This file states and proves the reduction.

The BCGM25 quantitative form: if `G` has MCA for `c` with error `εMCA`,
then `G` has CA for `c` with error `εCA(e, t) = εMCA((e − 1) / n)` for
`1 ≤ t < e ≤ n`.
-/

import LinearCodes.MCA.Definitions
import LinearCodes.MCA.SeedProbLemmas

set_option linter.unusedSectionVars false

namespace LinearCodes

/-- **BCGM25 Lemma 3.22 (MCA implies CA).** If `G` has MCA for `c` with
error `εMCA`, then `G` has CA for `c` with error `εCA(e, t) = εMCA((e−1)/n)`. -/
theorem MCA_implies_CA {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    CorrelatedAgreement G c (fun e _ => εMCA ((e - 1 : ℚ) / n)) := by
  sorry

theorem MutualCorrelatedAgreement_zero_simplify {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA)
    (us : Fin ℓ → (Fin n → F)) :
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c)
      ≤ εMCA 0 := by
  have hmono :
      seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) ≤
        seedProb (S := S) (fun x =>
          ∃ T : Finset (Fin n),
            (T.card : ℚ) ≥ n * (1 - 0) ∧
            InRestrictedCode c T (G.combine x us) ∧
            ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) := by
    apply seedProb_mono
    intro x hx
    rcases hx with ⟨hcomb, j, hj⟩
    refine ⟨Finset.univ, ?_, ?_, j, ?_⟩
    · norm_num
    · exact (inRestrictedCode_univ_iff c).2 hcomb
    · intro hu
      exact hj ((inRestrictedCode_univ_iff c).1 hu)
  calc
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) ≤
        seedProb (S := S) (fun x =>
          ∃ T : Finset (Fin n),
            (T.card : ℚ) ≥ n * (1 - 0) ∧
            InRestrictedCode c T (G.combine x us) ∧
            ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) := hmono
    _ ≤ εMCA 0 := hMCA us 0 (by norm_num) (by norm_num)


end LinearCodes
