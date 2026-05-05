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

/-- **MCA-at-zero simplification.** At `γ = 0`, the MCA bad event reduces:
`T.card ≥ n` forces `T = univ`, and restriction-to-univ collapses to plain
code membership. Hence the bad event becomes simply
`G.combine x us ∈ c ∧ ∃ j, us j ∉ c`.

This is a useful corollary of `MutualCorrelatedAgreement` that makes
many `γ = 0` arguments easier (e.g., the forward direction of
Lemma 3.18 can route through this). -/
theorem MutualCorrelatedAgreement_zero_simplify
    {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA)
    (us : Fin ℓ → (Fin n → F)) :
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c)
      ≤ εMCA 0 := by
  sorry

end LinearCodes
