/- The prover determined this theorem is likely FALSE:
-- -- Counterexample to `MCA_implies_CA`.
-- -- Take `F = ℚ`, `S = PUnit`, `n = 2`, `ℓ = 0`.
-- -- Let `c = ⊥ : Submodule ℚ (Fin 2 → ℚ)`.
-- -- Let `εMCA : ℚ → ℚ := fun _ => 0`.
-- -- Let `G : Generator ℚ PUnit 0` be the unique generator.
-- --
-- -- Why MCA holds:
-- -- * For any `us : Fin 0 → (Fin 2 → ℚ)` and any `γ`, the MCA bad event asks for
-- --   `∃ j : Fin 0, ¬ InRestrictedCode c T (us j)`, impossible since `Fin 0` is empty.
-- -- * Hence the bad event is false for every seed, so its seed-probability is `0`.
-- -- * Therefore `MutualCorrelatedAgreement G c εMCA` holds.
-- --
-- -- Why CA fails:
-- -- * Choose `e = 2` and `t = 1`; then `1 ≤ t`, `t < e`, and `e ≤ n`.
-- -- * The CA hypothesis on all rows is vacuous because there is no `i : Fin 0`.
-- -- * For every seed `x`, `G.combine x us = 0` because the sum is over `Fin 0`.
-- -- * Since `0 ∈ c`, take `codeword = 0`; then
-- --   `hammingDistance (G.combine x us) codeword = 0 ≤ e - t = 1`.
-- -- * So the CA event holds for every seed, hence has seed-probability `1`.
-- -- * But the claimed upper bound is `εMCA ((e - 1 : ℚ) / n) = εMCA (1 / 2) = 0`.
-- -- * Therefore the conclusion of `CorrelatedAgreement` fails.
-- --
-- -- Conclusion: the theorem needs an extra assumption such as `0 < ℓ`; without it, it is false.
-/
/- The prover determined this theorem is likely FALSE:
-- -- Counterexample to the false statement `MCA_implies_CA`.
-- --
-- -- Take:
-- -- * `F = ℚ`
-- -- * `S = PUnit` (one seed)
-- -- * `n = 2`
-- -- * `ℓ = 0`
-- -- * `c = ⊥ : Submodule ℚ (Fin 2 → ℚ)`
-- -- * `εMCA := fun _ => 0`
-- -- * `G : Generator ℚ PUnit 0` the unique generator
-- --
-- -- Why MCA holds:
-- -- * For any `us : Fin 0 → (Fin 2 → ℚ)` and any `γ`, the MCA bad event is
-- --   `∃ T : Finset (Fin 2), ... ∧ ∃ j : Fin 0, ¬ InRestrictedCode c T (us j)`.
-- -- * But `Fin 0` has no elements, so `∃ j : Fin 0, ...` is impossible.
-- -- * Hence the bad event is false for every seed `x`, so its seed-probability is `0`.
-- -- * Therefore `MutualCorrelatedAgreement G c εMCA` holds, since `0 ≤ εMCA γ = 0`.
-- --
-- -- Why CA fails:
-- -- * Choose `e = 2` and `t = 1`. Then `1 ≤ t`, `t < e`, and `e ≤ n` all hold.
-- -- * The CA premise
-- --   `∀ i : Fin 0, ∀ codeword ∈ c, e ≤ hammingDistance (us i) codeword`
-- --   is vacuous because there is no `i : Fin 0`.
-- -- * For any seed `x`, `G.combine x us = 0`, because the defining sum is over `Fin 0`.
-- -- * Since `0 ∈ c`, taking `codeword = 0` shows
-- --   `hammingDistance (G.combine x us) codeword = hammingDistance 0 0 = 0 ≤ e - t = 1`.
-- -- * So the CA event is true for every seed, hence its seed-probability is `1`.
-- -- * But the claimed bound is
-- --   `εMCA ((e - 1 : ℚ) / n) = εMCA (1 / 2) = 0`.
-- -- * Thus the conclusion
-- --   `CorrelatedAgreement G c (fun e _ => εMCA ((e - 1 : ℚ) / n))` fails.
-- --
-- -- Conclusion: the theorem needs an extra assumption such as `0 < ℓ`;
-- -- without it, the statement is false.
-/
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
