/-
# Counting sub-targets for Case 2 (BCGM25 Theorem 6.1)

The generic probabilistic / combinatorial primitives consumed by the
Case 2 proof of `MCA_unique_decoding_large_gamma_bound`:

* Sub-target A — probability → counting (`ncard_lt_of_seedProb_gt`).
* Sub-target B — distinct seeds in a finset (`exists_distinct_seeds_in_finset`).

These do not depend on MDS structure or column-difference machinery and
are also reused by the list-decoding Phase B proofs.

(Formerly the opening sections of `LinearCodes/MCA/Case2Subtargets.lean`,
extracted as part of the P2 file-split refactor.)
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.MaximalDomain

-- The file-level variables (`{F} [Field F]` etc.) are used by most
-- theorems but legitimately unused in some. Leaving the section-var
-- linter suppressed for this file.
set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-! ### Sub-target A: probability → counting -/

/-- Contrapositive of `seedProb_le_ncard_div`. -/
theorem ncard_lt_of_seedProb_gt
    {S : Type*} [Fintype S] [Nonempty S]
    (P : S → Prop) (N : ℕ)
    (h : ((N : ℚ) / Fintype.card S) < seedProb P) :
    N < {x : S | P x}.ncard := by
  by_contra hN
  push_neg at hN
  have h_le := seedProb_le_ncard_div P N hN
  linarith

/-! ### Sub-target B: distinct seeds in a finset -/

/-- Extract injective `Fin ℓ → S` mapping into a finset of size ≥ ℓ. -/
theorem exists_distinct_seeds_in_finset
    {S : Type*} {ℓ : ℕ} [DecidableEq S]
    (B : Finset S) (hB : ℓ ≤ B.card) :
    ∃ xs : Fin ℓ → S, Function.Injective xs ∧ ∀ i, xs i ∈ B := by
  obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq hB
  let e : Fin ℓ ≃ B' := (Finset.equivFinOfCardEq hB'_card).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hB'_sub (e i).property

end LinearCodes
