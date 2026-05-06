/-
# BCGM25 §9 cross-cutting predicates

Predicates connecting concrete generators (STIR, WHIR-univariate, WARP) to
the abstract MCA framework.
-/

import LinearCodes.MCA.Applications.STIR

set_option linter.unusedSectionVars false

namespace LinearCodes

/-! ### C1: STIR generator predicate -/

/-- C1: A generator is "STIR-style" if it equals `univariatePowers F d` for some `d`. -/
def IsSTIRGenerator {F : Type*} [Field F] {ℓ : ℕ} (G : Generator F F ℓ) : Prop :=
  ∃ d : ℕ, ℓ = d + 1 ∧ HEq G (Generator.univariatePowers F d)

/-- Sanity: the canonical STIR generator satisfies the predicate. -/
theorem univariatePowers_isSTIR {F : Type*} [Field F] (d : ℕ) :
    IsSTIRGenerator (Generator.univariatePowers F d) :=
  ⟨d, rfl, HEq.rfl⟩

end LinearCodes
