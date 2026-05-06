/-
# BCGM25 §9 cross-cutting predicates

Cross-cutting predicates connecting concrete generators used by modern
IOP-based SNARKs (STIR, WHIR-univariate, WARP) to the abstract MCA /
CA framework defined in `LinearCodes.MCA.Definitions`. These predicates
let downstream consumers state hypotheses against a single named
"profile" rather than re-deriving the structural facts each time.

Key contents:
* `IsSTIRGenerator G` — predicate asserting that `G` equals
  `Generator.univariatePowers F d` for some `d`, exposing the
  univariate-powers structure to the consumer.
* `univariatePowers_isSTIR` — sanity check: the canonical STIR generator
  satisfies the predicate.

Depends on `LinearCodes.MCA.Applications.STIR`. Future profiles
(WHIR-univariate, WARP) will be added here as their applications are
formalized.
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
