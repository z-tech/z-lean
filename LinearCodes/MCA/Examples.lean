/-
# Concrete generator examples

The standard generators studied in BCGM25 §2.3:

* `Generator.identity` — `G(x) = x`. Used in [RVW13].
* `Generator.univariatePowers` — `G(x) = (1, x, x², …, x^d)`. Used in
  the FRI-family proximity tests.
* `Generator.affineLine` — `G(x) = (1, x)`. The simplest non-trivial
  generator.

We define these and prove their basic identities. Quantitative
zero-evading bounds (e.g. for `univariatePowers`, `ε_ZE = d/|S|` over
sufficiently large fields) are deferred — those require polynomial
identity-lemma machinery that we'll build alongside §6.
-/

import LinearCodes.MCA.Definitions

set_option linter.unusedSectionVars false

namespace LinearCodes
namespace Generator

/-- The identity generator: `G(x) = x` for `x ∈ F^ℓ`. -/
def identity (F : Type*) [Field F] (ℓ : ℕ) : Generator F (Fin ℓ → F) ℓ :=
  ⟨fun x => x⟩

/-- The univariate-powers generator: `G(x) = (1, x, x², …, x^d)`. -/
def univariatePowers (F : Type*) [Field F] (d : ℕ) : Generator F F (d + 1) :=
  ⟨fun x i => x ^ i.val⟩

/-! ### Basic identities -/

/-- The identity generator's output equals its input. -/
theorem identity_apply (F : Type*) [Field F] {ℓ : ℕ} (x : Fin ℓ → F) (i : Fin ℓ) :
    (identity F ℓ) x i = x i := rfl

/-- The univariate-powers generator's `i`-th output is the `i`-th power. -/
theorem univariatePowers_apply (F : Type*) [Field F] {d : ℕ} (x : F) (i : Fin (d + 1)) :
    (univariatePowers F d) x i = x ^ i.val := rfl

/-- The first coordinate of `univariatePowers` is always `1`. -/
theorem univariatePowers_zero (F : Type*) [Field F] {d : ℕ} (x : F) :
    (univariatePowers F d) x ⟨0, Nat.succ_pos d⟩ = 1 := by
  simp [univariatePowers]

end Generator
end LinearCodes
