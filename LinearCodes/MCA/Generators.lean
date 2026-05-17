/-
# Concrete generators

The standard generators studied in BCGM25 §2.3 (formerly
`LinearCodes/MCA/Examples.lean`; this file defines load-bearing
library content, not examples):

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

/-- The affine-line generator: `G(x) = (1, x)`, used as the simplest
non-trivial polynomial generator in BCGM25. -/
def affineLine (F : Type*) [Field F] : Generator F F 2 :=
  ⟨fun x => ![1, x]⟩

/-- The affine-space generator: `G(x₁, …, xₛ) = (1, x₁, …, xₛ)`. The
basic generator for many proximity-test reductions. -/
def affineSpace (F : Type*) [Field F] (s : ℕ) :
    Generator F (Fin s → F) (s + 1) :=
  ⟨fun x => Fin.cons 1 x⟩

/-! ### Identities for `affineLine` and `affineSpace` -/

/-- The zeroth coordinate of `affineLine` is always `1`. -/
theorem affineLine_zero (F : Type*) [Field F] (x : F) :
    (affineLine F) x 0 = 1 := rfl

/-- The first coordinate of `affineLine` is the input. -/
theorem affineLine_one (F : Type*) [Field F] (x : F) :
    (affineLine F) x 1 = x := rfl

/-- The zeroth coordinate of `affineSpace` is always `1`. -/
theorem affineSpace_zero (F : Type*) [Field F] {s : ℕ} (x : Fin s → F) :
    (affineSpace F s) x 0 = 1 := rfl

/-- The `(i+1)`-th coordinate of `affineSpace` is the `i`-th input coordinate. -/
theorem affineSpace_succ (F : Type*) [Field F] {s : ℕ} (x : Fin s → F)
    (i : Fin s) :
    (affineSpace F s) x i.succ = x i := by
  simp [affineSpace, Fin.cons_succ]

end Generator
end LinearCodes
