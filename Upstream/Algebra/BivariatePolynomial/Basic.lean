/-
# Bivariate polynomial machinery (skeleton)

Definitions and theorem signatures for future Guruswami-Sudan list-decoding
work. None of these are proved yet — they exist as a target for future
infrastructure work.

This file is intentionally a stub: it stages a small API surface
(`Bivariate`, `weightedDegree`, `multiplicityAt`, and the GS interpolation
existence statement) so that downstream developments — in particular
tightening the Johnson MDS bound (J6) and pushing list-decoding capacity
beyond the trivial bounds currently available in `LinearCodes/` — can be
written against stable names while the underlying proofs are filled in.

All `sorry`s in this file are deliberate placeholders for future work.
-/

import Mathlib.Algebra.Polynomial.Basic

namespace BivariatePoly

/-- A bivariate polynomial `Q(X, Y)`. For now, just an alias of
`Polynomial (Polynomial F)`: the outer indeterminate plays the role of `Y`
and coefficients are univariate polynomials in `X`. -/
abbrev Bivariate (F : Type*) [Field F] := Polynomial (Polynomial F)

/-- Weighted `(a, b)`-degree of a bivariate polynomial: the maximum over
monomials `X^i Y^j` (with nonzero coefficient) of `a * i + b * j`.

In Guruswami-Sudan we instantiate this with `(a, b) = (1, k - 1)` where
`k` is the dimension of the underlying Reed–Solomon code. -/
def weightedDegree {F : Type*} [Field F] (a b : ℕ) (q : Bivariate F) : ℕ := sorry

/-- Multiplicity of a bivariate polynomial `q` at a point `(x, y) ∈ F × F`:
the largest `m` such that `(X - x)^i (Y - y)^j ∣ q` whenever `i + j < m`.

(Equivalently, the order of vanishing of the shifted polynomial
`q(X + x, Y + y)` at the origin.) -/
def multiplicityAt {F : Type*} [Field F] (q : Bivariate F) (x y : F) : ℕ := sorry

/-- **Guruswami-Sudan interpolation (existence).**

There exists a nonzero bivariate polynomial of weighted `(1, k - 1)`-degree
at most `⌊√(n (k - 1))⌋ + r`, vanishing with multiplicity at least `r` at
each of `n` given points.

Statement only — the proof is a linear-algebra dimension-counting argument:
the space of bivariate polynomials of bounded weighted degree has dimension
exceeding the number of multiplicity constraints, so a nonzero solution
exists. -/
theorem gs_interpolation_exists {F : Type*} [Field F] {n k : ℕ}
    (points : Fin n → F × F) (r : ℕ) :
    ∃ q : Bivariate F, q ≠ 0 ∧
      weightedDegree 1 (k - 1) q ≤ Nat.sqrt (n * (k - 1)) + r ∧
      ∀ i, multiplicityAt q (points i).1 (points i).2 ≥ r := sorry

end BivariatePoly
