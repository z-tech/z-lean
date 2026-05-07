import Mathlib.Data.ZMod.Basic

import Sumcheck.Src.EvalForm
import Sumcheck.Src.Verifier
import Sumcheck.Src.Convention

/-!
# Eval-form sumcheck oracle: `#eval` test cases

This file is the *correctness oracle* for `effsc` (the external Rust prover
that produces sumcheck round messages in evaluation form). The reference
values pinned here are produced by Lean's kernel from the formally-defined
Phase 1 honest prover (`honestProverMessageEvalsAt` in
`Sumcheck/Src/EvalForm.lean`) and can be cross-checked against `effsc`'s
output for the same polynomial / domain / round / challenge prefix.

## Convention recap (matches `Sumcheck/Src/EvalForm.lean`)

For round `i : Fin n` with prior challenges `challenges : Fin i.val → 𝔽`,
the eval-form prover's round polynomial is the univariate
`G_i(c) := Σ_{x ∈ domain^(n-i-1)} p(challenges, c, x)`,
i.e. fix variables `0..i-1` to the verifier's prior challenges, fix
variable `i` to `c`, and sum `p` over the residual variables `i+1..n-1`
ranging over `domain`. We pin `G_i(c)` for several small `c`. With
`d := indDegreeK p ⟨i,_⟩` evaluation points (degrees 0..d) one can
Lagrange-interpolate `G_i` and run the sumcheck verifier on it.

## How to use these as golden tests for `effsc`

1. Translate the polynomial below into `effsc`'s polynomial representation
   (variable indexing, monomial format).
2. Run `effsc`'s round-`i` prover with the same `challenges` and the same
   `domain` (here `[0,1]`, but extend to any list).
3. Evaluate the round polynomial it returns at `c ∈ {0, 1, 2}` and compare
   against the constants pinned here. A mismatch is a bug in `effsc`.

## Adding new examples

Pattern per polynomial:
* declare `pN : CPoly.CMvPolynomial N (ZMod p)` via the standard
  `CPoly.Lawful.fromUnlawful` builder (cf. `ProtocolTests.lean`),
* define `claimN := honestClaim domain pN` (kernel-checked),
* compute `roundN_0_at_c := honestProverMessageEvalsAt domain pN ⟨0,_⟩
  Fin.elim0 c` for a few small `c`,
* hand-compute the expected values (or `#eval` to discover them, then
  cross-check with another tool) and pin them with `native_decide`.

Field choice: `ZMod 17` here for fast `decide`/`native_decide` and
hand-verifiability. `effsc`'s production target is the Goldilocks prime
`p = 2^64 - 2^32 + 1` (see `CompPoly/Fields/Goldilocks.lean`); the same
test pattern works there once the prime fact instance is provided.
-/

namespace __EvalFormTests__

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev 𝔽 := ZMod 17

/-- Standard Boolean hypercube domain. -/
def domain : List 𝔽 := [0, 1]

/-! ## Example 1: n = 1, multilinear `p(x) = 1 + 2·x`

Hand computation:
* p(0) = 1, p(1) = 3, p(2) = 5
* honest claim = p(0) + p(1) = 4
* Round 0: i = 0, numOpenVars = 0, so the "sum" is over the empty
  hypercube — the round message just evaluates p at the single point [c]:
  G_0(c) = 1 + 2c.
-/

namespace Example1

/-- p(x) = 1 + 2·x over ZMod 17. Monomial `x^0` with coeff 1, `x^1` with coeff 2. -/
def p : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 1 𝔽).insert ⟨#[0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1], by decide⟩ (2 : 𝔽)

#eval honestClaim domain p                                                    -- 4
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)   -- 1
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)   -- 3
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽)   -- 5

/-- The honest claim is p(0) + p(1) = 4 mod 17. -/
example : honestClaim (n := 1) domain p = (4 : 𝔽) := by native_decide

/-- Round-0 evaluation at c = 0: G_0(0) = 1. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) = (1 : 𝔽) := by
  native_decide

/-- Round-0 evaluation at c = 1: G_0(1) = 3. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) = (3 : 𝔽) := by
  native_decide

/-- Round-0 evaluation at c = 2: G_0(2) = 5. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽) = (5 : 𝔽) := by
  native_decide

/-- Sumcheck consistency at round 0: G_0(0) + G_0(1) = honest claim. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      + honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
        = honestClaim (n := 1) domain p := by
  native_decide

end Example1

/-! ## Example 2: n = 2, multilinear `p(x,y) = 1 + x + y + x·y`

Hand computation:
* p(0,0) = 1, p(1,0) = 2, p(0,1) = 2, p(1,1) = 4
* honest claim = 1 + 2 + 2 + 4 = 9
* Round 0 (i = 0, numOpenVars = 1): G_0(c) = Σ_{y ∈ {0,1}} p(c, y)
                                          = (1 + c) + (2 + 2c)
                                          = 3 + 3c.
  Pinned: G_0(0) = 3, G_0(1) = 6, G_0(2) = 9.
* Round 1 with challenge r₀ (i = 1, numOpenVars = 0): G_1(c) = p(r₀, c)
                                                            = 1 + r₀ + c + r₀·c
                                                            = (1 + r₀) + (1 + r₀)·c.
  We pick r₀ = 5: G_1(c) = 6 + 6c. Pinned: G_1(0) = 6, G_1(1) = 12.
* Transcript consistency: G_1(0) + G_1(1) = 18 ≡ 1 mod 17,
  and G_0(5) = 3 + 3·5 = 18 ≡ 1 mod 17. So Σ_c G_1(c) = G_0(r₀). -/

namespace Example2

/-- p(x,y) = 1 + x + y + x·y. -/
def p : CPoly.CMvPolynomial 2 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 𝔽).insert ⟨#[0, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1, 0], by decide⟩ (1 : 𝔽)
      |>.insert ⟨#[0, 1], by decide⟩ (1 : 𝔽)
      |>.insert ⟨#[1, 1], by decide⟩ (1 : 𝔽)

#eval honestClaim domain p                                                              -- 9

-- Round 0 evaluations (no prior challenges).
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)             -- 3
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)             -- 6
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽)             -- 9

example : honestClaim (n := 2) domain p = (9 : 𝔽) := by native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) = (3 : 𝔽) := by
  native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) = (6 : 𝔽) := by
  native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽) = (9 : 𝔽) := by
  native_decide

/-- Round-0 sumcheck consistency: G_0(0) + G_0(1) = honest claim = 9. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      + honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
        = honestClaim (n := 2) domain p := by
  native_decide

/-! ### Round 1 transcript with challenge r₀ = 5

After absorbing r₀ = 5, the round-1 message is `G_1(c) = 6 + 6c`. The
transcript-consistency check on the verifier side is `Σ_c G_1(c) = G_0(r₀)`,
where `G_0(r₀)` is computed via Lagrange interpolation of round 0's two
evaluation points `(0, 3), (1, 6)`. Since `G_0` is degree 1 (multilinear in
x_0), the interpolant is exactly `3 + (6 - 3)·r₀ = 3 + 3·r₀`. At r₀ = 5
this is 18 ≡ 1 mod 17, and `G_1(0) + G_1(1) = 6 + 12 = 18 ≡ 1 mod 17`. -/

def r0 : 𝔽 := 5
def challenges1 : Fin 1 → 𝔽 := ![r0]

#eval honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (0 : 𝔽)           -- 6
#eval honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (1 : 𝔽)           -- 12

example :
    honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (0 : 𝔽) = (6 : 𝔽) := by
  native_decide

example :
    honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (1 : 𝔽) = (12 : 𝔽) := by
  native_decide

/-- Manual Lagrange interpolation of round 0 at r₀: degree-1 interpolant
through `(0, G_0(0))` and `(1, G_0(1))`. -/
def interpRound0AtR0 : 𝔽 :=
  let g00 := honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
  let g01 := honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
  g00 * (1 - r0) + g01 * r0

#eval interpRound0AtR0                                                                -- 1

/-- Transcript consistency between round 0 and round 1:
`Σ_c G_1(c) = G_0(r₀)` (the verifier's check between rounds). -/
example :
    honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (0 : 𝔽)
      + honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (1 : 𝔽)
        = interpRound0AtR0 := by
  native_decide

end Example2

/-! ## Example 3: n = 3, non-multilinear `p(x,y,z) = x²·y + z`

Hand computation:
* p(0,0,0) = 0, p(0,0,1) = 1, p(0,1,0) = 0, p(0,1,1) = 1,
  p(1,0,0) = 0, p(1,0,1) = 1, p(1,1,0) = 1, p(1,1,1) = 2
* honest claim = 0+1+0+1+0+1+1+2 = 6
* Round 0 (i = 0, numOpenVars = 2): G_0(c) = Σ_{(y,z) ∈ {0,1}²} (c²·y + z)
                                          = c²·(0+0+1+1) + (0+1+0+1)
                                          = 2c² + 2.
  Pinned: G_0(0) = 2, G_0(1) = 4, G_0(2) = 10. (Note degree 2 in x_0.)
* Sumcheck consistency: G_0(0) + G_0(1) = 2 + 4 = 6 = claim. -/

namespace Example3

/-- p(x,y,z) = x²·y + z. -/
def p : CPoly.CMvPolynomial 3 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 3 𝔽).insert ⟨#[2, 1, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[0, 0, 1], by decide⟩ (1 : 𝔽)

#eval honestClaim domain p                                                             -- 6

-- Round 0 evaluations.
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)            -- 2
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)            -- 4
#eval honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽)            -- 10

example : honestClaim (n := 3) domain p = (6 : 𝔽) := by native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) = (2 : 𝔽) := by
  native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) = (4 : 𝔽) := by
  native_decide

example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (2 : 𝔽) = (10 : 𝔽) := by
  native_decide

/-- Round-0 sumcheck consistency: G_0(0) + G_0(1) = honest claim = 6. -/
example :
    honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      + honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
        = honestClaim (n := 3) domain p := by
  native_decide

/-- The independent degree of x_0 in p is 2; this means the verifier needs
3 evaluations (at c = 0, 1, 2) to interpolate G_0 — the values pinned
above. -/
example : indDegreeK p ⟨0, by decide⟩ = 2 := by native_decide

end Example3

/-! ## Example 4 — MSB vs LSB convention on an asymmetric multilinear

Lean's spec convention is LSB (round-`i` binds `Fin n` position `i`); `effsc`'s
multilinear prover is MSB (round-`0` splits the table into halves of high-bit
0 vs 1). For symmetric polynomials the two conventions produce the same
round messages, so testing the convention layer needs an *asymmetric* poly.

Here `p(x₀, x₁) = 1 + 2·x₀ + 3·x₁ + 5·x₀·x₁`.
* LSB round 0 binds `x₀`. The round message is
  `G_0^LSB(c) = Σ_y p(c, y) = (1 + 2c) + (1 + 2c + 3 + 5c) = 5 + 9c`.
* MSB round 0 binds `x₁`. The round message is
  `G_0^MSB(c) = Σ_x p(x, c) = (1 + 3c) + (1 + 2 + 3c + 5c) = 4 + 11c`.

These differ at c=1 (LSB: 14; MSB: 15), confirming the convention parameter
actually changes the prover's output and is not vacuous. The
`honestProverMessageEvalsAtConv_MSB_eq_LSB_rename` theorem says MSB on `p`
is LSB on `rename reverseFin p`; this file pins the corresponding `#eval`
values so any regression in the convention plumbing breaks here. -/

namespace Example4

open Sumcheck

/-- p(x₀, x₁) = 1 + 2x₀ + 3x₁ + 5x₀x₁. -/
def p : CPoly.CMvPolynomial 2 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 𝔽).insert ⟨#[0, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1, 0], by decide⟩ (2 : 𝔽)
      |>.insert ⟨#[0, 1], by decide⟩ (3 : 𝔽)
      |>.insert ⟨#[1, 1], by decide⟩ (5 : 𝔽)

#eval honestClaim domain p                                                              -- 2 (= 19 mod 17)

-- LSB round-0 evaluations: G_0^LSB(c) = 5 + 9c.
#eval honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)  -- 5
#eval honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)  -- 14
-- MSB round-0 evaluations: G_0^MSB(c) = 4 + 11c.
#eval honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)  -- 4
#eval honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)  -- 15

example :
    honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      = (5 : 𝔽) := by native_decide

example :
    honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
      = (14 : 𝔽) := by native_decide

example :
    honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      = (4 : 𝔽) := by native_decide

example :
    honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
      = (15 : 𝔽) := by native_decide

/-- The conventions disagree on this polynomial — confirms the convention
parameter is non-vacuous on asymmetric multilinears. -/
example :
    honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
      ≠ honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) := by
  native_decide

/-- Both conventions compute the same total claim (sum over the full hypercube
is permutation-invariant). `Σ_x p(x) = p(0,0) + p(1,0) + p(0,1) + p(1,1)
= 1 + 3 + 4 + 11 = 19 ≡ 2 mod 17`. -/
example : honestClaim (n := 2) domain p = (2 : 𝔽) := by native_decide

/-- Both conventions satisfy the round-0 sumcheck identity
`G_0(0) + G_0(1) = honestClaim`. -/
example :
    honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      + honestProverMessageEvalsAtConv Convention.LSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
        = honestClaim (n := 2) domain p := by native_decide

example :
    honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽)
      + honestProverMessageEvalsAtConv Convention.MSB domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽)
        = honestClaim (n := 2) domain p := by native_decide

end Example4

end __EvalFormTests__
