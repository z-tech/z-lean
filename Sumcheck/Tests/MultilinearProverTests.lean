import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

import Sumcheck.Src.EvalForm
import Sumcheck.Src.MultilinearProver

set_option maxHeartbeats 800000

/-!
# Multilinear evaluation-table prover oracle: `#eval` test cases

This file is the *correctness oracle* for `effsc`'s multilinear sumcheck
prover (the eval-table state algorithm in
`Sumcheck/Src/MultilinearProver.lean`). The reference values pinned
here connect Phase 2's table-form prover to the Phase 1 symbolic
eval-form prover (`honestProverMessageEvalsAt` in
`Sumcheck/Src/EvalForm.lean`).

## Convention recap

Phase 2's `boolPoint_msb` maps table index `i : Fin (2^n)` to a
Boolean point whose variable `j` reads bit `n-1-j` of `i`. As a
consequence, when paired with `computeS0S1_msb` (low half / high
half of the table) and `fold_msb_succ` (in-place fold), the
table-form prover's `(s0, s1)` round message matches the **plain
LSB** symbolic prover at the round-`0`/`1` evaluation points
`(c = 0, c = 1)`. (No `Convention.MSB` in this file — that's a
separate sanity check pinned in `EvalFormTests.lean`.)

## How to use these as golden tests for `effsc`

For each polynomial `p` and challenge prefix `[r_0, ..., r_{i-1}]`:

1. Build the eval table: `t_0 := toEvalTable p`.
2. Fold once per challenge: `t_{i+1} := fold_msb_succ r_i t_i`.
3. The round-`i` message is `(s0_i, s1_i) := computeS0S1_msb t_i`.
4. Cross-check against
   `honestProverMessageEvalsAt domain p ⟨i, _⟩ challenges_i (0 or 1)`
   for `c ∈ {0, 1}`.

A mismatch is a bug in `effsc`'s Rust prover.

## Adding new examples

Pattern per polynomial:
* declare `pN : CPoly.CMvPolynomial N (ZMod 17)` via the standard
  `CPoly.Lawful.fromUnlawful` builder (cf. `EvalFormTests.lean`),
* compute `tN := toEvalTable pN` and `(s0, s1) := computeS0S1_msb tN`,
* `#eval` to discover the values, then pin with `native_decide`,
* cross-check `s0` and `s1` against
  `honestProverMessageEvalsAt domain pN ⟨0, _⟩ Fin.elim0 (0 / 1)`.

Field choice: `ZMod 17` for fast `decide`/`native_decide` and
hand-verifiability.
-/

namespace __MultilinearProverTests__

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev 𝔽 := ZMod 17

/-- Standard Boolean hypercube domain. -/
def domain : List 𝔽 := [0, 1]

open Sumcheck.MultilinearProver

/-! ## Example 1: n = 1, multilinear `p(x) = 1 + 2·x`

Hand computation:
* p(0) = 1, p(1) = 3.
* Eval table = `[1, 3]`.
* `(s0, s1) = computeS0S1_msb t = (t[0], t[1]) = (1, 3)`.
* Symbolic LSB: `G_0(0) = 1`, `G_0(1) = 3`. Match.
-/

namespace Example1

/-- p(x) = 1 + 2·x over ZMod 17. Monomial `x^0` with coeff 1, `x^1` with coeff 2. -/
def p : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 1 𝔽).insert ⟨#[0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1], by decide⟩ (2 : 𝔽)

def t : EvalTable 1 𝔽 := toEvalTable p
def s0 : 𝔽 := (computeS0S1_msb t).1
def s1 : 𝔽 := (computeS0S1_msb t).2

#eval s0  -- 1
#eval s1  -- 3

/-- Round-0 low-half sum equals `p(0) = 1`. -/
example : s0 = (1 : 𝔽) := by native_decide

/-- Round-0 high-half sum equals `p(1) = 3`. -/
example : s1 = (3 : 𝔽) := by native_decide

/-- Cross-check against the symbolic LSB eval-form prover at `c = 0`. -/
example :
    s0 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) := by
  native_decide

/-- Cross-check against the symbolic LSB eval-form prover at `c = 1`. -/
example :
    s1 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) := by
  native_decide

end Example1

/-! ## Example 2: n = 2, symmetric multilinear `p(x_0, x_1) = 1 + x_0 + x_1 + x_0·x_1`

Hand computation:
* p(0,0) = 1, p(0,1) = 2, p(1,0) = 2, p(1,1) = 4.
* Eval table (MSB-indexed: index `b1 b0` ↔ variable assignment `x_0 = b1, x_1 = b0`)
  = `[p(0,0), p(0,1), p(1,0), p(1,1)] = [1, 2, 2, 4]`.
* `s0 = t[0] + t[1] = 1 + 2 = 3` (variable 0 fixed to 0).
* `s1 = t[2] + t[3] = 2 + 4 = 6` (variable 0 fixed to 1).
* Symbolic LSB: `G_0(0) = 3`, `G_0(1) = 6`. Match.
-/

namespace Example2

/-- p(x_0, x_1) = 1 + x_0 + x_1 + x_0·x_1. -/
def p : CPoly.CMvPolynomial 2 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 𝔽).insert ⟨#[0, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1, 0], by decide⟩ (1 : 𝔽)
      |>.insert ⟨#[0, 1], by decide⟩ (1 : 𝔽)
      |>.insert ⟨#[1, 1], by decide⟩ (1 : 𝔽)

def t : EvalTable 2 𝔽 := toEvalTable p
def s0 : 𝔽 := (computeS0S1_msb t).1
def s1 : 𝔽 := (computeS0S1_msb t).2

#eval s0  -- 3
#eval s1  -- 6

example : s0 = (3 : 𝔽) := by native_decide
example : s1 = (6 : 𝔽) := by native_decide

/-- Cross-check against the symbolic LSB eval-form prover at `c = 0`. -/
example :
    s0 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) := by
  native_decide

/-- Cross-check against the symbolic LSB eval-form prover at `c = 1`. -/
example :
    s1 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) := by
  native_decide

/-! ### Round 1 transcript with challenge `r_0 = 5`

After binding `x_0 = 5`, we have `p(5, x_1) = 6 + 6·x_1`. So
`G_1(0) = 6`, `G_1(1) = 12` (in ZMod 17).

The table fold gives `t' = [6, 12]`:
* `t'[0] = t[0] + (t[2] - t[0]) * 5 = 1 + (2 - 1) * 5 = 6`,
* `t'[1] = t[1] + (t[3] - t[1]) * 5 = 2 + (4 - 2) * 5 = 12`.
-/

def r0 : 𝔽 := 5
def challenges1 : Fin 1 → 𝔽 := ![r0]

def tFolded : EvalTable 1 𝔽 := fold_msb_succ r0 t
def s0_r1 : 𝔽 := (computeS0S1_msb tFolded).1
def s1_r1 : 𝔽 := (computeS0S1_msb tFolded).2

#eval s0_r1  -- 6
#eval s1_r1  -- 12

example : s0_r1 = (6 : 𝔽) := by native_decide
example : s1_r1 = (12 : 𝔽) := by native_decide

/-- Cross-check round-1 fold against the symbolic LSB eval-form prover at `c = 0`. -/
example :
    s0_r1 = honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (0 : 𝔽) := by
  native_decide

/-- Cross-check round-1 fold against the symbolic LSB eval-form prover at `c = 1`. -/
example :
    s1_r1 = honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (1 : 𝔽) := by
  native_decide

end Example2

/-! ## Example 3: n = 2, asymmetric multilinear `p(x_0, x_1) = 1 + 2 x_0 + 3 x_1 + 5 x_0 x_1`

This case illustrates that `multilinearProverEvalForm` matches the **LSB**
symbolic prover (NOT MSB). For asymmetric multilinears the two conventions
disagree (cf. `EvalFormTests.lean::Example4`).

Hand computation:
* p(0,0) = 1, p(0,1) = 4, p(1,0) = 3, p(1,1) = 11 (all mod 17).
* Eval table = `[1, 4, 3, 11]`.
* `s0 = t[0] + t[1] = 1 + 4 = 5` — matches LSB `G_0(0) = 5`.
* `s1 = t[2] + t[3] = 3 + 11 = 14` — matches LSB `G_0(1) = 14`.
* MSB `G_0(1) = 15 ≠ 14`, so the table prover is *not* in MSB convention.
-/

namespace Example3

/-- p(x_0, x_1) = 1 + 2 x_0 + 3 x_1 + 5 x_0 x_1. -/
def p : CPoly.CMvPolynomial 2 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 𝔽).insert ⟨#[0, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1, 0], by decide⟩ (2 : 𝔽)
      |>.insert ⟨#[0, 1], by decide⟩ (3 : 𝔽)
      |>.insert ⟨#[1, 1], by decide⟩ (5 : 𝔽)

def t : EvalTable 2 𝔽 := toEvalTable p
def s0 : 𝔽 := (computeS0S1_msb t).1
def s1 : 𝔽 := (computeS0S1_msb t).2

#eval s0  -- 5
#eval s1  -- 14

example : s0 = (5 : 𝔽) := by native_decide
example : s1 = (14 : 𝔽) := by native_decide

/-- Cross-check `s0` against the symbolic LSB eval-form prover at `c = 0`. -/
example :
    s0 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (0 : 𝔽) := by
  native_decide

/-- Cross-check `s1` against the symbolic LSB eval-form prover at `c = 1`. -/
example :
    s1 = honestProverMessageEvalsAt domain p ⟨0, by decide⟩ Fin.elim0 (1 : 𝔽) := by
  native_decide

/-! ### Round 1 transcript with challenge `r_0 = 5`

After binding `x_0 = 5`, we have `p(5, x_1) = 11 + 11 x_1` (mod 17), so
`G_1(0) = 11`, `G_1(1) = 5` (mod 17).

The table fold yields `t' = [11, 5]`:
* `t'[0] = t[0] + (t[2] - t[0]) * 5 = 1 + (3 - 1) * 5 = 11`,
* `t'[1] = t[1] + (t[3] - t[1]) * 5 = 4 + (11 - 4) * 5 = 39 ≡ 5 (mod 17)`.
-/

def r0 : 𝔽 := 5
def challenges1 : Fin 1 → 𝔽 := ![r0]

def tFolded : EvalTable 1 𝔽 := fold_msb_succ r0 t
def s0_r1 : 𝔽 := (computeS0S1_msb tFolded).1
def s1_r1 : 𝔽 := (computeS0S1_msb tFolded).2

#eval s0_r1  -- 11
#eval s1_r1  -- 5

example : s0_r1 = (11 : 𝔽) := by native_decide
example : s1_r1 = (5 : 𝔽) := by native_decide

/-- Cross-check round-1 fold against the symbolic LSB eval-form prover at `c = 0`. -/
example :
    s0_r1 = honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (0 : 𝔽) := by
  native_decide

/-- Cross-check round-1 fold against the symbolic LSB eval-form prover at `c = 1`. -/
example :
    s1_r1 = honestProverMessageEvalsAt domain p ⟨1, by decide⟩ challenges1 (1 : 𝔽) := by
  native_decide

/-- Full transcript via `multilinearProverEvalForm`: pinned `(s0, s1)` pairs
    for both rounds, given challenges `![5, _]` (the second challenge is
    irrelevant for the round-1 message since the prover emits before reading
    the next challenge). -/
def transcript : List (𝔽 × 𝔽) :=
  multilinearProverEvalForm (n := 2) ![r0, 0] t

#eval transcript  -- [(5, 14), (11, 5)]

example : transcript = [((5 : 𝔽), (14 : 𝔽)), ((11 : 𝔽), (5 : 𝔽))] := by
  native_decide

end Example3

end __MultilinearProverTests__
