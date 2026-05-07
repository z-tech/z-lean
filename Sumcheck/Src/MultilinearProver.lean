import CompPoly.Multilinear.Basic
import CompPoly.Multivariate.CMvPolynomial

import Sumcheck.Src.CMvPolynomial
import Sumcheck.Src.Hypercube
import Sumcheck.Src.Convention

/-!
# Phase 2: Multilinear evaluation-table prover

This file mirrors the Rust `multilinear_sumcheck.rs` prover algorithm in Lean.
The state is an evaluation table — an `EvalTable n 𝔽 := Vector 𝔽 (2^n)` —
indexed by Boolean assignments to `n` variables.

We use the **MSB convention** natively (round 0 splits the table into low half
`[0, 2^(n-1))` and high half `[2^(n-1), 2^n)`, binding the high-order variable
first). The Phase 3 `Convention` layer (LSB↔MSB via `reverseFin`) is imported
to keep us interoperable with the LSB-style symbolic prover in `Src/Prover.lean`.

## Outline of definitions in this file

* `EvalTable n 𝔽` — Vector of `2^n` field elements, indexed little-endian as
  per CompPoly (we re-use `CMlPolynomialEval`).
* `boolPoint_msb` — turns an index `i : Fin (2^n)` into a Boolean point
  `Fin n → 𝔽` under the **MSB** convention (bit `n-1-j` of `i` is the value at
  variable `j`). The Phase 3 plan calls for using `reverseFin` to convert the
  CompPoly LSB indexing to MSB; we encode that directly here.
* `toEvalTable` — turns a `CMvPolynomial n 𝔽` into its MSB evaluation table
  by evaluating at every Boolean point.
* `computeS0S1_msb` — the `(s0, s1)` pair from `compute_sumcheck_polynomial`:
  `s0` is the sum over the low half, `s1` is the sum over the high half.
* `fold_msb_succ` / `fold_msb` — the MSB in-place fold:
  `t'[k] = t[k] + (t[k + 2^m] - t[k]) * w` for `k : Fin (2^m)`.
* `multilinearProverEvalForm` — round-by-round prover, by structural recursion
  on the number of remaining variables.

The proofs of correctness against the symbolic spec live in
`Sumcheck/Properties/MultilinearProver.lean`.
-/

namespace Sumcheck.MultilinearProver

open CompPoly

/-- The evaluation-table state. A length-`2^n` `Vector` of field elements,
    one per Boolean assignment to `n` variables. We re-use CompPoly's
    `CMlPolynomialEval`, which is defined as `Vector R (2^n)`. -/
abbrev EvalTable (n : ℕ) (𝔽 : Type _) := CompPoly.CMlPolynomialEval 𝔽 n

variable {𝔽 : Type _}

/-! ### Boolean-point lookups -/

/-- Boolean assignment to `n` variables under the **MSB** convention.

    The bit at position `j : Fin n` of the assignment is bit `n-1-j` of `i`,
    so that variable `0` is the *most* significant. CompPoly itself indexes
    little-endian (bit `j` of `i` is variable `j`); we obtain MSB by composing
    with `Sumcheck.reverseFin`.

    Returns `1 : 𝔽` for a set bit, `0 : 𝔽` for an unset bit. -/
def boolPoint_msb [Zero 𝔽] [One 𝔽]
    {n : ℕ} (i : Fin (2^n)) : Fin n → 𝔽 :=
  fun j =>
    let k : Fin n := Sumcheck.reverseFin j
    if (BitVec.ofFin i).getLsb k then (1 : 𝔽) else (0 : 𝔽)

/-! ### `toEvalTable` -/

/-- Materialise a multivariate polynomial as its evaluation table over the
    Boolean hypercube, MSB-indexed. -/
def toEvalTable [CommSemiring 𝔽]
    {n : ℕ} (p : CPoly.CMvPolynomial n 𝔽) : EvalTable n 𝔽 :=
  Vector.ofFn (fun i : Fin (2^n) =>
    CPoly.CMvPolynomial.eval (boolPoint_msb (𝔽 := 𝔽) i) p)

/-! ### `(s0, s1)` computation (MSB) -/

/-- Compute `(s0, s1)` from an evaluation table.

    For `n ≥ 1`, with half size `h := 2^(n-1)`:

      `s0 = Σ_{k : Fin h} t[castAdd k]   = sum over the low half`
      `s1 = Σ_{k : Fin h} t[natAdd  k]   = sum over the high half`

    For `n = 0` (single entry, scalar) the polynomial has degree-0 round message
    so we return `(t[0], 0)` per the Rust `compute_sumcheck_polynomial`
    `len == 1` branch. -/
def computeS0S1_msb [AddCommMonoid 𝔽]
    {n : ℕ} (t : EvalTable n 𝔽) : 𝔽 × 𝔽 :=
  match n, t with
  | 0, t =>
      have h0 : (0 : ℕ) < 2 ^ 0 := by simp
      (t[(⟨0, h0⟩ : Fin (2^0))], 0)
  | n + 1, t =>
      let h : ℕ := 2 ^ n
      have hsplit : h + h = 2 ^ (n + 1) := by
        show 2^n + 2^n = 2^(n+1)
        rw [pow_succ]; ring
      have htlt : ∀ k : Fin h, h + k.val < 2 ^ (n+1) := by
        intro k
        have := k.isLt
        omega
      have hcastlt : ∀ k : Fin h, k.val < 2 ^ (n+1) := by
        intro k
        have hk : k.val < h := k.isLt
        have hh : h ≤ 2 ^ (n+1) := by
          show 2^n ≤ 2^(n+1); rw [pow_succ]; omega
        omega
      let s0 : 𝔽 := ∑ k : Fin h, t[(⟨k.val, hcastlt k⟩ : Fin (2^(n+1)))]
      let s1 : 𝔽 := ∑ k : Fin h, t[(⟨h + k.val, htlt k⟩ : Fin (2^(n+1)))]
      (s0, s1)

/-! ### MSB fold -/

/-- MSB fold (successor form): `t'[k] = t[k] + (t[k + 2^m] - t[k]) * w`
    for `k : Fin (2^m)`.

    This mirrors the in-place loop body of the Rust `fold` function for
    `values.len() = 2^(m+1)` (so `half = 2^m`). -/
def fold_msb_succ [CommRing 𝔽]
    {m : ℕ} (w : 𝔽) (t : EvalTable (m+1) 𝔽) : EvalTable m 𝔽 :=
  let h : ℕ := 2 ^ m
  have hcastlt : ∀ k : Fin h, k.val < 2 ^ (m+1) := by
    intro k
    have hk : k.val < h := k.isLt
    have hh : h ≤ 2 ^ (m+1) := by
      show 2^m ≤ 2^(m+1); rw [pow_succ]; omega
    omega
  have htlt : ∀ k : Fin h, h + k.val < 2 ^ (m+1) := by
    intro k
    have := k.isLt
    show 2^m + k.val < 2^(m+1)
    rw [pow_succ]; omega
  Vector.ofFn (fun k : Fin h =>
    let lo := t[(⟨k.val, hcastlt k⟩ : Fin (2^(m+1)))]
    let hi := t[(⟨h + k.val, htlt k⟩ : Fin (2^(m+1)))]
    lo + (hi - lo) * w)

/-- Convenience MSB fold that case-splits on `n`. For `n = 0` the fold is the
    identity (no variables left to bind); for `n = m+1` it reduces by
    `fold_msb_succ`. The output type matches the Rust contract: folding a
    length-`2^n` table yields a length-`2^(n-1)` table when `n ≥ 1`, and a
    length-`1` table is left alone (the Rust `values.len() <= 1` branch).

    For uniformity with the recursive prover we package this via `Nat.rec` on
    `n`: when `n = 0`, the table is left unchanged (degenerate, since there are
    no remaining open variables to fold). -/
def fold_msb [CommRing 𝔽] :
    {n : ℕ} → (w : 𝔽) → (t : EvalTable n 𝔽) → EvalTable (n - 1) 𝔽
  | 0,     _, t => t
  | _ + 1, w, t => fold_msb_succ w t

/-! ### The recursive prover -/

/-- The eval-table multilinear prover, by structural recursion on `n`.

    On round 0 (i.e. when called with an `EvalTable n` for `n ≥ 1`):

    1. emit `computeS0S1_msb t` as the round message,
    2. read the round-0 challenge from `challenges`,
    3. fold via `fold_msb_succ`, recursing on the resulting `EvalTable (n-1)`.

    Returns the list of `(s0, s1)` pairs, one per round, of length `n`. -/
def multilinearProverEvalForm [CommRing 𝔽] :
    {n : ℕ} → (challenges : Fin n → 𝔽) → (t : EvalTable n 𝔽) → List (𝔽 × 𝔽)
  | 0,     _,          _ => []
  | n + 1, challenges, t =>
      let msg : 𝔽 × 𝔽 := computeS0S1_msb t
      let r : 𝔽 := challenges ⟨0, Nat.succ_pos n⟩
      let t' : EvalTable n 𝔽 := fold_msb_succ r t
      msg :: multilinearProverEvalForm
        (fun j => challenges ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) t'

end Sumcheck.MultilinearProver
