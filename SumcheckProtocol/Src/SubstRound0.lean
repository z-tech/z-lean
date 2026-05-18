import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.MvPolyEquiv

import SumcheckProtocol.Src.CMvPolynomial

/-!
# Single-variable substitution at position 0

This file defines `substRound0 w p`, the polynomial obtained by substituting
the round-0 variable (i.e. `Fin (n+1)` position 0) of `p : CMvPolynomial (n+1) 𝔽`
with the constant `w : 𝔽`, dropping that variable from the indexing.

Used by Phase 2's multilinear eval-table prover (`SumcheckProtocol/Src/MultilinearProver.lean`)
to state the round-i+1 input table as the eval-table of `substRound0 (challenges 0) p`.
Without this primitive the symbolic statement of `fold_correctness` cannot be phrased.

Defined as a thin wrapper around CompPoly's `bind₁` with the substitution map
`Fin.cases (C w) X`, plus the basic homomorphism lemmas (`substRound0_C`,
`substRound0_add`) inherited from `bind₁`.

## Upstream-PR candidates for CompPoly

The natural primitive to upstream is the more general `substAt (i : Fin n) (w : R) p`
which substitutes any single variable. Two key lemmas to land alongside the
definition:

1. **`eval_substAt`**: `(substAt i w p).eval b = p.eval (Fin.insertNth i w b)`.
   The unconditional pointwise evaluation property — `bind₁` plus
   `MvPolynomial.aeval_bind₁` give the proof.
2. **`MLE_substAt`**: when `p` is multilinear in variable `i` (`degreeOf i p ≤ 1`),
   `(substAt i w p).eval b = (1 - w) · p.eval(insertNth i 0 b) + w · p.eval(insertNth i 1 b)`.
   Proof via the coefficient decomposition `p = q + X_i · r` for multilinear `p`
   (with `degreeOf i q = 0` and `degreeOf i r = 0`).

The round-0 specialisation (this file) is just `substAt 0 w p` instantiated, with
`Fin.insertNth 0 w b = Fin.cons w b`. Once the upstream lemmas land, this file
becomes a thin alias.

## Why round-0 specifically (here)

For Phase 2's multi-round induction, only round-0 substitution is needed at any
inductive step (the recursion always peels the *first* remaining variable).
Generalising to `substAt i` is unnecessary for the immediate use case but is
the right primitive for upstream.
-/

namespace CPoly

open CMvPolynomial

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Substitution map sending `Fin (n+1)` position 0 to the constant `w` and
positions `1..n` to the corresponding variables of `CMvPolynomial n 𝔽`. -/
@[simp] def substRound0Map {n : ℕ} (w : 𝔽) :
    Fin (n + 1) → CMvPolynomial n 𝔽 :=
  Fin.cases (CMvPolynomial.C (n := n) w) (fun i => CMvPolynomial.X (R := 𝔽) i)

/-- `substRound0 w p` substitutes the round-0 variable (`Fin (n+1)` position 0)
of `p` with the constant `w`, producing a polynomial of arity `n`. -/
def substRound0 {n : ℕ} (w : 𝔽) (p : CMvPolynomial (n + 1) 𝔽) :
    CMvPolynomial n 𝔽 :=
  bind₁ (substRound0Map w) p

@[simp] lemma substRound0_C {n : ℕ} (w : 𝔽) (c : 𝔽) :
    substRound0 (n := n) w (CMvPolynomial.C (n := n + 1) c)
      = CMvPolynomial.C (n := n) c := by
  unfold substRound0
  exact bind₁_C _ c

@[simp] lemma substRound0_add {n : ℕ} (w : 𝔽) (p q : CMvPolynomial (n + 1) 𝔽) :
    substRound0 w (p + q) = substRound0 w p + substRound0 w q := by
  unfold substRound0
  exact bind₁_add _ p q

/-! ## Eval lemmas (deferred — pending upstream `aeval_bind₁` bridge)

Two eval lemmas are needed for downstream Phase-2 multi-round correctness:

* **`eval_substRound0`** (unconditional): `(substRound0 w p).eval b = p.eval (Fin.cons w b)`.
  Mathlib has `aeval_bind₁` for `MvPolynomial`; the analogue for `CMvPolynomial`
  via the `eval_equiv`/`eval₂_equiv` bridge (in
  `CompPoly/Multivariate/MvPolyEquiv/Eval.lean`) is the bridge piece — best
  upstreamed to CompPoly so the proof here stays a one-liner.

* **`eval_substRound0_multilinear`** (conditional, multilinear): when
  `degreeOf 0 p ≤ 1`, `(substRound0 w p).eval b = (1-w)·p.eval(0,b) + w·p.eval(1,b)`.
  Requires the coefficient decomposition `p = q + X_0 · r` for multilinear `p`,
  which is also the right CompPoly upstream candidate.

Until those upstream pieces land, the multi-round Phase 2 induction
(`fold_correctness` + `multi_round_correctness`) stays parked. The Phase 2
table-form correctness (`compute_correctness_at_zero/at_one` for round 0) is
already proven in `SumcheckProtocol/Properties/MultilinearProverBridge.lean`. -/

end CPoly
