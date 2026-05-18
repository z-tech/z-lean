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

variable {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

/-- Substitution map sending `Fin (n+1)` position 0 to the constant `w` and
positions `1..n` to the corresponding variables of `CMvPolynomial n 𝔽`. -/
def substRound0Map {n : ℕ} (w : 𝔽) :
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

/-! ## Eval lemma signatures (proofs deferred to upstream CompPoly)

The natural primitive `eval_substRound0` —
`(substRound0 w p).eval b = p.eval (Fin.cons w b)` — is the
unconditional pointwise evaluation property of `bind₁` at our specific
substitution map. Its proof factors through `MvPolynomial.aeval_bind₁`
on the Mathlib side combined with `fromCMvPolynomial`'s ring-hom
structure; the cleanest place for it is alongside `bind₁` in CompPoly.

Until that upstream PR lands, downstream theorems that depend on this
fact (`fold_correctness`, `multi_round_correctness`) take it as an
explicit hypothesis — see the **`EvalSubstRound0Hyp`** abbreviation
below. When the upstream lemma lands, every callsite supplies the
proven witness and the hypothesis disappears.

This file does not introduce a `sorry`: it only provides a named
**hypothesis abbreviation** that downstream theorems consume. -/

end CPoly

/-- The unconditional pointwise-evaluation property of `substRound0`,
phrased as a Prop-valued abbreviation so downstream theorems can take
it as a named hypothesis until the upstream CompPoly lemma lands. -/
def EvalSubstRound0Hyp (𝔽 : Type _) [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] (n : ℕ) : Prop :=
  ∀ (w : 𝔽) (p : CPoly.CMvPolynomial (n + 1) 𝔽) (b : Fin n → 𝔽),
    (CPoly.substRound0 w p).eval b = p.eval (Fin.cons w b)

/-- The multilinear extension at variable 0: when `p` is multilinear in
variable 0 (`degreeOf 0 p ≤ 1`), `(substRound0 w p).eval b` is a linear
interpolation between `p.eval (Fin.cons 0 b)` and `p.eval (Fin.cons 1 b)`.

This is the key property `fold_correctness` consumes: the `(1−w)·lo +
w·hi` linear interpolation in `fold_msb_succ` is correct exactly because
binding a multilinear variable to `w` is a linear blend of binding it
to `0` and `1`. -/
def EvalSubstRound0MultilinearHyp (𝔽 : Type _) [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (n : ℕ) : Prop :=
  ∀ (w : 𝔽) (p : CPoly.CMvPolynomial (n + 1) 𝔽) (b : Fin n → 𝔽),
    CPoly.CMvPolynomial.degreeOf (0 : Fin (n + 1)) p ≤ 1 →
    (CPoly.substRound0 w p).eval b =
      (1 - w) * p.eval (Fin.cons 0 b) + w * p.eval (Fin.cons 1 b)
