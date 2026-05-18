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

/-! ## General `eval_bind₁` lemma -/

/-- Universal property of `bind₁`: evaluating the substituted polynomial
at `b` is the same as evaluating the original at the substituted-then-
evaluated map. Key technical bridge for `eval_substRound0`. -/
theorem eval_bind₁_aux {n m : ℕ}
    (f : Fin n → CMvPolynomial m 𝔽) (p : CMvPolynomial n 𝔽) (b : Fin m → 𝔽) :
    (bind₁ f p).eval b = p.eval (fun i => (f i).eval b) := by
  classical
  -- Package both sides as `RingHom`s `CMvPolynomial n 𝔽 →+* 𝔽`.
  let φLHS : CMvPolynomial n 𝔽 →+* 𝔽 :=
    (CMvPolynomial.eval₂Hom (RingHom.id 𝔽) b).comp
      (CMvPolynomial.eval₂Hom (algebraMap 𝔽 (CMvPolynomial m 𝔽)) f)
  let φRHS : CMvPolynomial n 𝔽 →+* 𝔽 :=
    CMvPolynomial.eval₂Hom (RingHom.id 𝔽) (fun i => (f i).eval b)
  -- Transport: prove φLHS.comp polyEq.symm = φRHS.comp polyEq.symm via ringHom_ext,
  -- then apply at polyEq p.
  let polyEq : CMvPolynomial n 𝔽 ≃+* MvPolynomial (Fin n) 𝔽 := CPoly.polyRingEquiv
  suffices h : φLHS.comp polyEq.symm.toRingHom = φRHS.comp polyEq.symm.toRingHom by
    have happ := congrArg (fun ρ : MvPolynomial (Fin n) 𝔽 →+* 𝔽 => ρ (polyEq p)) h
    simp only [RingHom.comp_apply] at happ
    have hroundtrip : polyEq.symm.toRingHom (polyEq p) = p := by
      show polyEq.symm (polyEq p) = p
      exact polyEq.left_inv p
    rw [hroundtrip] at happ
    show (CMvPolynomial.eval₂Hom (RingHom.id 𝔽) b)
           ((CMvPolynomial.eval₂Hom (algebraMap 𝔽 (CMvPolynomial m 𝔽)) f) p)
        = (CMvPolynomial.eval₂Hom (RingHom.id 𝔽) (fun i => (f i).eval b)) p
    simpa [φLHS, φRHS] using happ
  refine MvPolynomial.ringHom_ext ?_ ?_
  · intro c
    have hC : polyEq.symm.toRingHom (MvPolynomial.C (σ := Fin n) c)
        = CMvPolynomial.C (n := n) c := by
      apply polyEq.injective
      show polyEq (polyEq.symm (MvPolynomial.C c)) = polyEq (CMvPolynomial.C c)
      rw [polyEq.apply_symm_apply]
      show MvPolynomial.C c = fromCMvPolynomial (CMvPolynomial.C c)
      simp [CMvPolynomial.fromCMvPolynomial_C]
    show φLHS (polyEq.symm.toRingHom (MvPolynomial.C c))
        = φRHS (polyEq.symm.toRingHom (MvPolynomial.C c))
    rw [hC]
    simp only [φLHS, φRHS, RingHom.comp_apply, CMvPolynomial.eval₂Hom_apply]
    have hLeft : CMvPolynomial.eval₂ (algebraMap 𝔽 (CMvPolynomial m 𝔽)) f
            (CMvPolynomial.C (n := n) c)
          = CMvPolynomial.C (n := m) c := by
      have := aeval_C (n := n) (R := 𝔽) (σ := CMvPolynomial m 𝔽) f c
      simpa [aeval, algebraMap] using this
    rw [hLeft]
    have hLO : CMvPolynomial.eval₂ (RingHom.id 𝔽) b (CMvPolynomial.C (n := m) c) = c := by
      have := aeval_C (n := m) (R := 𝔽) (σ := 𝔽) b c
      simpa [aeval] using this
    have hRO : CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun i => (f i).eval b)
            (CMvPolynomial.C (n := n) c) = c := by
      have := aeval_C (n := n) (R := 𝔽) (σ := 𝔽) (fun i => (f i).eval b) c
      simpa [aeval] using this
    rw [hLO, hRO]
  · intro i
    have hX : polyEq.symm.toRingHom (MvPolynomial.X (R := 𝔽) i)
        = CMvPolynomial.X (R := 𝔽) i := by
      apply polyEq.injective
      show polyEq (polyEq.symm (MvPolynomial.X i)) = polyEq (CMvPolynomial.X i)
      rw [polyEq.apply_symm_apply]
      show MvPolynomial.X i = fromCMvPolynomial (CMvPolynomial.X i)
      rw [CMvPolynomial.fromCMvPolynomial_X]
    show φLHS (polyEq.symm.toRingHom (MvPolynomial.X i))
        = φRHS (polyEq.symm.toRingHom (MvPolynomial.X i))
    rw [hX]
    simp only [φLHS, φRHS, RingHom.comp_apply, CMvPolynomial.eval₂Hom_apply]
    have hLeft : CMvPolynomial.eval₂ (algebraMap 𝔽 (CMvPolynomial m 𝔽)) f
            (CMvPolynomial.X (R := 𝔽) i) = f i := by
      have := aeval_X (n := n) (R := 𝔽) (σ := CMvPolynomial m 𝔽) f i
      simpa [aeval] using this
    have hRO : CMvPolynomial.eval₂ (RingHom.id 𝔽) (fun i => (f i).eval b)
            (CMvPolynomial.X (R := 𝔽) i) = (f i).eval b := by
      have := aeval_X (n := n) (R := 𝔽) (σ := 𝔽) (fun i => (f i).eval b) i
      simpa [aeval] using this
    rw [hLeft, hRO]
    rfl

/-- **`eval_substRound0`** (unconditional).

`(substRound0 w p).eval b = p.eval (Fin.cons w b)`. -/
theorem eval_substRound0 {n : ℕ} (w : 𝔽) (p : CMvPolynomial (n + 1) 𝔽) (b : Fin n → 𝔽) :
    (substRound0 w p).eval b = p.eval (Fin.cons w b) := by
  unfold substRound0
  rw [eval_bind₁_aux (substRound0Map w) p b]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · -- i = 0: (substRound0Map w 0).eval b = (C w).eval b = w = Fin.cons w b 0
    show (substRound0Map w 0).eval b
        = (Fin.cons (α := fun _ : Fin (n + 1) => 𝔽) w b) 0
    rw [Fin.cons_zero]
    show (substRound0Map w (0 : Fin (n + 1))).eval b = w
    have hmap : substRound0Map w (0 : Fin (n + 1)) = CMvPolynomial.C (n := n) w := by
      unfold substRound0Map; rfl
    rw [hmap]
    have := aeval_C (n := n) (R := 𝔽) (σ := 𝔽) b w
    simpa [aeval] using this
  · -- i = j.succ: (substRound0Map w j.succ).eval b = (X j).eval b = b j = Fin.cons w b j.succ
    show (substRound0Map w j.succ).eval b
        = (Fin.cons (α := fun _ : Fin (n + 1) => 𝔽) w b) j.succ
    rw [Fin.cons_succ]
    show (substRound0Map w j.succ).eval b = b j
    have hmap : substRound0Map w j.succ = CMvPolynomial.X (R := 𝔽) j := by
      unfold substRound0Map; rfl
    rw [hmap]
    have := aeval_X (n := n) (R := 𝔽) (σ := 𝔽) b j
    simpa [aeval] using this

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
