import Sumcheck.IP.SharpSAT.CNF
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.Rename

namespace SharpSAT

open CPoly

-- Field embedding of booleans: true ↦ 1, false ↦ 0.
def boolToField {𝔽 : Type*} [Zero 𝔽] [One 𝔽] (b : Bool) : 𝔽 :=
  if b then 1 else 0

section BoolToField

variable {𝔽 : Type*} [Field 𝔽]

@[simp] lemma boolToField_true : (boolToField true : 𝔽) = 1 := rfl
@[simp] lemma boolToField_false : (boolToField false : 𝔽) = 0 := rfl

@[simp] lemma boolToField_or (a b : Bool) :
    (boolToField (a || b) : 𝔽) =
      1 - (1 - boolToField a) * (1 - boolToField b) := by
  cases a <;> cases b <;> simp [boolToField]

@[simp] lemma boolToField_and (a b : Bool) :
    (boolToField (a && b) : 𝔽) = boolToField a * boolToField b := by
  cases a <;> cases b <;> simp [boolToField]

end BoolToField

-- Evaluating the polynomial `CMvPolynomial.X i` at `vals` returns `vals i`.
lemma eval_X_eq {𝔽 : Type*} {n : ℕ} [CommSemiring 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (vals : Fin n → 𝔽) (i : Fin n) :
    (CMvPolynomial.X i : CMvPolynomial n 𝔽).eval vals = vals i := by
  rw [eval_equiv, CMvPolynomial.fromCMvPolynomial_X]
  exact MvPolynomial.eval_X _

-- Universe-polymorphic `eval_sub`. CompPoly's upstream `eval_sub` lives in a
-- `{R : Type}` section so it only unifies at universe 0; we restate it at
-- `Type*` so it matches our `{𝔽 : Type*}` callers.
lemma eval_sub' {𝔽 : Type*} {n : ℕ} [CommRing 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (vals : Fin n → 𝔽) (p q : CMvPolynomial n 𝔽) :
    (p - q).eval vals = p.eval vals - q.eval vals := by
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (RingHom.id 𝔽) vals).map_sub p q

-- Arithmetize a single literal:
--   xᵢ  ↦ Xᵢ
--   ¬xᵢ ↦ 1 - Xᵢ
def arithLit {𝔽 : Type*} {n : ℕ} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (ℓ : Literal n) : CMvPolynomial n 𝔽 :=
  if ℓ.pol then CMvPolynomial.X ℓ.var
  else (1 : CMvPolynomial n 𝔽) - CMvPolynomial.X ℓ.var

-- Arithmetize a 3-clause as 1 - ∏(1 - arithLit ℓᵢ).
def arithClause {𝔽 : Type*} {n : ℕ} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (c : Clause3 n) : CMvPolynomial n 𝔽 :=
  1 - (1 - arithLit (𝔽 := 𝔽) c.ℓ₁) *
      (1 - arithLit (𝔽 := 𝔽) c.ℓ₂) *
      (1 - arithLit (𝔽 := 𝔽) c.ℓ₃)

-- Arithmetize a 3-CNF formula as the product of its clause polynomials.
def arithmetize {𝔽 : Type*} {n : ℕ} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (φ : CNF3 n) : CMvPolynomial n 𝔽 :=
  φ.foldr (fun c acc => arithClause (𝔽 := 𝔽) c * acc) 1

section EvalLemmas

variable {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

lemma eval_arithLit {n : ℕ} (ℓ : Literal n) (x : Fin n → Bool) :
    (arithLit (𝔽 := 𝔽) ℓ).eval (fun i => boolToField (x i)) =
      boolToField (ℓ.eval x) := by
  unfold arithLit Literal.eval
  cases ℓ.pol <;> cases hx : x ℓ.var <;>
    simp [hx, eval_X_eq, boolToField, eval_sub']

lemma eval_arithClause {n : ℕ} (c : Clause3 n) (x : Fin n → Bool) :
    (arithClause (𝔽 := 𝔽) c).eval (fun i => boolToField (x i)) =
      boolToField (c.eval x) := by
  unfold arithClause Clause3.eval
  rw [show (c.ℓ₁.eval x || c.ℓ₂.eval x || c.ℓ₃.eval x)
        = (c.ℓ₁.eval x || (c.ℓ₂.eval x || c.ℓ₃.eval x)) from by
    cases c.ℓ₁.eval x <;> cases c.ℓ₂.eval x <;> cases c.ℓ₃.eval x <;> rfl]
  simp [eval_sub', eval_arithLit, boolToField_or, mul_assoc]

lemma eval_arithmetize {n : ℕ} (φ : CNF3 n) (x : Fin n → Bool) :
    (arithmetize (𝔽 := 𝔽) φ).eval (fun i => boolToField (x i)) =
      boolToField (φ.eval x) := by
  induction φ with
  | nil => simp [arithmetize, CNF3.eval, boolToField]
  | cons c φ ih =>
      simp only [arithmetize, List.foldr_cons] at *
      rw [eval_mul, eval_arithClause, ih, CNF3.eval_cons, boolToField_and]

/-- **Indicator-form arithmetization.** At any boolean assignment, the
arithmetized formula evaluates to `1` if the formula is satisfied and `0`
otherwise. Summing this over `{0,1}^n` therefore counts satisfying
assignments — the reduction used by `honestClaim_arithmetize_eq_numSatisfying`. -/
lemma eval_arithmetize_eq_indicator {n : ℕ} (φ : CNF3 n) (x : Fin n → Bool) :
    (arithmetize (𝔽 := 𝔽) φ).eval (fun i => boolToField (x i)) =
      (if φ.eval x = true then (1 : 𝔽) else 0) := by
  rw [eval_arithmetize]
  cases φ.eval x <;> simp [boolToField]

end EvalLemmas

end SharpSAT
