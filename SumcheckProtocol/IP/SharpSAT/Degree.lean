import SumcheckProtocol.IP.SharpSAT.Arithmetize
import SumcheckProtocol.Properties.Probability.Fields
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.MvPolyEquiv.Instances
import CompPoly.Multivariate.VarsDegrees
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

namespace SharpSAT

open CPoly

section Helpers

variable {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}

-- Bridge a CMvPolynomial degree claim to MvPolynomial via `degreeOf_equiv`.
omit [BEq 𝔽] [LawfulBEq 𝔽] in
private lemma degreeOf_eq (p : CMvPolynomial n 𝔽) (i : Fin n) :
    p.degreeOf i = (fromCMvPolynomial p).degreeOf i :=
  congrFun (CPoly.degreeOf_equiv (S := 𝔽) (p := p)) i

lemma degreeOf_one_c (i : Fin n) :
    (1 : CMvPolynomial n 𝔽).degreeOf i = 0 := by
  rw [degreeOf_eq, CPoly.map_one, MvPolynomial.degreeOf_one]

lemma degreeOf_X_le_c (i j : Fin n) :
    (CMvPolynomial.X j : CMvPolynomial n 𝔽).degreeOf i ≤ 1 := by
  rw [degreeOf_eq, CMvPolynomial.fromCMvPolynomial_X]
  rw [MvPolynomial.degreeOf_X]
  split <;> simp

lemma degreeOf_add_le_c (p q : CMvPolynomial n 𝔽) (i : Fin n) :
    (p + q).degreeOf i ≤ max (p.degreeOf i) (q.degreeOf i) := by
  rw [degreeOf_eq, degreeOf_eq p, degreeOf_eq q, CPoly.map_add]
  exact MvPolynomial.degreeOf_add_le i _ _

lemma degreeOf_sub_le_c (p q : CMvPolynomial n 𝔽) (i : Fin n) :
    (p - q).degreeOf i ≤ max (p.degreeOf i) (q.degreeOf i) := by
  rw [sub_eq_add_neg]
  calc (p + -q).degreeOf i
      ≤ max (p.degreeOf i) ((-q).degreeOf i) := degreeOf_add_le_c p (-q) i
    _ = max (p.degreeOf i) (q.degreeOf i) := by
        congr 1
        rw [degreeOf_eq, degreeOf_eq q, CPoly.map_neg, MvPolynomial.degreeOf_neg]

lemma degreeOf_mul_le_c (p q : CMvPolynomial n 𝔽) (i : Fin n) :
    (p * q).degreeOf i ≤ p.degreeOf i + q.degreeOf i := by
  rw [degreeOf_eq, degreeOf_eq p, degreeOf_eq q, CPoly.map_mul]
  exact MvPolynomial.degreeOf_mul_le i _ _

end Helpers

section DegreeBounds

variable {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}

lemma degreeOf_arithLit_le (ℓ : Literal n) (i : Fin n) :
    (arithLit (𝔽 := 𝔽) ℓ).degreeOf i ≤ 1 := by
  unfold arithLit
  split
  · exact degreeOf_X_le_c i ℓ.var
  · calc ((1 : CMvPolynomial n 𝔽) - CMvPolynomial.X ℓ.var).degreeOf i
        ≤ max ((1 : CMvPolynomial n 𝔽).degreeOf i)
            ((CMvPolynomial.X ℓ.var : CMvPolynomial n 𝔽).degreeOf i) :=
          degreeOf_sub_le_c _ _ i
      _ ≤ max 0 1 := by
          apply max_le_max
          · rw [degreeOf_one_c]
          · exact degreeOf_X_le_c i ℓ.var
      _ = 1 := by norm_num

lemma degreeOf_arithClause_le (c : Clause3 n) (i : Fin n) :
    (arithClause (𝔽 := 𝔽) c).degreeOf i ≤ 3 := by
  unfold arithClause
  -- 1 - ((1 - ℓ₁) * (1 - ℓ₂) * (1 - ℓ₃))
  have h1ℓ : ∀ ℓ : Literal n,
      ((1 : CMvPolynomial n 𝔽) - arithLit ℓ).degreeOf i ≤ 1 := by
    intro ℓ
    calc ((1 : CMvPolynomial n 𝔽) - arithLit ℓ).degreeOf i
        ≤ max ((1 : CMvPolynomial n 𝔽).degreeOf i) ((arithLit (𝔽 := 𝔽) ℓ).degreeOf i) :=
          degreeOf_sub_le_c _ _ i
      _ ≤ max 0 1 := by
          apply max_le_max
          · rw [degreeOf_one_c]
          · exact degreeOf_arithLit_le ℓ i
      _ = 1 := by norm_num
  have hprod12 :
      (((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₁) *
        ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₂)).degreeOf i ≤ 2 := by
    calc _ ≤ ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₁).degreeOf i +
            ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₂).degreeOf i :=
          degreeOf_mul_le_c _ _ i
      _ ≤ 1 + 1 := add_le_add (h1ℓ _) (h1ℓ _)
  have hprod123 :
      (((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₁) *
        ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₂) *
        ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₃)).degreeOf i ≤ 3 := by
    calc _ ≤ _ + ((1 : CMvPolynomial n 𝔽) - arithLit c.ℓ₃).degreeOf i :=
          degreeOf_mul_le_c _ _ i
      _ ≤ 2 + 1 := add_le_add hprod12 (h1ℓ _)
  calc _ ≤ max ((1 : CMvPolynomial n 𝔽).degreeOf i) _ :=
          degreeOf_sub_le_c _ _ i
    _ ≤ max 0 3 := max_le_max (by rw [degreeOf_one_c]) hprod123
    _ = 3 := by norm_num

lemma degreeOf_arithmetize_le (φ : CNF3 n) (i : Fin n) :
    (arithmetize (𝔽 := 𝔽) φ).degreeOf i ≤ 3 * φ.length := by
  induction φ with
  | nil => simp [arithmetize, degreeOf_one_c]
  | cons c φ ih =>
      simp only [arithmetize, List.foldr_cons, List.length_cons]
      calc (arithClause (𝔽 := 𝔽) c * _).degreeOf i
          ≤ (arithClause (𝔽 := 𝔽) c).degreeOf i + _ := degreeOf_mul_le_c _ _ i
        _ ≤ 3 + 3 * φ.length := add_le_add (degreeOf_arithClause_le c i) ih
        _ = 3 * (φ.length + 1) := by ring

/-- The arithmetized 3-CNF has individual degree at most `3·|φ|`: each clause
contributes an `arithClause` factor of individual degree at most 3, and the
product over `|φ|` clauses adds. -/
lemma maxIndDegree_arithmetize_le (φ : CNF3 n) :
    maxIndDegree (arithmetize (𝔽 := 𝔽) φ) ≤ 3 * φ.length := by
  unfold maxIndDegree
  refine Finset.sup_le ?_
  intro i _
  exact degreeOf_arithmetize_le φ i

end DegreeBounds

section SoundnessBound

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}

/-- The #SAT soundness error is bounded by `n · 3·|φ| / |𝔽|` — the standard
Schwartz–Zippel-style bound with individual degree `3·|φ|` from the arithmetized
3-CNF. Making this ≤ 1/3 (as required for IP membership) reduces to a
field-size lower bound. -/
theorem sharpSAT_soundnessError_le (φ : CNF3 n) :
    soundnessError (arithmetize (𝔽 := 𝔽) φ)
      ≤ (n : ℚ) * (3 * φ.length : ℕ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
  unfold soundnessError
  rcases Nat.eq_zero_or_pos (fieldSize (𝔽 := 𝔽)) with hF | hF
  · simp [hF]
  have hpos : (0 : ℚ) < (fieldSize (𝔽 := 𝔽) : ℚ) := by exact_mod_cast hF
  rw [div_le_div_iff_of_pos_right hpos]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast maxIndDegree_arithmetize_le φ

end SoundnessBound

end SharpSAT
