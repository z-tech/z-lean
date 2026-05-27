import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv.Core
import Mathlib.Algebra.MvPolynomial.Polynomial

-- The polynomial g - h, used by the soundness chain to invoke
-- `CPoly.CMvPolynomial.eval_ext_univariate` (degree-bounded Schwartz-Zippel).
@[simp] noncomputable def differencePoly
  {n : ℕ} {𝔽 : Type _} [CommRing 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : MvPolynomial (Fin n) 𝔽 :=
  CPoly.fromCMvPolynomial g - CPoly.fromCMvPolynomial h
