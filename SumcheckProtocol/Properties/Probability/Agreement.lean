import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Probability.CountingAgreement
import SumcheckProtocol.Properties.Probability.CountingPolynomials

@[simp] def probAgreementAtRandomChallenge
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽)
  (_h_not_equal : g ≠ h) : ℚ :=
    countAssignmentsCausingAgreement g h / countAllAssignmentsN (𝔽 := 𝔽) n
