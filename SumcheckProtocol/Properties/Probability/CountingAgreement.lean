import SumcheckProtocol.Properties.Events.Agreement
import SumcheckProtocol.Properties.Probability.Universe

@[simp] def countAssignmentsCausingAgreement
  {n} {𝔽} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (g h : CPoly.CMvPolynomial n 𝔽) : ℕ :=
  {assignment ∈ allAssignmentsN n 𝔽 | AgreementAtEvent g h assignment}.card
