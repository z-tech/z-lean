import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Events.Accepts
import SumcheckProtocol.Properties.Probability.Challenges

noncomputable def probSoundness
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)) : ℚ :=
  probEvent (E := AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P)
