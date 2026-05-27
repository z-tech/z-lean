import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Events.BadRound

-- a transcript is "bad" if at least one round polynomial (in the first k rounds)
-- differs from the honest one
def BadTranscriptEvent
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 k.val) : Prop :=
  ∃ i : Fin k.val,
    BadRound k domain (t.roundPolys i) p t.challenges i
