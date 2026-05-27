import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Events.BadRound

import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Prover

-- a transcript is "bad" if at least one round polynomial differs from honest
def BadTranscriptEvent
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  ∃ i : Fin n,
    BadRound domain (t.roundPolys i) p t.challenges i
