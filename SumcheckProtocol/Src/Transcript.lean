import CompPoly.Multivariate.CMvPolynomial
import SumcheckProtocol.Src.Prover
import InteractiveProtocol.Src.Protocol

-- a sumcheck transcript: the round polynomials and verifier challenges
structure Transcript (𝔽 : Type _) (n : ℕ) [CommRing 𝔽] where
  roundPolys : Fin n → (CPoly.CMvPolynomial 1 𝔽)
  challenges : Fin n → 𝔽

-- evaluate a round polynomial at the challenge to get the next round's claim
@[simp] def nextClaim {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (roundChallenge : 𝔽)
  (roundP : CPoly.CMvPolynomial 1 𝔽) : 𝔽 :=
  CPoly.CMvPolynomial.eval (fun _ => roundChallenge) roundP

-- compute the intermediate claims from an initial claim, round polynomials, and challenges
-- claims(0) = initialClaim, claims(k+1) = nextClaim(challenges(k), roundPolys(k))
def generateHonestClaims
  {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
  (initialClaim : 𝔽)
  (roundPolys : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (challenges : Fin n → 𝔽) : Fin (n+1) → 𝔽
  | ⟨0, _⟩ => initialClaim
  | ⟨k+1, hk⟩ =>
      let i : Fin n := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      nextClaim (challenges i) (roundPolys i)

-- compute claims from a transcript and initial claim
def Transcript.claims {𝔽} {n} [CommRing 𝔽] [DecidableEq 𝔽]
  (t : Transcript 𝔽 n) (initialClaim : 𝔽) : Fin (n+1) → 𝔽 :=
  generateHonestClaims initialClaim t.roundPolys t.challenges

def generateHonestTranscript
  {𝔽} {n} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (claimP  : CPoly.CMvPolynomial n 𝔽)
  (_initialClaim : 𝔽)
  (challenges : Fin n → 𝔽) : Transcript 𝔽 n :=
  { roundPolys := fun i => honestProverMessageAt domain claimP i (challengeSubset challenges i)
    challenges := challenges }
