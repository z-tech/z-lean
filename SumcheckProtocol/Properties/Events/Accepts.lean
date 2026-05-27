import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Verifier
import SumcheckProtocol.Properties.Events.BadTranscript

-- the verifier accepts a transcript given an initial claim
def AcceptsEvent
  {𝔽} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (initialClaim : 𝔽)
  (t : Transcript 𝔽 n) : Prop :=
  isVerifierAccepts (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩
    domain p initialClaim t = true

-- the verifier accepts the prover's transcript for a given set of challenges
-- defined directly in terms of the generic protocol interface
def AcceptsOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  sumcheckProtocolFull.verifierAccepts st (generateTranscript sumcheckProtocolFull st P r)

-- unfold AcceptsOnChallenges to the concrete AcceptsEvent for use in proofs
@[simp] lemma AcceptsOnChallenges_unfold
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  AcceptsOnChallenges st P r ↔
    AcceptsEvent st.domain st.polynomial st.claim (proverTranscriptFull st P r) := by
  rfl

-- the verifier accepts AND the transcript has a bad round
def AcceptsAndBadTranscriptOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))) :
  (Fin n → 𝔽) → Prop :=
fun r =>
  AcceptsOnChallenges st P r
  ∧ BadTranscriptEvent st.domain st.polynomial (proverTranscriptFull st P r)

@[simp] lemma AcceptsAndBadTranscriptOnChallenges_unfold
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges st P r ↔
    (AcceptsEvent st.domain st.polynomial st.claim (proverTranscriptFull st P r)
     ∧ BadTranscriptEvent st.domain st.polynomial (proverTranscriptFull st P r)) := by
  simp [AcceptsAndBadTranscriptOnChallenges, AcceptsOnChallenges_unfold]
