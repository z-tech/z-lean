import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Verifier
import SumcheckProtocol.Properties.Events.BadTranscript

-- the verifier accepts a transcript given an initial claim, parameterised by
-- the partial-run stop point k.
def AcceptsEvent
  {𝔽} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (initialClaim : 𝔽)
  (t : Transcript 𝔽 k.val) : Prop :=
  isVerifierAccepts (𝔽 := 𝔽) (n := n) k domain p initialClaim t = true

-- the verifier accepts the prover's transcript for a given set of challenges
def AcceptsOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k)) :
  (Fin k.val → 𝔽) → Prop :=
fun r =>
  (sumcheckProtocol k).verifierAccepts st
    (generateTranscript (sumcheckProtocol k) st P r)

-- unfold AcceptsOnChallenges to the concrete AcceptsEvent for use in proofs
@[simp] lemma AcceptsOnChallenges_unfold
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽) :
  AcceptsOnChallenges k st P r ↔
    AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st P r) := by
  rfl

-- the verifier accepts AND the transcript has a bad round
def AcceptsAndBadTranscriptOnChallenges
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k)) :
  (Fin k.val → 𝔽) → Prop :=
fun r =>
  AcceptsOnChallenges k st P r
  ∧ BadTranscriptEvent k st.domain st.polynomial (proverTranscript k st P r)

@[simp] lemma AcceptsAndBadTranscriptOnChallenges_unfold
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges k st P r ↔
    (AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st P r)
     ∧ BadTranscriptEvent k st.domain st.polynomial (proverTranscript k st P r)) := by
  simp [AcceptsAndBadTranscriptOnChallenges, AcceptsOnChallenges_unfold]
