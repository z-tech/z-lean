import Sumcheck.IP.Statement
import InteractiveProtocol.Properties.Soundness
import Sumcheck.Properties.Theorems
import Sumcheck.Properties.Events
import Sumcheck.Properties.Probability

-- Here we show how sumcheck's completeness and soundness lift into the IP framework

theorem sumcheck_hasSoundnessError {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      (fun st => soundnessError st.polynomial) := by
  intro st P hFalse
  unfold probAccept
  -- AcceptsOnChallenges IS sumcheckProtocol.verifierAccepts ∘ generateTranscript
  have hEq : (fun r => sumcheckProtocol.verifierAccepts st
      (generateTranscript sumcheckProtocol st P r))
    = (fun r => AcceptsOnChallenges st P r) := rfl
  rw [hEq]
  exact soundness_dishonest st P (by unfold sumcheckClaimIsCorrect at hFalse; exact hFalse)

theorem sumcheck_hasPerfectCompleteness {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n))
      sumcheckClaimIsCorrect
      sumcheckHonestProver := by
  intro st hTrue
  unfold probAccept
  have hEq : (fun r => sumcheckProtocol.verifierAccepts st
      (generateTranscript sumcheckProtocol st sumcheckHonestProver r))
    = (fun r => AcceptsEvent st.domain st.polynomial st.claim
        (generateHonestTranscript st.domain st.polynomial st.claim r)) := by
    rfl
  rw [hEq, hTrue]
  exact perfect_completeness st.domain st.polynomial
