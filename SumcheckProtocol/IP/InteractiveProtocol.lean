import SumcheckProtocol.IP.Statement
import InteractiveProtocol.Properties.Soundness
import SumcheckProtocol.Properties.Theorems
import SumcheckProtocol.Properties.Events
import SumcheckProtocol.Properties.Probability

-- Here we show how sumcheck's completeness and soundness lift into the IP framework

theorem sumcheck_hasSoundnessError {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasSoundnessError
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)
      sumcheckClaimIsCorrect
      (fun st => soundnessError st.polynomial) := by
  intro st P hFalse
  unfold probAccept
  -- AcceptsOnChallenges IS (sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩).verifierAccepts ∘ generateTranscript
  have hEq : (fun r => (sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩).verifierAccepts st
      (generateTranscript (sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩) st P r))
    = (fun r => AcceptsOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r) := rfl
  rw [hEq]
  exact soundness_dishonest st P (by unfold sumcheckClaimIsCorrect at hFalse; exact hFalse)

theorem sumcheck_hasPerfectCompleteness {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)
      sumcheckClaimIsCorrect
      (sumcheckHonestProver ⟨n, Nat.lt_succ_self n⟩) := by
  intro st hTrue
  unfold probAccept
  have hEq : (fun r => (sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩).verifierAccepts st
      (generateTranscript (sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩) st (sumcheckHonestProver ⟨n, Nat.lt_succ_self n⟩) r))
    = (fun r => AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ st.domain st.polynomial st.claim
        (generateHonestTranscript st.domain st.polynomial st.claim r)) := by
    rfl
  rw [hEq, hTrue]
  exact perfect_completeness st.domain st.polynomial
