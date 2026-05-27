import SumcheckProtocol.Properties.Probability.Challenges
import SumcheckProtocol.Properties.Lemmas.HonestRoundProofs
import SumcheckProtocol.Properties.Lemmas.Degree
import SumcheckProtocol.Properties.Lemmas.Accepts
import SumcheckProtocol.Properties.Lemmas.SoundnessLemmas

-- Prob verifier accepts when all round polys are honest (and claim is honest) is one
theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  probOverChallenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsEvent (𝔽 := 𝔽) (n := n) domain p (honestClaim domain p)
        (generateHonestTranscript (𝔽 := 𝔽) (n := n) domain p (honestClaim domain p) r))
  = 1 := by
  classical
  -- the honest transcript is accepted for every challenge tuple.

  -- First, prove every honest transcript is accepted
  have hE : ∀ r : Fin n → 𝔽,
      AcceptsEvent domain p (honestClaim domain p) (generateHonestTranscript domain p (honestClaim domain p) r) := by
    intro r
    simp only [AcceptsEvent, isVerifierAccepts, Transcript.claims, Bool.and_eq_true,
      residualSum_full_eq_eval]
    constructor
    · -- roundsOk: each round passes verifierCheck and claims consistency
      rw [List.all_eq_true]
      intro i _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · -- verifierCheck passes
        simp only [verifierCheck, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · -- Sum identity: domain sum of honest poly = claim
          exact honest_transcript_sum_identity domain p r i
        · -- Degree bound: honestRoundPoly degree ≤ indDegreeK
          -- The honest polynomial has degree at most the individual degree
          have hpoly : (generateHonestTranscript domain p (honestClaim domain p) r).roundPolys i =
            honestRoundPoly domain p r i := by
            simp [generateHonestTranscript, honestRoundPoly, honestProverMessageAt]
          rw [hpoly]
          exact honest_round_poly_degree_le_ind_degree_k domain p r i
      · -- Claims consistency: claims i.succ = nextClaim (challenges i) (roundPolys i)
        -- For i : Fin n, i.succ = ⟨i.val + 1, ...⟩ which matches the succ case of generateHonestClaims
        have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
        simp only [generateHonestTranscript, generateHonestClaims, nextClaim, hsuc]
    · -- finalOk: final claim equals polynomial evaluation
      simp only [decide_eq_true_eq]
      -- Use the helper lemma that handles dependent types via induction
      exact honest_transcript_final_eq_eval n domain p r
  have hfilter :
      (Finset.univ.filter (fun r => AcceptsEvent domain p (honestClaim domain p) (generateHonestTranscript domain p (honestClaim domain p) r)) : Finset (Fin n → 𝔽))
        = Finset.univ := by
    ext r
    simp [hE r]

  simp [probEvent, allChallenges, hfilter]
