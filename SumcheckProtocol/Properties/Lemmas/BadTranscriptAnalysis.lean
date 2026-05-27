/-
  BadTranscriptAnalysis.lean

  Lemma showing that acceptance with a bad transcript implies
  there exists a round where the prover's polynomial disagrees
  with the honest polynomial but they agree on the next claim.
-/

import SumcheckProtocol.Properties.Events.Accepts
import SumcheckProtocol.Properties.Events.BadRound
import SumcheckProtocol.Properties.Lemmas.BadTranscript
import SumcheckProtocol.Properties.Lemmas.Accepts
import SumcheckProtocol.Properties.Lemmas.HonestRoundProofs

lemma accepts_and_bad_implies_exists_round_disagree_but_agree
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges st P r →
    ∃ i : Fin n, RoundDisagreeButAgreeAtChallenge st P r i := by
  classical
  intro h
  rcases h with ⟨hAcc, hBad⟩
  let t : Transcript 𝔽 n := proverTranscript st P r

  -- pick the last bad round
  have hLast : LastBadRound st P r := by
    exact badTranscript_implies_lastBadRound st P r (by simpa [t] using hBad)

  rcases hLast with ⟨i, hi_bad, hi_after⟩
  refine ⟨i, ?_⟩

  have hneq : t.roundPolys i ≠ honestRoundPoly st.domain (p := st.polynomial) (ch := r) i := by
    simpa [t] using hi_bad

  have hsuc :
      (i.succ : Fin (n + 1)) =
        ⟨i.val.succ, by exact Nat.succ_lt_succ i.isLt⟩ := by
    ext; rfl

  by_cases hlast : i.val.succ = n
  · -- last-round case
    have hfinal : t.claims st.claim (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
      exact (decide_eq_true_eq.mp (acceptsEvent_final_ok st.domain (p := st.polynomial) (claim := st.claim) (t := t) hAcc))

    have hlast_idx : (Fin.last n : Fin (n + 1)) = i.succ := by
      ext; simp [Fin.last]; omega

    have hfinal' : t.claims st.claim (i.succ) = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
      simpa [hlast_idx] using hfinal

    have ht_claim_last :
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          = CPoly.CMvPolynomial.eval r st.polynomial := by
      have := hfinal'.symm
      have htmp :
          CPoly.CMvPolynomial.eval r st.polynomial =
            nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
        simpa [t, proverTranscript, generateHonestClaims, nextClaim, hsuc] using this
      simpa [eq_comm] using htmp

    have honest_last :
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPoly st.domain (p := st.polynomial) (ch := r) i)
          = CPoly.CMvPolynomial.eval r st.polynomial := by
      simpa using (honest_last_round st.domain (p := st.polynomial) (r := r) (i := i) hlast)

    have hnc :
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPoly st.domain (p := st.polynomial) (ch := r) i) := by
      calc
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
            = CPoly.CMvPolynomial.eval r st.polynomial := ht_claim_last
        _   = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
                (honestRoundPoly st.domain (p := st.polynomial) (ch := r) i) := by
              simpa using honest_last.symm

    refine ⟨hneq, ?_⟩
    simpa [nextClaim] using hnc

  · -- not-last-round case
    have hlt : i.val.succ < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    let j : Fin n := ⟨i.val.succ, hlt⟩

    have hj_honest : t.roundPolys j = honestRoundPoly st.domain (p := st.polynomial) (ch := r) j := by
      have hij : i < j := by
        exact Fin.lt_def.mpr (Nat.lt_succ_self i.val)
      simpa [t, j] using hi_after j hij

    have hsum :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPoly st.domain (p := st.polynomial) (ch := r) j)) 0
          =
        t.claims st.claim (Fin.castSucc j) := by
      exact acceptsEvent_domain_sum_eq_claim_of_honest st.domain
        (p := st.polynomial) (claim := st.claim) (r := r) (t := t) (i := j) (hi := hj_honest) hAcc

    have hcast : (Fin.castSucc j) = i.succ := by
      ext; simp [j]

    have hclaim_i_succ :
        t.claims st.claim (i.succ)
          =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
      simp [t, proverTranscript, Transcript.claims, generateHonestClaims, nextClaim, hsuc]

    have hclaim_j :
        t.claims st.claim (Fin.castSucc j)
          =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
      simpa [hcast] using hclaim_i_succ

    have honest_step :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPoly st.domain (p := st.polynomial) (ch := r) j)) 0
          =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPoly st.domain (p := st.polynomial) (ch := r) i) := by
      simpa [j] using (honest_step_round st.domain (p := st.polynomial) (r := r) (i := i) hlt)

    refine ⟨hneq, ?_⟩
    calc
      nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          = t.claims st.claim (Fin.castSucc j) := by
              simpa using (Eq.symm hclaim_j)
      _ =
          st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
              (honestRoundPoly st.domain (p := st.polynomial) (ch := r) j)) 0 := by
              simpa using hsum.symm
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
            (honestRoundPoly st.domain (p := st.polynomial) (ch := r) i) := honest_step
