import SumcheckProtocol.Properties.Probability.Challenges
import SumcheckProtocol.Properties.Lemmas.HonestRoundProofs
import SumcheckProtocol.Properties.Lemmas.Degree
import SumcheckProtocol.Properties.Lemmas.Accepts
import SumcheckProtocol.Properties.Lemmas.SoundnessLemmas

import SumcheckProtocol.Properties.Theorems.Soundness
theorem honest_partial_transcript_final_claim_eq_residual_k {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (hclaim : st.claim = honestClaim st.domain st.polynomial)
  (r : Fin k.val → 𝔽) :
  (proverTranscript k st (sumcheckHonestProver k) r).claims st.claim (Fin.last k.val)
    =
  residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := by
  classical
  let t : Transcript 𝔽 k.val := proverTranscript k st (sumcheckHonestProver k) r
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := by
      apply Fin.ext
      simpa using hk
    subst hk0
    have hclaim0 : t.claims st.claim (Fin.last 0) = st.claim := by
      simpa [Transcript.claims] using
        (generate_honest_claims_zero st.claim t.roundPolys t.challenges)
    have hchal0 : r = (fun i : Fin 0 => i.elim0) := by
      funext i
      exact i.elim0
    have hhonest0 :
        residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.zero_le n)
          = honestClaim st.domain (p := st.polynomial) := by
      simpa [honestClaim, hchal0]
    calc
      t.claims st.claim (Fin.last 0) = st.claim := hclaim0
      _ = honestClaim st.domain (p := st.polynomial) := hclaim
      _ = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.zero_le n) := by
            simpa using hhonest0.symm
  · obtain ⟨m, hk' : k.val = m + 1⟩ := Nat.exists_eq_succ_of_ne_zero hk
    let iLast : Fin k.val := ⟨m, by simpa [hk']⟩
    have hlast : iLast.val.succ = k.val := by
      simp [iLast, hk']
    have hlast_idx : (Fin.last k.val : Fin (k.val + 1)) = iLast.succ := by
      apply Fin.ext
      simpa [Nat.succ_eq_add_one] using hlast.symm
    have hclaims :
        t.claims st.claim iLast.succ =
          nextClaim (𝔽 := 𝔽) (roundChallenge := r iLast) (t.roundPolys iLast) := by
      simp [t, Transcript.claims, generateHonestClaims, iLast, hk']
    have hsubset :
        challengeSubset r iLast = fun j : Fin iLast.val => r ⟨j.val, Nat.lt_trans j.isLt iLast.isLt⟩ := by
      funext j
      simp [challengeSubset]
    have hround :
        t.roundPolys iLast = honestRoundPolyAtK k st.domain st.polynomial r iLast := by
      simpa [t, proverTranscript, sumcheckHonestProver, honestRoundPolyAtK, hsubset]
    calc
      t.claims st.claim (Fin.last k.val) = t.claims st.claim iLast.succ := by rw [hlast_idx]
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r iLast) (t.roundPolys iLast) := hclaims
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r iLast)
            (honestRoundPolyAtK k st.domain st.polynomial r iLast) := by rw [hround]
      _ = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) :=
            honest_last_round_atK k st.domain st.polynomial r iLast hlast

theorem honest_partial_transcript_sum_identity_k {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (hclaim : st.claim = honestClaim st.domain st.polynomial)
  (r : Fin k.val → 𝔽)
  (i : Fin k.val) :
  st.domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      ((proverTranscript k st (sumcheckHonestProver k) r).roundPolys i)) 0
    =
  (proverTranscript k st (sumcheckHonestProver k) r).claims st.claim (Fin.castSucc i) := by
  let t := proverTranscript k st (sumcheckHonestProver k) r
  have hround :
      ∀ j : Fin k.val,
        t.roundPolys j = honestRoundPolyAtK k st.domain st.polynomial r j := by
    intro j
    rfl
  cases' hi : i.val with m
  · have hkpos : 0 < k.val := by
      simpa [hi] using i.isLt
    let i0 : Fin k.val := ⟨0, hkpos⟩
    have hi_eq : i = i0 := by
      apply Fin.ext
      simp [i0, hi]
    subst hi_eq
    have hcast0 : Fin.castSucc i0 = 0 := by
      apply Fin.ext
      simp [i0]
    have hclaim0 : t.claims st.claim (Fin.castSucc i0) = st.claim := by
      rw [hcast0]
      simpa [Transcript.claims] using
        (generate_honest_claims_zero st.claim t.roundPolys t.challenges)
    have hn_pos : 0 < n := by
      omega
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = Nat.succ n' :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)
    subst hn'
    have htrue :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPolyAtK k st.domain st.polynomial r i0)) 0
        = honestClaim st.domain (p := st.polynomial) := by
      simpa [i0] using
        (honest_round0_atK_domain_sum_eq_honest_claim_aux (k := k) (domain := st.domain)
          (p := st.polynomial) (r := r) hkpos)
    calc
      st.domain.foldl (fun acc a =>
        acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0
          = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
                (honestRoundPolyAtK k st.domain st.polynomial r i0)) 0 := by
              rw [hround i0]
      _ = honestClaim st.domain (p := st.polynomial) := htrue
      _ = st.claim := by simpa using hclaim.symm
      _ = t.claims st.claim (Fin.castSucc i0) := by simpa using hclaim0.symm
  · have hi_val : i.val = m + 1 := by
      simp [hi]
    have hk1_lt : m + 1 < k.val := by
      simpa [hi] using i.isLt
    have hm_lt : m < k.val := by
      omega
    let prev : Fin k.val := ⟨m, hm_lt⟩
    let j : Fin k.val := ⟨m + 1, hk1_lt⟩
    have hi_eq : i = j := by
      apply Fin.ext
      simp [j, hi_val]
    subst hi_eq
    have hstep :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPolyAtK k st.domain st.polynomial r j)) 0
        =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r prev)
          (honestRoundPolyAtK k st.domain st.polynomial r prev) := by
      simpa [j, prev] using
        (honest_step_round_atK k st.domain st.polynomial r prev hk1_lt)
    have hclaimj :
        t.claims st.claim (Fin.castSucc j)
          = nextClaim (𝔽 := 𝔽) (roundChallenge := r prev) (t.roundPolys prev) := by
      simp [t, Transcript.claims, generateHonestClaims, prev, j]
    calc
      st.domain.foldl (fun acc a =>
        acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys j)) 0
          = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
                (honestRoundPolyAtK k st.domain st.polynomial r j)) 0 := by
              rw [hround j]
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r prev)
            (honestRoundPolyAtK k st.domain st.polynomial r prev) := hstep
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r prev) (t.roundPolys prev) := by
            rw [hround prev]
      _ = t.claims st.claim (Fin.castSucc j) := by
            simpa using hclaimj.symm

theorem honest_accepts_on_challenges_k {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (hclaim : st.claim = honestClaim st.domain st.polynomial)
  (r : Fin k.val → 𝔽) :
  AcceptsOnChallenges k st (sumcheckHonestProver k) r := by
  classical
  rw [AcceptsOnChallenges_unfold]
  unfold AcceptsEvent isVerifierAccepts
  simp only [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro i hi
    simp only [Bool.and_eq_true]
    constructor
    · unfold verifierCheck
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact honest_partial_transcript_sum_identity_k k st hclaim r i
      · simpa [proverTranscript, sumcheckHonestProver] using
          (honest_round_poly_atK_degree_le_ind_degree_k k st.domain st.polynomial r i)
    · apply decide_eq_true_eq.mpr
      have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
      simp [proverTranscript, Transcript.claims, generateHonestClaims, hsuc]
  · apply decide_eq_true_eq.mpr
    exact honest_partial_transcript_final_claim_eq_residual_k k st hclaim r

theorem perfect_completeness_k {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (hclaim : st.claim = honestClaim st.domain st.polynomial) :
  probOverChallenges (E := AcceptsOnChallenges k st (sumcheckHonestProver k))
    = 1 := by
  classical
  have hE : ∀ r : Fin k.val → 𝔽, AcceptsOnChallenges k st (sumcheckHonestProver k) r := by
    intro r
    exact honest_accepts_on_challenges_k k st hclaim r
  have hE' : ∀ r : Fin k.val → 𝔽,
      AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st (sumcheckHonestProver k) r) := by
    intro r
    exact (AcceptsOnChallenges_unfold k st (sumcheckHonestProver k) r).mp (hE r)
  have hfilter :
      (Finset.univ.filter (fun r : Fin k.val → 𝔽 =>
        AcceptsOnChallenges k st (sumcheckHonestProver k) r) : Finset (Fin k.val → 𝔽))
        = Finset.univ := by
    ext r
    simp [AcceptsOnChallenges_unfold, hE' r]
  simp [probOverChallenges, probEvent, allChallenges, hfilter]


-- Prob verifier accepts when all round polys are honest (and claim is honest) is one
theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) :
  probOverChallenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsEvent (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩
        domain p (honestClaim domain p)
        (generateHonestTranscript (𝔽 := 𝔽) (n := n) domain p (honestClaim domain p) r))
  = 1 := by
  classical
  -- the honest transcript is accepted for every challenge tuple.

  -- First, prove every honest transcript is accepted
  have hE : ∀ r : Fin n → 𝔽,
      AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p (honestClaim domain p) (generateHonestTranscript domain p (honestClaim domain p) r) := by
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
      (Finset.univ.filter (fun r => AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p (honestClaim domain p) (generateHonestTranscript domain p (honestClaim domain p) r)) : Finset (Fin n → 𝔽))
        = Finset.univ := by
    ext r
    simp [hE r]

  simp [probEvent, allChallenges, hfilter]
