import SumcheckProtocol.Properties.Lemmas.SoundnessLemmas

/-- **Round-by-round soundness (partial-run).** For any partial-run prover
stopping at `k`, any round `i : Fin k.val`, the probability that the
transcript accepts AND round-`i` disagrees-but-agrees-at-challenge is
bounded by `maxIndDegree(p) / |𝔽|`. The bound is `k`-independent —
useful for GKR/batched-sumcheck composition where per-round bounds compose. -/
theorem soundness_per_round {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (i : Fin k.val) :
    probOverChallenges (𝔽 := 𝔽) (n := k.val)
      (fun r =>
        AcceptsAndBadTranscriptOnChallenges k st P r ∧
        RoundDisagreeButAgreeAtChallenge k st P r i)
      ≤ (maxIndDegree st.polynomial) / fieldSize (𝔽 := 𝔽) :=
  prob_single_round_accepts_and_disagree_le_k (𝔽 := 𝔽) (n := n) k st P i

-- Prob verifier accepts transcript when at least one round poly differs from honest one
theorem soundness {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩)) :
     probOverChallenges (E := AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P)
      ≤ soundnessError st.polynomial := by
  classical

  -- Keep AcceptsAndBad in the per-round event.
  let E : Fin n → (Fin n → 𝔽) → Prop :=
    fun i r =>
      AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r ∧
        RoundDisagreeButAgreeAtChallenge ⟨n, Nat.lt_succ_self n⟩ st P r i

  -- Step 1: Accepts∧Bad implies ∃ i, (Accepts∧Bad ∧ RoundDisagreeButAgreeAtChallenge i).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r →
          ∃ i : Fin n, E i r := by
    intro r hAB
    rcases
      accepts_and_bad_implies_exists_round_disagree_but_agree
        (st := st) (P := P) (r := r) hAB
      with ⟨i, hi⟩
    exact ⟨i, ⟨hAB, hi⟩⟩

  have hmono :
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r)
        ≤
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, E i r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Step 2: union bound over i.
  have hunion :
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => ∃ i : Fin n, E i r)
        ≤
      (∑ i : Fin n,
        probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => E i r)) :=
    prob_over_challenges_exists_le_sum (𝔽 := 𝔽) (n := n) E

  -- Step 3: use the (now-lemma) sumcheck-specific bound.
  have hround :
      (∑ i : Fin n,
        probOverChallenges (𝔽 := 𝔽) (n := n) (fun r => E i r))
      ≤ soundnessError st.polynomial := by
    simpa [E, soundnessError] using
      sum_accepts_and_round_disagree_but_agree_bound
        (st := st) (P := P)

  exact le_trans (le_trans hmono hunion) hround

-- Prob verifier accepts transcript when claim is not honest claim
theorem soundness_dishonest {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩))
  (h : st.claim ≠ honestClaim st.domain (p := st.polynomial)) :
  probOverChallenges (E := AcceptsOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P)
    ≤ soundnessError st.polynomial := by
  classical

  -- Key reduction: dishonest claim ⇒ (accept → bad), hence accept ⊆ (accept ∧ bad).
  have hImp :
      ∀ r : (Fin n → 𝔽),
        AcceptsOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r →
          AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r := by
    intro r hAcc
    refine ⟨?hAccEvent, ?hBad⟩
    · -- acceptance part
      simpa [AcceptsOnChallenges, AcceptsAndBadTranscriptOnChallenges]
        using hAcc
    · -- badness part
      exact
        accepts_on_challenges_dishonest_implies_bad
          (st := st) (P := P) (r := r) h hAcc

  have hmono :
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r)
        ≤
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r) :=
    prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp

  -- Now just reuse your existing soundness_accept_bad_transcript theorem.
  have hsound :
      probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r => AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r)
        ≤ soundnessError st.polynomial :=
    soundness (𝔽 := 𝔽) (n := n) (st := st) (P := P)

  exact le_trans hmono hsound
