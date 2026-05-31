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
  let E : Fin n → (Fin n → 𝔽) → Prop := fun i r =>
    AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r ∧
      RoundDisagreeButAgreeAtChallenge ⟨n, Nat.lt_succ_self n⟩ st P r i
  have hImp :
      ∀ r,
        AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P r →
          ∃ i, E i r := by
    intro r hAB
    rcases accepts_and_bad_implies_exists_round_disagree_but_agree
        (st := st) (P := P) (r := r) hAB with ⟨i, hi⟩
    exact ⟨i, hAB, hi⟩
  have hmono :=
    prob_over_challenges_mono
      (E := AcceptsAndBadTranscriptOnChallenges ⟨n, Nat.lt_succ_self n⟩ st P)
      (F := fun r => ∃ i, E i r)
      hImp
  have hunion :=
    prob_over_challenges_exists_le_sum (𝔽 := 𝔽) (n := n) E
  have hround := by
    simpa only [E, soundnessError] using
      sum_accepts_and_round_disagree_but_agree_bound (st := st) (P := P)
  exact le_trans (le_trans hmono hunion) hround

theorem addCasesFun_prefix_current_rest_eq_snoc {α : Type _} {n : ℕ}
(i : Fin n)
(challenges : Fin i.val → α)
(a : α)
(b : Fin (numOpenVars (n := n) i) → α)
(hsplit : i.val.succ + numOpenVars (n := n) i = n) :
  (fun j : Fin n =>
    addCasesFun challenges
      (fun t : Fin (numOpenVars (n := n) i + 1) => Fin.cases a b t)
      (Fin.cast (honest_split_eq (n := n) i).symm j))
    =
  (fun j : Fin n =>
    addCasesFun (Fin.snoc challenges a) b
      (Fin.cast hsplit.symm j)) := by
  funext j
  have h :=
    congrArg (fun f => f (Fin.cast hsplit.symm j))
      (Fin.append_left_snoc challenges a b)
  have hcast :
      Fin.cast (Nat.succ_add_eq_add_succ i.val (numOpenVars (n := n) i))
          (Fin.cast hsplit.symm j)
        =
      Fin.cast (honest_split_eq (n := n) i).symm j := by
    apply Fin.ext
    simp
  simpa [addCasesFun, Function.comp, hcast] using h.symm

theorem eval_lawful_c_univariate {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
(a c : 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
    (CPoly.Lawful.C (n := 1) (R := 𝔽) c) = c := by
  change CPoly.CMvPolynomial.eval₂ (R := 𝔽) (S := 𝔽) (n := 1)
      (RingHom.id 𝔽) (fun _ : Fin 1 => a)
      (CPoly.Lawful.C (n := 1) (R := 𝔽) c) = c
  exact CPoly.eval₂_Lawful_C
      (n := 1) (R := 𝔽) (S := 𝔽)
      (f := RingHom.id 𝔽)
      (vs := fun _ : Fin 1 => a)
      (c := c)

theorem honest_prover_message_at_nextClaim_eq_roundSum {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(domain : List 𝔽)
(p : CPoly.CMvPolynomial n 𝔽)
(i : Fin n)
(challenges : Fin i.val → 𝔽)
(a : 𝔽) :
  nextClaim (𝔽 := 𝔽) (roundChallenge := a)
    (honestProverMessageAt domain (𝔽 := 𝔽) (n := n) (p := p) (i := i) (challenges := challenges))
    =
  roundSum (𝔽 := 𝔽) domain challenges a p (Nat.succ_le_of_lt i.isLt) := by
  classical
  letI : BEq 𝔽 := instBEqOfDecidableEq
  letI : LawfulBEq 𝔽 := CPoly.lawfulBEqOfDecidableEq
  let openVars : ℕ := numOpenVars (n := n) i
  have hsplit : i.val.succ + openVars = n := by
    simpa [openVars, numOpenVars, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      honest_split_eq (n := n) i
  rw [nextClaim, honest_prover_message_at_def, roundSum, residual_sum_eq_with_openVars_def, residualSumWithOpenVars]
  have hmap :=
    sum_over_domain_recursive_map
      (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽) (γ := 𝔽)
      domain
      (addβ := fun a b =>
        @HAdd.hAdd
          (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
          instHAdd a b)
      (zeroβ := c1 (𝔽 := 𝔽) 0)
      (addγ := (· + ·))
      (zeroγ := 0)
      (g := fun q => CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) q)
      (hg := by
        intro x y
        simp)
      (hgz := by
        simp)
      (m := openVars)
      (F := fun b =>
        CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i challenges b) p)
  rw [hmap]
  apply sum_over_domain_recursive_congr
  intro b
  calc
    CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
        (CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i challenges b) p)
      =
        CPoly.CMvPolynomial.eval
          (fun j : Fin n =>
            CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
              (honestCombinedMap (𝔽 := 𝔽) (n := n) i challenges b j))
          p := by
            simpa using
              (CPoly.eval₂_eval₂Poly_c1
                (𝔽 := 𝔽) (n := n) (p := p)
                (vs := honestCombinedMap (𝔽 := 𝔽) (n := n) i challenges b)
                (b := a))
    _ = CPoly.CMvPolynomial.eval
          (fun j : Fin n =>
            addCasesFun challenges
              (fun t : Fin (openVars + 1) => Fin.cases a b t)
              (Fin.cast (honest_split_eq (n := n) i).symm j))
          p := by
            congr 1
            funext j
            cases h : (Fin.cast (honest_split_eq (n := n) i).symm j) using Fin.addCases with
            | left t =>
                rw [honest_combined_map_def, h, addCasesFun]
                simpa [Fin.addCases] using
                  (eval_lawful_c_univariate (𝔽 := 𝔽) (a := a) (c := challenges t))
            | right t =>
                simpa [honest_combined_map_def, addCasesFun, h] using
                  (eval_honest_right_map (𝔽 := 𝔽) (i := i) (a := a) (b := b) (t := t))
    _ = CPoly.CMvPolynomial.eval
          (fun j : Fin n =>
            addCasesFun (Fin.snoc challenges a) b
              (Fin.cast hsplit.symm j))
          p := by
            congr 1
            exact addCasesFun_prefix_current_rest_eq_snoc
              (i := i) (challenges := challenges) (a := a) (b := b) (hsplit := hsplit)

theorem honest_last_round_atK {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(k : Fin (n + 1))
(domain : List 𝔽)
(p : CPoly.CMvPolynomial n 𝔽)
(r : Fin k.val → 𝔽)
(i : Fin k.val)
(hlast : i.val.succ = k.val) :
  nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPolyAtK k domain p r i)
    =
  residualSum (𝔽 := 𝔽) domain r p (Nat.le_of_lt_succ k.isLt) := by
  classical
  let hk_le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  let iN : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩
  let pref : Fin i.val → 𝔽 := fun j => r ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  let r' : Fin i.val.succ → 𝔽 := fun u => r (Fin.cast hlast u)
  have hs_last : Fin.cast hlast (Fin.last i.val) = i := by
    apply Fin.ext
    simp [hlast]
  have hs_cast (j : Fin i.val) : Fin.cast hlast j.castSucc = ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
    apply Fin.ext
    simp [hlast]
  have hs : (Fin.snoc pref (r i) : Fin i.val.succ → 𝔽) = r' := by
    funext u
    cases u using Fin.lastCases with
    | last =>
        simp [r', hs_last]
    | cast j =>
        simp [pref, r', hs_cast]
  have hmain := honest_prover_message_at_nextClaim_eq_roundSum (domain := domain) (p := p) (i := iN) (challenges := pref) (a := r i)
  have hmain' :
      nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPolyAtK k domain p r i)
        = residualSum (𝔽 := 𝔽) domain r' p (Nat.succ_le_of_lt iN.isLt) := by
    simpa [honestRoundPolyAtK, roundSum, pref, iN, hs, r'] using hmain
  have hres : residualSum (𝔽 := 𝔽) domain r' p (Nat.succ_le_of_lt iN.isLt) = residualSum (𝔽 := 𝔽) domain r p hk_le := by
    rw [residual_sum_eq_with_openVars_def (𝔽 := 𝔽) (domain := domain) (ch := r') (p := p) (hk := Nat.succ_le_of_lt iN.isLt)]
    rw [residual_sum_eq_with_openVars_def (𝔽 := 𝔽) (domain := domain) (ch := r) (p := p) (hk := hk_le)]
    unfold residualSumWithOpenVars
    have hm : n - i.val.succ = n - k.val := by
      omega
    have hnL0 : i.val.succ + (n - i.val.succ) = n := by
      omega
    have hnMid : i.val.succ + (n - k.val) = n := by
      omega
    have hnR : k.val + (n - k.val) = n := by
      omega
    rw [sum_over_domain_recursive_cast (domain := domain) (add := (· + ·)) (zero := (0 : 𝔽)) hm]
    apply sum_over_domain_recursive_congr
    intro x
    change CPoly.CMvPolynomial.eval (fun j => Fin.append r' (x ∘ Fin.cast hm) (Fin.cast hnL0.symm j)) p =
      CPoly.CMvPolynomial.eval (fun j => Fin.append r x (Fin.cast hnR.symm j)) p
    congr 1
    funext j
    have h1 := congrArg (fun f => f (Fin.cast hnL0.symm j)) (Fin.append_cast_right r' x (n - i.val.succ) hm)
    have h1' :
        Fin.append r' (x ∘ Fin.cast hm) (Fin.cast hnL0.symm j)
          = Fin.append r' x (Fin.cast hnMid.symm j) := by
      simpa [Function.comp, hnL0, hnMid] using h1
    have h2 := congrArg (fun f => f (Fin.cast hnMid.symm j)) (Fin.append_cast_left r x i.val.succ hlast)
    exact h1'.trans h2
  exact hmain'.trans hres

theorem honest_step_round_atK {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(k : Fin (n + 1))
(domain : List 𝔽)
(p : CPoly.CMvPolynomial n 𝔽)
(r : Fin k.val → 𝔽)
(i : Fin k.val)
(hlt : i.val.succ < k.val) :
  let j : Fin k.val := ⟨i.val.succ, hlt⟩
  domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestRoundPolyAtK k domain p r j)) 0
    =
  nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPolyAtK k domain p r i) := by
  let hk_le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  let rExt : Fin n → 𝔽 := fun j => if h : j.val < k.val then r ⟨j.val, h⟩ else 0
  let iN : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩
  have hltN : iN.val.succ < n := lt_of_lt_of_le hlt hk_le
  let jK : Fin k.val := ⟨i.val.succ, hlt⟩
  let jN : Fin n := ⟨i.val.succ, hltN⟩
  have hi_eq : honestRoundPolyAtK k domain p r i = honestRoundPoly domain p rExt iN := by
    apply honestRoundPolyAtK_eq_honestRoundPoly_of_extend
    intro t
    simp only [rExt]
    split_ifs with h
    · rfl
    · exfalso
      exact h (lt_trans t.isLt i.isLt)
  have hj_eq : honestRoundPolyAtK k domain p r jK = honestRoundPoly domain p rExt jN := by
    apply honestRoundPolyAtK_eq_honestRoundPoly_of_extend
    intro t
    simp only [rExt]
    split_ifs with h
    · rfl
    · exfalso
      exact h (lt_trans t.isLt hlt)
  have hri : rExt iN = r i := by
    simp only [rExt, iN]
    split_ifs with h
    · rfl
    · exfalso
      exact h i.isLt
  simpa [jK, jN, hri, hi_eq, hj_eq] using honest_step_round domain p rExt iN hltN

theorem accepts_and_bad_implies_exists_round_disagree_but_agree_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(k : Fin (n + 1))
(st : SumcheckProtocolStatement 𝔽 n)
(P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
(r : Fin k.val → 𝔽) :
  AcceptsAndBadTranscriptOnChallenges k st P r →
    ∃ i : Fin k.val, RoundDisagreeButAgreeAtChallenge k st P r i := by
  classical
  intro h
  rcases h with ⟨hAcc, hBad⟩
  let t : Transcript 𝔽 k.val := proverTranscript k st P r

  have hLast : LastBadRound k st P r := by
    exact badTranscript_implies_lastBadRound_k k st P r (by simpa [t] using hBad)

  rcases hLast with ⟨i, hi_bad, hi_after⟩
  refine ⟨i, ?_⟩

  have hneq : t.roundPolys i ≠ honestRoundPolyAtK k st.domain st.polynomial r i := by
    simpa [t] using hi_bad

  by_cases hlast : i.val.succ = k.val
  · have hfinal :
        t.claims st.claim (Fin.last k.val) =
          residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := by
      exact decide_eq_true_eq.mp
        (acceptsEvent_final_ok_k k st.domain (p := st.polynomial) (claim := st.claim) (t := t) hAcc)

    have hlast_idx : (Fin.last k.val : Fin (k.val + 1)) = i.succ := by
      apply Fin.ext
      simpa [Nat.succ_eq_add_one] using hlast.symm

    have hclaim_last :
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := by
      have hround_i :
          t.claims st.claim i.succ =
            nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
        simpa [t] using
          (acceptsEvent_round_facts_k k st.domain (p := st.polynomial) (claim := st.claim) (t := t) (i := i) hAcc).2
      calc
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
            = t.claims st.claim i.succ := by simpa using hround_i.symm
        _ = t.claims st.claim (Fin.last k.val) := by rw [hlast_idx]
        _ = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := hfinal

    have honest_last :
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
          (honestRoundPolyAtK k st.domain st.polynomial r i)
          = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := by
      exact honest_last_round_atK k st.domain st.polynomial r i hlast

    refine ⟨hneq, ?_⟩
    calc
      nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          = residualSum (𝔽 := 𝔽) st.domain r st.polynomial (Nat.le_of_lt_succ k.isLt) := hclaim_last
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
            (honestRoundPolyAtK k st.domain st.polynomial r i) := by
              simpa using honest_last.symm

  · have hlt : i.val.succ < k.val := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    let j : Fin k.val := ⟨i.val.succ, hlt⟩

    have hj_honest : t.roundPolys j = honestRoundPolyAtK k st.domain st.polynomial r j := by
      have hij : i < j := by
        exact Fin.lt_def.mpr (Nat.lt_succ_self i.val)
      simpa [t, j] using hi_after j hij

    have hsum :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPolyAtK k st.domain st.polynomial r j)) 0
          =
        t.claims st.claim (Fin.castSucc j) := by
      exact acceptsEvent_domain_sum_eq_claim_of_honest_k k st.domain
        (p := st.polynomial) (claim := st.claim) (r := r) (t := t) (i := j) (hi := hj_honest) hAcc

    have hcast : (Fin.castSucc j) = i.succ := by
      apply Fin.ext
      simp [j, Nat.succ_eq_add_one]

    have hclaim_i_succ :
        t.claims st.claim i.succ =
          nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
      simpa [t] using
        (acceptsEvent_round_facts_k k st.domain (p := st.polynomial) (claim := st.claim) (t := t) (i := i) hAcc).2

    have hclaim_j :
        t.claims st.claim (Fin.castSucc j) =
          nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i) := by
      simpa [hcast] using hclaim_i_succ

    have honest_step :
        st.domain.foldl (fun acc a =>
          acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
            (honestRoundPolyAtK k st.domain st.polynomial r j)) 0
          =
        nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
          (honestRoundPolyAtK k st.domain st.polynomial r i) := by
      simpa [j] using (honest_step_round_atK k st.domain st.polynomial r i hlt)

    refine ⟨hneq, ?_⟩
    calc
      nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
          = t.claims st.claim (Fin.castSucc j) := by
              simpa using (Eq.symm hclaim_j)
      _ = st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
              (honestRoundPolyAtK k st.domain st.polynomial r j)) 0 := by
              simpa using hsum.symm
      _ = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
            (honestRoundPolyAtK k st.domain st.polynomial r i) := honest_step

theorem soundness_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k)) :
     probOverChallenges (E := AcceptsAndBadTranscriptOnChallenges k st P)
      ≤ soundnessErrorK k st.polynomial := by
  classical
  let E : Fin k.val → (Fin k.val → 𝔽) → Prop := fun i r =>
    AcceptsAndBadTranscriptOnChallenges k st P r ∧
      RoundDisagreeButAgreeAtChallenge k st P r i
  have hImp : ∀ r, AcceptsAndBadTranscriptOnChallenges k st P r → ∃ i, E i r := by
    intro r hr
    rcases accepts_and_bad_implies_exists_round_disagree_but_agree_k k st P r hr with ⟨i, hi⟩
    exact ⟨i, hr, hi⟩
  have hmono := prob_over_challenges_mono
    (E := AcceptsAndBadTranscriptOnChallenges k st P)
    (F := fun r => ∃ i, E i r) hImp
  have hunion := prob_over_challenges_exists_le_sum (𝔽 := 𝔽) (n := k.val) E
  have hround := sum_accepts_and_round_disagree_but_agree_bound_k (k := k) (st := st) (P := P)
  simpa only [E, soundnessErrorK] using le_trans (le_trans hmono hunion) hround



theorem all_rounds_honest_of_not_bad_k_aux {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 k.val)
  (domain : List 𝔽)
  (hNoBad : ¬ BadTranscriptEvent k domain p t) :
  ∀ i : Fin k.val,
    t.roundPolys i = honestRoundPolyAtK k domain p t.challenges i := by
  intro i
  by_contra hneq
  apply hNoBad
  refine ⟨i, ?_⟩
  simpa [BadRound] using hneq

theorem honest_round0_atK_domain_sum_eq_honest_claim_aux {𝔽 : Type _} {n' : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (Nat.succ n' + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial (Nat.succ n') 𝔽)
  (r : Fin k.val → 𝔽)
  (hkpos : 0 < k.val) :
  let i0 : Fin k.val := ⟨0, hkpos⟩
  domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestRoundPolyAtK k domain p r i0)) 0
    = honestClaim domain (p := p) := by
  dsimp
  let rExt : Fin (Nat.succ n') → 𝔽 := fun _ => 0
  have hbridge :
      honestRoundPolyAtK k domain p r ⟨0, hkpos⟩ =
        honestRoundPoly domain p rExt ⟨0, Nat.succ_pos n'⟩ := by
    apply honestRoundPolyAtK_eq_honestRoundPoly_of_extend
    intro j
    exact Fin.elim0 j
  rw [hbridge]
  simpa [rExt] using honest_round0_domain_sum_eq_honest_claim (domain := domain) (p := p) (r := rExt)

theorem claim_eq_honest_claim_of_accepts_and_all_rounds_honest_k_aux {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽)
  (hall :
    ∀ i : Fin k.val,
      (proverTranscript k st P r).roundPolys i
        = honestRoundPolyAtK k st.domain st.polynomial r i)
  (hAcc : AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st P r)) :
  st.claim = honestClaim st.domain (p := st.polynomial) := by
  classical
  let t : Transcript 𝔽 k.val := proverTranscript k st P r
  cases hk : k.val with
  | zero =>
      have hk0 : k = 0 := by
        apply Fin.ext
        simp [hk]
      subst hk0
      have hfinal :
          t.claims st.claim (Fin.last 0) =
            residualSum (𝔽 := 𝔽) st.domain t.challenges st.polynomial (Nat.zero_le n) := by
        exact decide_eq_true_eq.mp
          (acceptsEvent_final_ok_k (k := 0) st.domain (p := st.polynomial) (claim := st.claim) (t := t) hAcc)
      have hclaim0 : t.claims st.claim (Fin.last 0) = st.claim := by
        simpa [Transcript.claims] using
          (generate_honest_claims_zero st.claim t.roundPolys t.challenges)
      have hchal0 : t.challenges = (fun i : Fin 0 => i.elim0) := by
        funext i
        exact i.elim0
      have hhonest0 :
          residualSum (𝔽 := 𝔽) st.domain t.challenges st.polynomial (Nat.zero_le n)
            = honestClaim st.domain (p := st.polynomial) := by
        simpa [honestClaim, hchal0]
      calc
        st.claim = t.claims st.claim (Fin.last 0) := by simpa using hclaim0.symm
        _ = residualSum (𝔽 := 𝔽) st.domain t.challenges st.polynomial (Nat.zero_le n) := hfinal
        _ = honestClaim st.domain (p := st.polynomial) := hhonest0
  | succ m =>
      have hkpos : 0 < k.val := by
        simpa [hk]
      let i0 : Fin k.val := ⟨0, hkpos⟩
      have hsum0 :
          st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0
          =
          t.claims st.claim (Fin.castSucc i0) := by
        exact acceptsEvent_domain_sum_eq_claim_k k st.domain (p := st.polynomial) (claim := st.claim) (t := t) (i := i0) hAcc
      have hi0 : t.roundPolys i0 = honestRoundPolyAtK k st.domain st.polynomial r i0 := by
        simpa [t] using hall i0
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
        st.claim = t.claims st.claim (Fin.castSucc i0) := by simpa using hclaim0.symm
        _ = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0 := by
              symm
              exact hsum0
        _ = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
                (honestRoundPolyAtK k st.domain st.polynomial r i0)) 0 := by
              simp [hi0]
        _ = honestClaim st.domain (p := st.polynomial) := htrue

theorem accepts_on_challenges_dishonest_implies_bad_k_aux {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽)
  (hDish : st.claim ≠ honestClaim st.domain (p := st.polynomial))
  (hAcc : AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st P r)) :
  BadTranscriptEvent k st.domain st.polynomial (proverTranscript k st P r) := by
  classical
  let t := proverTranscript k st P r
  by_contra hNoBad
  have hall :
      ∀ i : Fin k.val,
        t.roundPolys i = honestRoundPolyAtK k st.domain st.polynomial t.challenges i :=
    all_rounds_honest_of_not_bad_k_aux k st.polynomial t st.domain hNoBad
  have hall' :
      ∀ i : Fin k.val,
        (proverTranscript k st P r).roundPolys i = honestRoundPolyAtK k st.domain st.polynomial r i := by
    intro i
    simpa [t] using hall i
  have hEq : st.claim = honestClaim st.domain (p := st.polynomial) :=
    claim_eq_honest_claim_of_accepts_and_all_rounds_honest_k_aux k st P r hall' hAcc
  exact hDish hEq

theorem soundness_dishonest_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (h : st.claim ≠ honestClaim st.domain (p := st.polynomial)) :
  probOverChallenges (E := AcceptsOnChallenges k st P)
    ≤ soundnessErrorK k st.polynomial := by
  let hImp : ∀ r, AcceptsOnChallenges k st P r → AcceptsAndBadTranscriptOnChallenges k st P r := by
    intro r hAcc
    refine ⟨?_, ?_⟩
    · simpa [AcceptsOnChallenges, AcceptsAndBadTranscriptOnChallenges] using hAcc
    ·
      have hAcc' : AcceptsEvent k st.domain st.polynomial st.claim (proverTranscript k st P r) := by
        simpa [AcceptsOnChallenges] using hAcc
      exact accepts_on_challenges_dishonest_implies_bad_k_aux k st P r h hAcc'
  have hMono :
      probOverChallenges (E := AcceptsOnChallenges k st P) ≤
        probOverChallenges (E := AcceptsAndBadTranscriptOnChallenges k st P) := by
    exact prob_over_challenges_mono hImp
  exact le_trans hMono (soundness_k k st P)


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
