import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Src.Verifier
import SumcheckProtocol.Properties.Lemmas.HonestProver
import SumcheckProtocol.Properties.Lemmas.Hypercube
import SumcheckProtocol.Properties.Lemmas.Eval
import SumcheckProtocol.Properties.Lemmas.Nat
import SumcheckProtocol.Properties.Lemmas.Fin

theorem eval_honest_round_poly_eq_sum_eval {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) (a : 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestRoundPoly domain (p := p) (ch := r) i)
    =
  sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
    domain (· + ·) 0
    (m := numOpenVars (n := n) i)
    (fun x =>
      CPoly.CMvPolynomial.eval
        (fun k : Fin n =>
          addCasesFun
            (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
            (fun t : Fin (numOpenVars (n := n) i + 1) => Fin.cases a x t)
            (Fin.cast (honestSplitEqCast (n := n) i (numOpenVars (n := n) i) rfl).symm k))
        p) := by
  classical
  unfold honestRoundPoly
  -- After unfolding, the goal becomes:
  -- eval₂ (RingHom.id 𝔽) (fun _ => a) (honestProverMessageAt domain ...)
  --   = sumOverDomainRecursive domain (·+·) 0 (m := ...) (fun x => eval (...) p)
  -- honestProverMessageAt is sumOverDomainRecursive domain (fun a b => @HAdd.hAdd ... a b) 0 (m := ...) (fun b => eval₂Poly c1 ...)
  -- We need to push eval₂ through sumOverDomainRecursive using sum_over_domain_recursive_map

  -- First, use the map lemma to push eval₂ through
  rw [show honestProverMessageAt domain (𝔽 := 𝔽) (p := p) (i := i)
       (challenges := challengeSubset r i)
     = sumOverDomainRecursive domain
         (fun a b => @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
           instHAdd a b)
         0
         (m := numOpenVars (n := n) i)
         (fun b => CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b) p)
     from by simp [honestProverMessageAt]]

  have hmap := sum_over_domain_recursive_map
    (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽) (γ := 𝔽)
    domain
    (addβ := fun a b => @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
      instHAdd a b)
    (zeroβ := 0)
    (addγ := (· + ·))
    (zeroγ := 0)
    (g := fun q => CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) q)
    (hg := by intro x y; simp)
    (hgz := by simp)
    (m := numOpenVars (n := n) i)
    (F := fun b => CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b) p)
  rw [hmap]
  apply sum_over_domain_recursive_congr
  intro x
  simp [CPoly.eval₂_eval₂Poly_c1, eval_honest_combined_map_eq_addCasesFun]


theorem num_open_vars_succ {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) :
    numOpenVars (n := n) i
      = numOpenVars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1 := by
  have hNat : n - (i.val + 1) = 1 + (n - (i.val + 2)) := nat_sub_add_two n i.val hlt
  simpa [numOpenVars, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNat

theorem honest_step_round {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlt : i.val.succ < n) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestRoundPoly domain (p := p) (ch := r) j)) 0
    =
    nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (honestRoundPoly domain (p := p) (ch := r) i) := by
  classical
  simp [nextClaim]
  set j : Fin n := ⟨i.val.succ, hlt⟩ with hj

  -- Rewrite each eval₂ using the sum-expansion lemma
  have hr :=
    eval_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) domain (p := p) (r := r) (i := i) (a := r i)
  rw [hr]

  set openI : ℕ := numOpenVars (n := n) i
  set openJ : ℕ := numOpenVars (n := n) j

  have hm : openI = openJ + 1 := by
    simpa [openI, openJ, hj] using (num_open_vars_succ (n := n) i hlt)

  -- The RHS is sumOverDomainRecursive domain (·+·) 0 (m := openI) Fi
  -- = domain.foldl (\acc a => acc + sumOverDomainRecursive domain (·+·) 0 (m := openJ) (Fi ∘ cons a)) 0
  -- by the succ unfolding.
  -- The LHS folds eval₂(a)(honestRoundPoly domain j) over domain, and each
  -- eval₂(a)(honestRoundPoly domain j) = sumOverDomainRecursive domain (·+·) 0 (m := openJ) (Fj_a).
  -- We show these are pointwise equal.

  let Fi : (Fin openI → 𝔽) → 𝔽 := fun x =>
    CPoly.CMvPolynomial.eval
      (fun k : Fin n =>
        addCasesFun
          (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
          (fun t : Fin (openI + 1) => Fin.cases (r i) x t)
          (Fin.cast (honest_split_eq (n := n) i).symm k))
      p

  -- Expand the RHS using sum_over_domain_recursive_succ_of_hopen
  have hsplit :=
    sum_over_domain_recursive_succ_of_hopen (𝔽 := 𝔽) (β := 𝔽)
      domain (add := (· + ·)) (zero := 0)
      (m := openJ) (m' := openI) hm
      (F := fun x => Fi x)
  rw [hsplit]

  -- Now both sides are domain.foldl (...) 0
  -- We need to show the accumulators match pointwise
  have hm1 : openJ + 1 + 1 = openI + 1 := by
    simp [hm, Nat.add_assoc]

  -- For each a in domain, show the inner values match
  congr 1
  funext acc a

  -- The LHS accumulator is: acc + eval₂(a)(honestRoundPoly domain j)
  -- The RHS accumulator is: acc + sumOverDomainRecursive domain (·+·) 0 (m := openJ) (Fi ∘ cons a ∘ cast hm)
  -- We need: eval₂(a)(honestRoundPoly domain j) = sumOverDomainRecursive ... (Fi ∘ cons a ∘ cast hm)

  have heval_a :=
    eval_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) domain (p := p) (r := r) (i := j) (a := a)

  rw [heval_a]
  congr 1
  apply sum_over_domain_recursive_congr

  -- Now show the two functions over (Fin openJ → 𝔽) are equal
  intro x

  let Fja : (Fin openJ → 𝔽) → 𝔽 := fun x =>
    CPoly.CMvPolynomial.eval
      (fun k : Fin n =>
        addCasesFun
          (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
          (fun t : Fin (openJ + 1) => Fin.cases a x t)
          (Fin.cast (honest_split_eq (n := n) j).symm k))
      p

  change Fja x = Fi ((Fin.cons a x) ∘ Fin.cast hm)

  unfold Fi Fja
  have hpoint :
      (fun k : Fin n =>
          addCasesFun
            (fun t : Fin j.val => r ⟨t.val, Nat.lt_trans t.isLt j.isLt⟩)
            (fun t : Fin (openJ + 1) => Fin.cases a x t)
            (Fin.cast (honest_split_eq (n := n) j).symm k))
        =
      (fun k : Fin n =>
          addCasesFun
            (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
            (fun t : Fin (openI + 1) =>
              Fin.cases (r i) ((Fin.cons a x) ∘ Fin.cast hm) t)
            (Fin.cast (honest_split_eq (n := n) i).symm k)) := by
    funext k
    cases hk : (Fin.cast (honest_split_eq (n := n) j).symm k) using Fin.addCases with
    | left t =>
        cases t using Fin.lastCases with
        | last =>
            have hi :
                Fin.cast (honest_split_eq (n := n) i).symm k
                  =
                Fin.natAdd i.val (0 : Fin (numOpenVars (n := n) i + 1)) := by
              apply cast_split_eq_succ_last (n := n) i hlt k
              simpa [hj] using hk
            simp [addCasesFun, hi, openI, openJ]
        | cast t0 =>
            have hi :
                Fin.cast (honest_split_eq (n := n) i).symm k
                  =
                Fin.castAdd (numOpenVars (n := n) i + 1) t0 := by
              apply cast_split_eq_succ_castSucc (n := n) i hlt k t0
              simpa [hj] using hk
            simp [addCasesFun, hi, openI, openJ]
    | right t =>
        have hi :
            Fin.cast (honest_split_eq (n := n) i).symm k
              =
            Fin.natAdd i.val (Fin.cast hm1 (Fin.succ t)) := by
          apply
            cast_split_eq_succ_right (n := n) i hlt k t
              (hm1 := by
                simpa [openI, openJ] using hm1)
          simpa [hj] using hk
        simp [addCasesFun, hi, openI, openJ, Fin.cons, Fin.cases]

  simpa [addCasesFun] using congrArg (fun f => CPoly.CMvPolynomial.eval f p) hpoint

lemma honest_last_round
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽] [Fintype 𝔽]
  [BEq 𝔽] [LawfulBEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
  (hlast : i.val.succ = n) :
  nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
      (honestRoundPoly domain (p := p) (ch := r) i)
    =
  CPoly.CMvPolynomial.eval r p := by
  classical

  have hi : i.val + 1 = n := by
    simpa [Nat.succ_eq_add_one] using hlast

  have hopen : numOpenVars (n := n) i = 0 := by
    simp [numOpenVars, hi]

  -- define b0 at the dependent type via simp [hopen]
  let b0 : Fin (numOpenVars (n := n) i) → 𝔽 :=
    emptyOpenAssignment (𝔽 := 𝔽) (n := n) i hopen

  -- last round => honestRoundPoly is just F applied to the empty assignment
  have hround :
      honestRoundPoly domain (p := p) (ch := r) i
        =
      CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
        (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0)
        p := by
    -- unfold honestRoundPoly to honestProverMessageAt, then to domain sum
    change honestProverMessageAt domain p i (challengeSubset r i)
      = CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0) p
    rw [honest_prover_message_at_def]
    -- since numOpenVars = 0, the domain sum collapses to F(empty)
    have hcollapse :=
      sum_over_domain_recursive_eq_of_m_eq_zero
        (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽) domain
        (fun a b => a + b) (c1 (𝔽 := 𝔽) 0)
        (m := numOpenVars (n := n) i)
        (F := fun b => CPoly.eval₂Poly c1
          (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b) p)
        hopen
    rw [hcollapse]
    congr 1; congr 1; funext j; exact Fin.elim0 (hopen ▸ j)

  -- expand nextClaim, rewrite by hround
  have hnc :
      nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
          (honestRoundPoly domain (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0) p) := by
    simp [nextClaim, hround]

  have heval :
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0) p)
        =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
            (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0 j))
        p := by
    simpa using
      (CPoly.eval₂_eval₂Poly_c1 (𝔽 := 𝔽) (n := n) (p := p)
        (vs := honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0)
        (b := r i))

  have hpt :
      (fun j =>
        CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
          (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0 j))
      =
      r := by
    funext j
    by_cases hj : j = i
    · subst hj
      have hcm :
          honestCombinedMap (𝔽 := 𝔽) (n := n) j (challengeSubset r j) b0 j = x0 := by
        simpa using
          (honest_combined_map_at_i_is_x0 (𝔽 := 𝔽) (n := n)
            (i := j) (challenges := challengeSubset r j) (b := b0))
      simpa [hcm, x0] using (CPoly.eval_x0 (𝔽 := 𝔽) (b := r j))
    ·
      have hjlt_succ : j.val < i.val.succ := by
        exact (hlast.symm ▸ j.isLt)
      have hjle : j.val ≤ i.val := Nat.le_of_lt_succ hjlt_succ
      have hne : j.val ≠ i.val := by
        intro hEq
        apply hj
        ext
        exact hEq
      have hjlt : j.val < i.val := Nat.lt_of_le_of_ne hjle hne
      let t : Fin i.val := ⟨j.val, hjlt⟩
      let j' : Fin n :=
        Fin.cast (honest_split_eq (n := n) i)
          (Fin.castAdd (numOpenVars (n := n) i + 1) t)
      have hj' : j' = j := by
        ext
        simp [j', t]
      have hmap' :
          honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0 j'
            =
          c1 (challengeSubset r i t) := by
        simpa [j'] using
          (honest_combined_map_left (𝔽 := 𝔽) (n := n)
            (i := i) (challenges := challengeSubset r i) (b := b0) (t := t))
      have hmap :
          honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0 j
            =
          c1 (challengeSubset r i t) := by
        simpa [hj'] using hmap'
      have htj :
          (⟨t.val, Nat.lt_trans t.isLt i.isLt⟩ : Fin n) = j := by
        ext
        rfl
      simp [hmap, challengeSubset, htj, c1]
      show CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i) (CPoly.CMvPolynomial.C _) = _
      exact CPoly.eval_C _ _

  -- final assembly
  calc
    nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
        (honestRoundPoly domain (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
        (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
          (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0) p) := by
          exact hnc
    _ =
      CPoly.CMvPolynomial.eval
        (fun j =>
          CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r i)
            (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b0 j))
        p := by
          exact heval
    _ =
      CPoly.CMvPolynomial.eval r p := by
          simp [hpt]

-- ============================================================================
-- honest_round0_domain_sum_eq_honest_claim
-- ============================================================================

lemma honest_round0_domain_sum_eq_honest_claim
  {𝔽 : Type _} {n' : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial (Nat.succ n') 𝔽)
  (r : Fin (Nat.succ n') → 𝔽) :
  let i0 : Fin (Nat.succ n') := ⟨0, Nat.succ_pos n'⟩
  domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestRoundPoly domain (p := p) (ch := r) i0)) 0
    =
    honestClaim domain (p := p) := by
  intro i0

  have hopen : numOpenVars (n := Nat.succ n') i0 = n' := by
    simp [numOpenVars, i0]

  -- Rewrite each eval₂ using the sum expansion lemma
  -- The LHS is domain.foldl (fun acc a => acc + sumOverDomainRecursive domain (·+·) 0 (m:=n') (Fa)) 0
  -- which equals sumOverDomainRecursive domain (·+·) 0 (m:=n'+1) F
  -- by the succ unfolding.

  -- First, rewrite the RHS (honestClaim) to sumOverDomainRecursive form
  simp only [honestClaim, residualSum]

  -- The RHS is sumOverDomainRecursive domain (·+·) 0 (m := Nat.succ n') (fun x => eval (addCasesFun [] x (cast ...)) p)
  -- The LHS after eval₂ expansion becomes domain.foldl ... which is the succ unfolding

  -- Use sum_over_domain_recursive_succ to rewrite the RHS
  rw [sum_over_domain_recursive_succ]

  -- Now both sides are domain.foldl (...) 0
  -- Show the fold functions are equal
  congr 1
  funext acc a

  -- Show the inner expressions match
  have heval_a := eval_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := Nat.succ n') domain
    (p := p) (r := r) (i := i0) (a := a)
  rw [heval_a]
  congr 1

-- ============================================================================
-- Lemmas moved from Theorems/Completeness.lean
-- ============================================================================


lemma honestTranscript_roundPoly_eq_honestRoundPoly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) :
  (generateHonestTranscript domain (𝔽 := 𝔽) (n := n) p (honestClaim domain p) r).roundPolys i
    =
  honestRoundPoly domain (p := p) (ch := r) i := by
  classical

  -- Force the same `==` that `generateHonestTranscript` uses.
  letI : BEq 𝔽 := instBEqOfDecidableEq (α := 𝔽)

  -- Make it lawful using decide.
  letI : LawfulBEq 𝔽 :=
  { rfl := by
      intro a
      simp
    eq_of_beq := by
      intro a b h
      have hdec : decide (a = b) = true := by
        simpa [instBEqOfDecidableEq] using h
      have : (decide (a = b) = true) = (a = b) := by
        simp
      have hab : a = b := by
        simpa [this] using hdec
      exact hab }

  cases i with
  | mk k hk => simp [generateHonestTranscript, honestRoundPoly, honestProverMessageAt]


lemma honest_transcript_sum_identity
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (r : Fin n → 𝔽)
  (i : Fin n) :
  domain.foldl (fun acc a =>
    acc + CPoly.CMvPolynomial.eval (fun _ => a)
      ((generateHonestTranscript domain p (honestClaim domain p) r).roundPolys i)) 0 =
  (generateHonestTranscript domain p (honestClaim domain p) r).claims (honestClaim domain p) (Fin.castSucc i) := by
  classical

  have hrp : (generateHonestTranscript domain p (honestClaim domain p) r).roundPolys i =
    honestRoundPoly domain p r i := by
    exact honestTranscript_roundPoly_eq_honestRoundPoly domain p r i
  -- Rewrite domain.foldl ... (roundPolys i) to domain.foldl ... (honestRoundPoly domain p r i)
  conv_lhs => arg 1; ext acc a; rw [hrp]

  cases' h : i.val with k
  · have hcast : Fin.castSucc i = ⟨0, Nat.succ_pos n⟩ := by
      ext; simp [h]
    simp only [generateHonestTranscript, hcast]
    have hn_pos : 0 < n := i.pos
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = Nat.succ n' := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)
    subst hn'
    have hi_eq : i = ⟨0, Nat.succ_pos n'⟩ := by
      ext
      exact h
    subst hi_eq
    exact honest_round0_domain_sum_eq_honest_claim domain p r

  · have hi_val : i.val = k + 1 := by simp [h]
    have hk_lt : k < n := by omega
    have hk1_lt : k + 1 < n := by omega
    let prev : Fin n := ⟨k, hk_lt⟩
    have hstep := honest_step_round (𝔽 := 𝔽) (n := n) domain (p := p) (r := r) (i := prev) hk1_lt
    simp only [generateHonestTranscript]
    have hi_eq : i = ⟨k + 1, hk1_lt⟩ := Fin.ext hi_val
    subst hi_eq
    simp only [prev, honestRoundPoly, honestProverMessageAt] at hstep ⊢
    exact hstep


lemma honest_transcript_final_eq_eval
  {𝔽 : Type _}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
  ∀ (n : ℕ) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽),
  (generateHonestTranscript domain p (honestClaim domain p) r).claims (honestClaim domain p) (Fin.last n) =
    CPoly.CMvPolynomial.eval (generateHonestTranscript domain p (honestClaim domain p) r).challenges p := by
  intro n
  induction n with
  | zero =>
    intro domain p r
    simp [generateHonestTranscript, Transcript.claims, generateHonestClaims, Fin.last,
          honestClaim, residualSum]
    congr 1; funext i; exact Fin.elim0 i
  | succ n' ih =>
    intro domain p r
    simp only [generateHonestTranscript, Transcript.claims, generateHonestClaims, Fin.last]
    let iLast : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
    have hLast : iLast.val.succ = n' + 1 := by simp [iLast]
    have hrp : honestProverMessageAt domain p iLast (challengeSubset r iLast) =
        honestRoundPoly domain p r iLast := by
      simp [honestRoundPoly]
    rw [hrp]
    exact honest_last_round domain p r iLast hLast
