import SumcheckProtocol.Properties.Events.Accepts
import SumcheckProtocol.Properties.Events.BadRound
import SumcheckProtocol.Src.Verifier
import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Hypercube

set_option maxHeartbeats 10000000

lemma acceptsEvent_rounds_ok
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 n) :
  AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p claim t →
    (List.finRange n).all (fun i : Fin n =>
      verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i)
      &&
      decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i))
    ) = true := by
  intro hAcc
  dsimp [AcceptsEvent] at hAcc
  simp [isVerifierAccepts, residualSum_full_eq_eval] at hAcc
  -- turn (roundsOk && finalOk) = true into roundsOk = true ∧ finalOk = true
  have h' : ( (List.finRange n).all (fun i : Fin n =>
      verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i)
      &&
      decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i))
    ) = true
    ∧
    decide (t.claims claim (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true) := by
    simpa [Bool.and_eq_true] using hAcc
  exact h'.1

/-- K-parameterized: the rounds-OK part of `AcceptsEvent` for a partial-run
transcript of length `k.val`. The check ranges over `Fin k.val` and uses
`indDegreeK p ⟨i.val, _⟩` to lift the partial-round index into the polynomial. -/
lemma acceptsEvent_rounds_ok_k
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 k.val) :
  AcceptsEvent k domain p claim t →
    (List.finRange k.val).all (fun i : Fin k.val =>
      verifierCheck domain
        (indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩)
        (t.claims claim (Fin.castSucc i)) (t.roundPolys i)
      &&
      decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i))
    ) = true := by
  intro hAcc
  dsimp [AcceptsEvent] at hAcc
  simp [isVerifierAccepts] at hAcc
  have hk_le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  have h' :
      ((List.finRange k.val).all (fun i : Fin k.val =>
          verifierCheck domain
            (indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩)
            (t.claims claim (Fin.castSucc i)) (t.roundPolys i)
          &&
          decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i))
        ) = true
        ∧
        decide (t.claims claim (Fin.last k.val) =
          residualSum (𝔽 := 𝔽) domain t.challenges p hk_le) = true) := by
    simpa [Bool.and_eq_true] using hAcc
  exact h'.1

lemma acceptsEvent_final_ok
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 n) :
  AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p claim t →
    decide (t.claims claim (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true := by
  intro hAcc
  dsimp [AcceptsEvent] at hAcc
  simp [isVerifierAccepts, residualSum_full_eq_eval] at hAcc
  have h' :
      (List.finRange n).all (fun i : Fin n =>
        verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i)
        &&
        decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i))
      ) = true
      ∧
      decide (t.claims claim (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p) = true := by
    simpa [Bool.and_eq_true] using hAcc
  exact h'.2

lemma verifier_check_eq_true_iff
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (maxDegree : ℕ)
  (roundClaim : 𝔽)
  (roundP : CPoly.CMvPolynomial 1 𝔽) :
  verifierCheck (𝔽 := 𝔽) domain maxDegree roundClaim roundP = true
    ↔
    (domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) roundP) 0
      = roundClaim)
    ∧
    (CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ roundP ≤ maxDegree) := by
  simp [verifierCheck]

lemma acceptsEvent_round_facts
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 n)
  (i : Fin n) :
  AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p claim t →
    verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i) = true
    ∧
    t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i) := by
  intro hAcc
  have hRounds := acceptsEvent_rounds_ok domain (p := p) (claim := claim) (t := t) hAcc

  have hall :
      ∀ x, x ∈ List.finRange n →
        (verifierCheck domain (indDegreeK p x) (t.claims claim (Fin.castSucc x)) (t.roundPolys x)
          &&
          decide (t.claims claim x.succ = nextClaim (t.challenges x) (t.roundPolys x))) = true := by
    exact List.all_eq_true.mp hRounds

  have hi_mem : i ∈ List.finRange n := by
    simp [List.mem_finRange i]

  have hix := hall i hi_mem

  have hsplit :
      verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i) = true
      ∧ decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i)) = true := by
    simpa [Bool.and_eq_true] using hix

  refine ⟨hsplit.1, ?_⟩
  exact decide_eq_true_eq.mp hsplit.2

lemma acceptsEvent_domain_sum_eq_claim
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 n)
  (i : Fin n) :
  AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p claim t →
    domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i)) 0
      =
    t.claims claim (Fin.castSucc i) := by
  intro hAcc
  have hcheck := (acceptsEvent_round_facts domain (p := p) (claim := claim) (t := t) (i := i) hAcc).1
  -- unpack verifierCheck = true into the domain sum equality
  have hiff :=
    (verifier_check_eq_true_iff (𝔽 := 𝔽) domain
      (maxDegree := indDegreeK p i)
      (roundClaim := t.claims claim (Fin.castSucc i))
      (roundP := t.roundPolys i))
  have hprops := hiff.mp hcheck
  exact hprops.1

/-- K-parameterized per-round facts: for a partial-run-accepted transcript,
each round-`i` (i < k.val) satisfies the verifier's check and claims consistency. -/
lemma acceptsEvent_round_facts_k
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 k.val)
  (i : Fin k.val) :
  AcceptsEvent k domain p claim t →
    verifierCheck domain
      (indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩)
      (t.claims claim (Fin.castSucc i)) (t.roundPolys i) = true
    ∧
    t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i) := by
  intro hAcc
  have hRounds := acceptsEvent_rounds_ok_k k domain (p := p) (claim := claim) (t := t) hAcc
  have hall :
      ∀ x, x ∈ List.finRange k.val →
        (verifierCheck domain
            (indDegreeK p ⟨x.val, lt_of_lt_of_le x.isLt (Nat.le_of_lt_succ k.isLt)⟩)
            (t.claims claim (Fin.castSucc x)) (t.roundPolys x)
          &&
          decide (t.claims claim x.succ = nextClaim (t.challenges x) (t.roundPolys x))) = true :=
    List.all_eq_true.mp hRounds
  have hi_mem : i ∈ List.finRange k.val := by simp [List.mem_finRange i]
  have hix := hall i hi_mem
  have hsplit :
      verifierCheck domain
        (indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩)
        (t.claims claim (Fin.castSucc i)) (t.roundPolys i) = true
      ∧ decide (t.claims claim i.succ = nextClaim (t.challenges i) (t.roundPolys i)) = true := by
    simpa [Bool.and_eq_true] using hix
  refine ⟨hsplit.1, ?_⟩
  exact decide_eq_true_eq.mp hsplit.2

/-- K-parameterized domain-sum identity from an accepted partial-run transcript. -/
lemma acceptsEvent_domain_sum_eq_claim_k
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (t : Transcript 𝔽 k.val)
  (i : Fin k.val) :
  AcceptsEvent k domain p claim t →
    domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i)) 0
      =
    t.claims claim (Fin.castSucc i) := by
  intro hAcc
  have hcheck := (acceptsEvent_round_facts_k k domain (p := p) (claim := claim) (t := t) (i := i) hAcc).1
  have hiff :=
    (verifier_check_eq_true_iff (𝔽 := 𝔽) domain
      (maxDegree := indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩)
      (roundClaim := t.claims claim (Fin.castSucc i))
      (roundP := t.roundPolys i))
  have hprops := hiff.mp hcheck
  exact hprops.1

lemma acceptsEvent_domain_sum_eq_claim_of_honest
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (claim : 𝔽)
  (r : Fin n → 𝔽)
  (t : Transcript 𝔽 n)
  (i : Fin n)
  (hi : t.roundPolys i = honestRoundPoly domain p r i) :
  AcceptsEvent ⟨n, Nat.lt_succ_self n⟩ domain p claim t →
    domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (honestRoundPoly domain p r i)) 0
      =
    t.claims claim (Fin.castSucc i) := by
  intro hAcc
  simpa [hi] using (acceptsEvent_domain_sum_eq_claim domain (p := p) (claim := claim) (t := t) (i := i) hAcc)
