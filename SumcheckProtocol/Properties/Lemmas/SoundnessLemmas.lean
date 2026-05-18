/-
  SoundnessLemmas.lean

  Auxiliary lemmas for the soundness proof, including:
  - accepts_and_bad_implies_exists_round_disagree_but_agree
  - degree_eval2Poly_honest_combined_map_le_ind_degree_k
  - honest_round_poly_degree_le_ind_degree_k
  - prob_over_challenges_fiber_le
  - prob_single_round_accepts_and_disagree_le
  - sum_accepts_and_round_disagree_but_agree_bound
-/

import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import SumcheckProtocol.Properties.Probability.Challenges
import SumcheckProtocol.Properties.Events.Accepts
import SumcheckProtocol.Properties.Events.BadRound
import SumcheckProtocol.Src.Verifier

import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Properties.Probability.Fields
import CompPoly.Data.ExtTreeMap.ExtTreeMap
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import SumcheckProtocol.Properties.Lemmas.BadTranscript
import SumcheckProtocol.Properties.Lemmas.Accepts
import SumcheckProtocol.Properties.Lemmas.HonestProver
import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Properties.Lemmas.Hypercube
import SumcheckProtocol.Properties.Lemmas.Agreement
import SumcheckProtocol.Properties.Lemmas.Degree
import SumcheckProtocol.Properties.Lemmas.List
import SumcheckProtocol.Properties.Lemmas.Fin
import SumcheckProtocol.Properties.Lemmas.CMvPolynomial
import SumcheckProtocol.Properties.Lemmas.Eval
import SumcheckProtocol.Properties.Lemmas.Nat
import SumcheckProtocol.Properties.Lemmas.HonestRoundProofs
import SumcheckProtocol.Properties.Lemmas.BadTranscriptAnalysis


-- every monomial in a CMvPolynomial has exponent at variable i bounded by indDegreeK
lemma monomial_exponent_le_ind_degree {𝔽 : Type _} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (p : CPoly.CMvPolynomial n 𝔽) (i : Fin n)
    (mc : CPoly.CMvMonomial n × 𝔽) (hmc : mc ∈ p.1.toList) :
    extractExpVarI mc.1 i ≤ indDegreeK p i := by
  classical
  have hget : p.1[mc.1]? = some mc.2 :=
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := p.1) (k := mc.1) (v := mc.2)).1 hmc
  have hcne : mc.2 ≠ (0 : 𝔽) := by
    intro hc0; exact (p.2 mc.1) (by simpa [hc0] using hget)
  let m' : Fin n →₀ ℕ := CPoly.CMvMonomial.toFinsupp mc.1
  have hcoeffMv : MvPolynomial.coeff m' (CPoly.fromCMvPolynomial (R := 𝔽) p) = mc.2 := by
    simpa [m', CPoly.CMvPolynomial.coeff, hget] using CPoly.coeff_eq (n := n) (R := 𝔽) (m := m') p
  have hsupp : m' ∈ (CPoly.fromCMvPolynomial (R := 𝔽) p).support :=
    MvPolynomial.mem_support_iff.2 (by simpa [hcoeffMv] using hcne)
  have hmon := MvPolynomial.monomial_le_degreeOf (i := i) (h_m := hsupp)
  have hdegEq : MvPolynomial.degreeOf i (CPoly.fromCMvPolynomial (R := 𝔽) p)
      = CPoly.CMvPolynomial.degreeOf i p := by
    simpa using (congrArg (fun f => f i) (CPoly.degreeOf_equiv (p := p) (S := 𝔽))).symm
  simpa [indDegreeK, extractExpVarI, m', hdegEq] using hmon

-- folding c * substMonomial over a list of monomials preserves the degree bound,
-- when each monomial's exponent at i is bounded by d and the substitution map is honest
lemma eval2Poly_foldl_degree_le {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
    (b : Fin (numOpenVars (n := n) i) → 𝔽)
    (vs : Fin n → CPoly.CMvPolynomial 1 𝔽)
    (hvs : vs = honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b)
    (d : ℕ) (hd : d = indDegreeK p i)
    (l : List (CPoly.CMvMonomial n × 𝔽))
    (hsub : ∀ mc ∈ l, mc ∈ p.1.toList)
    (acc : CPoly.CMvPolynomial 1 𝔽)
    (hacc : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) acc ≤ d) :
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (List.foldl (fun acc mc =>
        Add.add (Mul.mul (c1 (𝔽 := 𝔽) mc.2) (substMonomial (𝔽 := 𝔽) (n := n) vs mc.1)) acc)
        acc l) ≤ d := by
  induction l generalizing acc with
  | nil => simpa [List.foldl] using hacc
  | cons mc l ih =>
      have hmc_mem : mc ∈ p.1.toList := hsub mc (by simp)
      have hexp : extractExpVarI mc.1 i ≤ d := by
        simpa [hd] using monomial_exponent_le_ind_degree p i mc hmc_mem
      have hsubst : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (substMonomial (n := n) (𝔽 := 𝔽) vs mc.1)
          ≤ extractExpVarI mc.1 i := by
        simpa [hvs] using degree_subst_monomial_honest_combined_le_exp_i
          (𝔽 := 𝔽) (n := n) (r := r) (i := i) (b := b) (m := mc.1)
      have hmul_le : CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
          (Mul.mul (c1 (𝔽 := 𝔽) mc.2) (substMonomial (n := n) (𝔽 := 𝔽) vs mc.1)) ≤ d := by
        have hmul' := degreeOf_mul_le_univariate (𝔽 := 𝔽)
          (a := c1 (𝔽 := 𝔽) mc.2) (b := substMonomial (n := n) (𝔽 := 𝔽) vs mc.1)
        have : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) mc.2) +
            CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (substMonomial (n := n) (𝔽 := 𝔽) vs mc.1)
            ≤ extractExpVarI mc.1 i := by
          rw [degreeOf_c1_eq_zero]; simpa using hsubst
        exact le_trans (le_trans hmul' this) hexp
      have hstep : CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
          (Add.add (Mul.mul (c1 (𝔽 := 𝔽) mc.2) (substMonomial (n := n) (𝔽 := 𝔽) vs mc.1)) acc) ≤ d :=
        hadd_degreeOf0_le (𝔽 := 𝔽) (d := d) _ _ hmul_le hacc
      simpa [List.foldl] using ih (fun mc' hmc' => hsub mc' (by simp [hmc'])) _ hstep

-- evaluating p through the honest substitution map produces a univariate
-- polynomial whose degree is at most the individual degree of p in variable i
theorem degree_eval2Poly_honest_combined_map_le_ind_degree_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n)
(b : Fin (numOpenVars (n := n) i) → 𝔽) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1
        (honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b) p)
    ≤ indDegreeK p i := by
  classical
  let vs := honestCombinedMap (𝔽 := 𝔽) (n := n) i (challengeSubset r i) b
  let d := indDegreeK p i
  let step : CPoly.CMvPolynomial 1 𝔽 → (CPoly.CMvMonomial n × 𝔽) → CPoly.CMvPolynomial 1 𝔽 :=
    fun acc mc => Add.add (Mul.mul (c1 (𝔽 := 𝔽) mc.2) (substMonomial (𝔽 := 𝔽) (n := n) vs mc.1)) acc
  have hinit : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (c1 (𝔽 := 𝔽) (0 : 𝔽)) ≤ d := by
    rw [degreeOf_c1_eq_zero]; exact Nat.zero_le d
  have hfold : CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (List.foldl step (c1 (𝔽 := 𝔽) (0 : 𝔽)) p.1.toList) ≤ d :=
    eval2Poly_foldl_degree_le p r i b vs rfl d rfl p.1.toList (fun _ h => h) _ hinit
  have heq : CPoly.eval₂Poly (𝔽 := 𝔽) (n := n) c1 vs p =
      List.foldl step (c1 (𝔽 := 𝔽) (0 : 𝔽)) p.1.toList := by
    simpa [step] using CPoly.eval₂Poly_eq_list_foldl (𝔽 := 𝔽) (n := n) (f := c1) (vs := vs) (p := p)
  simpa [vs, d, heq] using hfold

-- the honest round polynomial has degree at most indDegreeK p i
theorem honest_round_poly_degree_le_ind_degree_k {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(domain : List 𝔽)
(p : CPoly.CMvPolynomial n 𝔽) (r : Fin n → 𝔽) (i : Fin n) :
  CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (honestRoundPoly domain (p := p) (ch := r) i)
    ≤ indDegreeK p i := by
  classical
  dsimp [honestRoundPoly]
  -- reduce to the general degree lemma for honestProverMessageAt
  refine degree_honest_prover_message_at_le_of_per_b (𝔽 := 𝔽) (n := n)
    domain
    (p := p) (i := i) (challenges := challengeSubset r i) (d := indDegreeK p i) ?_
  intro b
  -- the remaining goal is exactly the provided axiom
  simpa using
    (degree_eval2Poly_honest_combined_map_le_ind_degree_k (𝔽 := 𝔽) (n := n)
      (p := p) (r := r) (i := i) (b := b))

-- the set satisfying E injects into the sigma type Σ rRest, fiber(rRest)
-- via r ↦ (removeNth i r, r i)
lemma filter_card_le_sigma_fiber {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
    (i : Fin (n + 1)) (E : (Fin (n + 1) → 𝔽) → Prop) [DecidablePred E] :
    (Finset.univ.filter E).card ≤
    ((Finset.univ : Finset (Fin n → 𝔽)).sigma
      (fun rRest => (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest)))).card := by
  let g : (Fin (n + 1) → 𝔽) → Sigma fun _ : (Fin n → 𝔽) => 𝔽 :=
    fun r => ⟨Fin.removeNth i r, r i⟩
  have hg_maps : Set.MapsTo g (Finset.univ.filter E : Set _)
      ((Finset.univ.sigma (fun rRest => Finset.univ.filter (fun a => E (Fin.insertNth i a rRest)))) : Set _) := by
    intro r hr
    have hrE : E r := by simpa [Finset.mem_filter] using hr
    have hrE' : E (Fin.insertNth i (r i) (Fin.removeNth i r)) := by
      simpa [Fin.insertNth_self_removeNth] using hrE
    simp only [Finset.coe_sigma, Finset.coe_filter, Finset.coe_univ, Set.mem_sigma_iff]
    exact ⟨Set.mem_univ _, by simpa [g, hrE']⟩
  have hg_inj : Set.InjOn g (Finset.univ.filter E : Set _) := by
    intro r _ s _ hgs
    have hrest := congrArg Sigma.fst hgs
    have ha := congrArg Sigma.snd hgs
    simp [g] at hrest ha
    calc r = Fin.insertNth i (r i) (Fin.removeNth i r) := by simp
      _ = Fin.insertNth i (s i) (Fin.removeNth i s) := by simp [hrest, ha]
      _ = s := by simp
  exact Finset.card_le_card_of_injOn g hg_maps hg_inj

-- bounding the sigma cardinality: if each fiber has ≤ d elements,
-- then the sigma has ≤ d * |Fin n → 𝔽| elements
lemma sigma_fiber_card_le {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
    (i : Fin (n + 1)) (d : ℕ) (E : (Fin (n + 1) → 𝔽) → Prop) [DecidablePred E]
    (hfiber : ∀ rRest : (Fin n → 𝔽),
      ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤ d) :
    ((Finset.univ : Finset (Fin n → 𝔽)).sigma
      (fun rRest => (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest)))).card
    ≤ d * Fintype.card (Fin n → 𝔽) := by
  classical
  have hS_card : ((Finset.univ : Finset (Fin n → 𝔽)).sigma
      (fun rRest => (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest)))).card
      = ∑ rRest : (Fin n → 𝔽), ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card := by
    simp
  rw [hS_card]
  calc ∑ rRest : (Fin n → 𝔽), ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card
      ≤ ∑ _ : (Fin n → 𝔽), d := Finset.sum_le_sum (fun rRest _ => hfiber rRest)
    _ = d * Fintype.card (Fin n → 𝔽) := by simp [Nat.mul_comm]

-- generic fiber counting: if for every choice of the other n variables,
-- at most d values of variable i satisfy E, then Pr[E] ≤ d / |𝔽|
theorem prob_over_challenges_fiber_le {𝔽 : Type _} {n : ℕ} [Fintype 𝔽] [DecidableEq 𝔽]
(i : Fin (n + 1)) (d : ℕ) (E : (Fin (n + 1) → 𝔽) → Prop) [DecidablePred E]
(hfiber : ∀ rRest : (Fin n → 𝔽),
  ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤ d) :
  probOverChallenges (𝔽 := 𝔽) (n := n + 1) E ≤ (d : ℚ) / fieldSize (𝔽 := 𝔽) := by
  classical
  simp [probEvent, allChallenges, fieldSize]
  -- align the classical decidable instance with the provided one
  have hfilter :
      (@Finset.filter (Fin (n + 1) → 𝔽) E (fun a => Classical.propDecidable (E a)) Finset.univ)
        = (Finset.univ.filter E) := by
    simpa using Finset.filter_congr_decidable (s := (Finset.univ : Finset (Fin (n + 1) → 𝔽)))
      (p := E) (h := fun a => Classical.propDecidable (E a))
  rw [hfilter]
  -- counting: |{r | E r}| ≤ d * |Fin n → 𝔽|
  have hcardNat : (Finset.univ.filter E).card ≤ d * Fintype.card (Fin n → 𝔽) :=
    le_trans (filter_card_le_sigma_fiber i E) (sigma_fiber_card_le i d E hfiber)
  have hcardQ : ((Finset.univ.filter E).card : ℚ) ≤ (d : ℚ) * (Fintype.card (Fin n → 𝔽) : ℚ) := by
    exact_mod_cast hcardNat
  -- arithmetic: d * |𝔽|^n / |𝔽|^(n+1) = d / |𝔽|
  have hden_nonneg : (0 : ℚ) ≤ (Fintype.card 𝔽 : ℚ) ^ (n + 1) :=
    pow_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card 𝔽)) (n + 1)
  refine le_trans (div_le_div_of_nonneg_right hcardQ hden_nonneg) ?_
  by_cases h0 : Fintype.card 𝔽 = 0
  · simp [h0]
  · have h0q : (Fintype.card 𝔽 : ℚ) ≠ 0 := by exact_mod_cast h0
    have hpow_ne : (Fintype.card 𝔽 : ℚ) ^ n ≠ 0 := pow_ne_zero n h0q
    simp [pow_succ, mul_comm]
    refine le_of_eq ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_div_mul_left (a := (d : ℚ)) (b := (Fintype.card 𝔽 : ℚ))
        (c := (Fintype.card 𝔽 : ℚ) ^ n) hpow_ne

-- if the verifier accepts a transcript, the round-i polynomial has degree ≤ maxIndDegree
lemma adversary_poly_degree_le_max_ind_degree {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽) (claim : 𝔽) (t : Transcript 𝔽 n) (i : Fin n)
    (hAcc : AcceptsEvent domain p claim t) :
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) (t.roundPolys i) ≤ maxIndDegree p := by
  have hcheck :
      verifierCheck domain (indDegreeK p i) (t.claims claim (Fin.castSucc i)) (t.roundPolys i) = true :=
    (acceptsEvent_round_facts domain (p := p) (claim := claim) (t := t) (i := i) hAcc).1
  have hdeg :
      CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ (t.roundPolys i) ≤ indDegreeK p i :=
    ((verifier_check_eq_true_iff (𝔽 := 𝔽) domain
      (maxDegree := indDegreeK p i)
      (roundClaim := t.claims claim (Fin.castSucc i))
      (roundP := t.roundPolys i)).1 hcheck).2
  exact le_trans hdeg (ind_degree_k_le_max_ind_degree p i)

-- deg(g - h) ≤ d when deg(g) ≤ d and deg(h) ≤ d (for univariate CMvPolynomials)
lemma difference_poly_degree_le {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (g h : CPoly.CMvPolynomial 1 𝔽) (d : ℕ)
    (hgdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) g ≤ d)
    (hhdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) h ≤ d) :
    MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) ≤ d := by
  classical
  let i0 : Fin 1 := ⟨0, by decide⟩
  have hEqg : CPoly.CMvPolynomial.degreeOf i0 g =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial g) := by
    simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := g) (S := 𝔽))
  have hEqh : CPoly.CMvPolynomial.degreeOf i0 h =
      MvPolynomial.degreeOf (σ := Fin 1) (R := 𝔽) i0 (CPoly.fromCMvPolynomial h) := by
    simpa using congrArg (fun f => f i0) (CPoly.degreeOf_equiv (p := h) (S := 𝔽))
  have hsub_le :=
    MvPolynomial.degreeOf_sub_le (R := 𝔽) (σ := Fin 1) i0
      (CPoly.fromCMvPolynomial g) (CPoly.fromCMvPolynomial h)
  have hmax_le : max (MvPolynomial.degreeOf i0 (CPoly.fromCMvPolynomial g))
      (MvPolynomial.degreeOf i0 (CPoly.fromCMvPolynomial h)) ≤ d :=
    max_le_iff.mpr ⟨by rw [← hEqg]; exact hgdeg, by rw [← hEqh]; exact hhdeg⟩
  simpa [differencePoly, i0] using le_trans hsub_le hmax_le

-- Schwartz-Zippel core for univariate: distinct polynomials g ≠ h with deg(g-h) ≤ d
-- agree on at most d field elements (evaluated via nextClaim)
lemma agreement_set_card_le {𝔽 : Type _} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (g h : CPoly.CMvPolynomial 1 𝔽) (d : ℕ)
    (hgh_ne : g ≠ h)
    (hdiffdeg : MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) ≤ d) :
    ({a ∈ (Finset.univ : Finset 𝔽) |
        nextClaim (𝔽 := 𝔽) (roundChallenge := a) g =
          nextClaim (𝔽 := 𝔽) (roundChallenge := a) h}).card ≤ d := by
  classical
  let agreeA : Finset 𝔽 :=
    {a ∈ (Finset.univ : Finset 𝔽) |
      nextClaim (𝔽 := 𝔽) (roundChallenge := a) g =
        nextClaim (𝔽 := 𝔽) (roundChallenge := a) h}
  let agreeF : Finset (Fin 1 → 𝔽) :=
    {assignment ∈ (Finset.univ : Finset (Fin 1 → 𝔽)) |
      CPoly.CMvPolynomial.eval assignment g = CPoly.CMvPolynomial.eval assignment h}

  -- map scalar agreement to function-space agreement
  have hmap : agreeA.card ≤ agreeF.card := by
    have hmaps : Set.MapsTo (fun a : 𝔽 => (fun _ : Fin 1 => a)) (agreeA : Set 𝔽) (agreeF : Set (Fin 1 → 𝔽)) := by
      intro a ha
      have haEq := (Finset.mem_filter.1 ha).2
      exact Finset.mem_filter.2 ⟨by simp, by simpa [agreeF, nextClaim] using haEq⟩
    have hinj : Set.InjOn (fun a : 𝔽 => (fun _ : Fin 1 => a)) (agreeA : Set 𝔽) := by
      intro a1 _ a2 _ hEq
      simpa using congrArg (fun f => f (0 : Fin 1)) hEq
    exact Finset.card_le_card_of_injOn _ hmaps hinj

  -- use Schwartz-Zippel to bound the function-space agreement count
  have hAgreeF : agreeF.card = countAssignmentsCausingAgreement g h := by
    simp [countAssignmentsCausingAgreement, agreeF, allAssignmentsN, allChallenges,
      AgreementAtEvent, AgreementEvent, -AgreementEvent_eval_equiv]
    rfl
  have hprob := prob_agreement_le_degree_over_field_size (𝔽 := 𝔽) g h hgh_ne
  have hprob' :
      (countAssignmentsCausingAgreement g h : ℚ) / (countAllAssignmentsN (𝔽 := 𝔽) 1 : ℚ) ≤
      (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
    simpa [probAgreementAtRandomChallenge] using hprob
  have hdenom : countAllAssignmentsN (𝔽 := 𝔽) 1 = fieldSize (𝔽 := 𝔽) := by
    simp [countAllAssignmentsN, fieldSize, allAssignmentsN]
  have hpos : 0 < (fieldSize (𝔽 := 𝔽) : ℚ) := by
    exact_mod_cast (show 0 < fieldSize (𝔽 := 𝔽) by
      simpa [fieldSize] using (Fintype.card_pos_iff.2 ⟨(0 : 𝔽)⟩))
  have hcount_le_deg :
      (countAssignmentsCausingAgreement g h : ℚ) ≤
      (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) : ℚ) := by
    have hprob'' : (countAssignmentsCausingAgreement g h : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) ≤
        (MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
      simpa [hdenom] using hprob'
    have := mul_le_mul_of_nonneg_right hprob'' (le_of_lt hpos)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ne_of_gt hpos] using this
  have hcount_nat : countAssignmentsCausingAgreement g h ≤
      MvPolynomial.degreeOf (⟨0, by decide⟩ : Fin 1) (differencePoly g h) := by
    exact_mod_cast hcount_le_deg
  have hagreeF_le : agreeF.card ≤ d := by
    exact le_trans (by simpa [hAgreeF] using hcount_nat) hdiffdeg
  exact le_trans hmap hagreeF_le

-- the set of challenges where the adversary "disagrees but agrees at the challenge point"
-- is a subset of the polynomial agreement set
-- if every element of a filtered set satisfies a predicate, the set is bounded
-- by the predicate's satisfying set
lemma filter_card_le_of_implies {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽] [Fintype 𝔽] {n : ℕ}
    (g h : CPoly.CMvPolynomial 1 𝔽)
    (i : Fin (n + 1)) (rRest : Fin n → 𝔽)
    (E : (Fin (n + 1) → 𝔽) → Prop) [DecidablePred E]
    (hE_implies_agree : ∀ a, E (Fin.insertNth i a rRest) →
        nextClaim (𝔽 := 𝔽) (roundChallenge := a) g =
          nextClaim (𝔽 := 𝔽) (roundChallenge := a) h) :
    ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤
    ({a ∈ (Finset.univ : Finset 𝔽) |
        nextClaim (𝔽 := 𝔽) (roundChallenge := a) g =
          nextClaim (𝔽 := 𝔽) (roundChallenge := a) h}).card :=
  Finset.card_le_card (fun a ha =>
    Finset.mem_filter.2 ⟨by simp, hE_implies_agree a (Finset.mem_filter.1 ha).2⟩)

-- Schwartz-Zippel for a single round: if the adversary's round-i polynomial
-- differs from honest but agrees at the challenge, then the probability of
-- this happening (over the random challenge at round i) is ≤ maxIndDegree(p) / |𝔽|
theorem prob_single_round_accepts_and_disagree_le {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(st : SumcheckProtocolStatement 𝔽 n) (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) (i : Fin n) :
  probOverChallenges (𝔽 := 𝔽) (n := n)
    (fun r =>
      AcceptsAndBadTranscriptOnChallenges st P r ∧
      RoundDisagreeButAgreeAtChallenge st P r i)
    ≤ (maxIndDegree st.polynomial) / fieldSize (𝔽 := 𝔽) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n' =>
      let E : (Fin (n' + 1) → 𝔽) → Prop := fun r =>
        AcceptsAndBadTranscriptOnChallenges st P r ∧
        RoundDisagreeButAgreeAtChallenge st P r i
      letI : DecidablePred E := Classical.decPred _

      have hfiber : ∀ rRest : (Fin n' → 𝔽),
          ((Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))).card ≤
            maxIndDegree st.polynomial := by
        intro rRest
        classical
        -- reference challenges: use 0 at position i (choice doesn't matter for g, h)
        let r0 : Fin (n' + 1) → 𝔽 := Fin.insertNth i (0 : 𝔽) rRest
        let g : CPoly.CMvPolynomial 1 𝔽 := (proverTranscript st P r0).roundPolys i
        let h : CPoly.CMvPolynomial 1 𝔽 := honestRoundPoly st.domain (p := st.polynomial) (ch := r0) i
        let S : Finset 𝔽 := (Finset.univ : Finset 𝔽).filter (fun a => E (Fin.insertNth i a rRest))

        by_cases hS : S = ∅
        · simp [S, hS]
        ·
          -- pick a witness where the event holds
          rcases Finset.nonempty_iff_ne_empty.2 hS with ⟨a0, ha0⟩
          have ha0E : E (Fin.insertNth i a0 rRest) := (Finset.mem_filter.1 ha0).2
          let adv_tr_a0 := proverTranscript st P (Fin.insertNth i a0 rRest)

          -- key: challenges before round i don't depend on the challenge at i
          have hchal_eq (a : 𝔽) :
              challengeSubset (Fin.insertNth i a rRest) i = challengeSubset r0 i := by
            funext j
            have hjlt : (⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : Fin (n' + 1)) < i :=
              Fin.lt_def.mpr j.isLt
            simp [r0, challengeSubset, Fin.insertNth_apply_below hjlt]

          -- so g and h don't depend on the challenge at position i
          have hg_eq (a : 𝔽) :
              (proverTranscript st P (Fin.insertNth i a rRest)).roundPolys i = g := by
            simp [proverTranscript, g, hchal_eq a]
          have hh_eq (a : 𝔽) :
              honestRoundPoly st.domain (p := st.polynomial) (ch := Fin.insertNth i a rRest) i = h := by
            unfold honestRoundPoly
            simpa [h, r0] using congrArg
              (fun cs => honestProverMessageAt st.domain (p := st.polynomial) (i := i) (challenges := cs))
              (hchal_eq a)

          -- g ≠ h (from the witness a0 where the event holds)
          have hgh_ne : g ≠ h := by
            intro hgh
            exact (ha0E.2).1 (by rw [hg_eq a0, hh_eq a0, hgh])

          -- degree bounds
          have hgdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) g ≤ maxIndDegree st.polynomial := by
            have : adv_tr_a0.roundPolys i = g := hg_eq a0
            simpa [this] using adversary_poly_degree_le_max_ind_degree st.domain st.polynomial st.claim adv_tr_a0 i (ha0E.1).1
          have hhdeg : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) h ≤ maxIndDegree st.polynomial := by
            have : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) h ≤ indDegreeK st.polynomial i := by
              simpa [h] using honest_round_poly_degree_le_ind_degree_k st.domain st.polynomial r0 i
            exact le_trans this (ind_degree_k_le_max_ind_degree st.polynomial i)

          -- Schwartz-Zippel: agreement set bounded by degree of difference polynomial
          have hdiffdeg := difference_poly_degree_le g h (maxIndDegree st.polynomial) hgdeg hhdeg
          have hagree_card := agreement_set_card_le g h (maxIndDegree st.polynomial) hgh_ne hdiffdeg

          -- failure set ⊆ agreement set
          have hS_le : S.card ≤
              ({a ∈ (Finset.univ : Finset 𝔽) |
                  nextClaim (𝔽 := 𝔽) (roundChallenge := a) g =
                    nextClaim (𝔽 := 𝔽) (roundChallenge := a) h}).card := by
            refine Finset.card_le_card ?_
            intro a ha
            have haE : E (Fin.insertNth i a rRest) := (Finset.mem_filter.1 ha).2
            let r : Fin (n' + 1) → 𝔽 := Fin.insertNth i a rRest
            have hri : r i = a := by simp [r]
            refine Finset.mem_filter.2 ⟨by simp, ?_⟩
            have h1 := (haE.2).2
            simp only [nextClaim] at h1 ⊢
            rw [Fin.insertNth_apply_same, hg_eq a, hh_eq a] at h1
            exact h1

          exact le_trans hS_le hagree_card

      simpa [E] using
        prob_over_challenges_fiber_le (𝔽 := 𝔽) (n := n') (i := i) (d := maxIndDegree st.polynomial)
          (E := E) (hfiber := hfiber)

-- union bound over all rounds: the total probability of some round having
-- a disagree-but-agree event is ≤ n * maxIndDegree(p) / |𝔽| = soundnessError
theorem sum_accepts_and_round_disagree_but_agree_bound {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
(st : SumcheckProtocolStatement 𝔽 n) (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) :
  (∑ i : Fin n,
      probOverChallenges (𝔽 := 𝔽) (n := n)
        (fun r =>
          AcceptsAndBadTranscriptOnChallenges st P r ∧
          RoundDisagreeButAgreeAtChallenge st P r i))
    ≤ soundnessError st.polynomial := by
  classical
  -- Sum the pointwise bounds.
  have hsum :
      (∑ i : Fin n,
          probOverChallenges (𝔽 := 𝔽) (n := n)
            (fun r =>
              AcceptsAndBadTranscriptOnChallenges st P r ∧
              RoundDisagreeButAgreeAtChallenge st P r i))
        ≤ ∑ i : Fin n, ((maxIndDegree st.polynomial : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ)) := by
    refine Fintype.sum_mono ?_
    intro i
    simpa using
      (prob_single_round_accepts_and_disagree_le (𝔽 := 𝔽) (n := n)
        (st := st) (P := P) (i := i))

  calc
    (∑ i : Fin n,
        probOverChallenges (𝔽 := 𝔽) (n := n)
          (fun r =>
            AcceptsAndBadTranscriptOnChallenges st P r ∧
            RoundDisagreeButAgreeAtChallenge st P r i))
        ≤ ∑ i : Fin n, ((maxIndDegree st.polynomial : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ)) := hsum
    _ = (n : ℚ) * ((maxIndDegree st.polynomial : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ)) := by
      simp
    _ = soundnessError st.polynomial := by
      simp [soundnessError, div_eq_mul_inv, mul_left_comm, mul_comm]

-- contrapositive: if no round is bad, all round polynomials are honest
lemma all_rounds_honest_of_not_bad
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽)
  (t : Transcript 𝔽 n)
  (domain : List 𝔽)
  (hNoBad : ¬ BadTranscriptEvent domain p t) :
  ∀ i : Fin n,
    t.roundPolys i = honestRoundPoly domain (p := p) (ch := t.challenges) i := by
  classical
  intro i
  by_contra hneq
  apply hNoBad
  refine ⟨i, ?_⟩
  simpa [BadRound] using hneq


@[simp] lemma generate_honest_claims_zero
  {𝔽} {n : ℕ} [CommRing 𝔽] [DecidableEq 𝔽]
  (initialClaim : 𝔽)
  (roundPolys : Fin n → CPoly.CMvPolynomial 1 𝔽)
  (challenges : Fin n → 𝔽) :
  generateHonestClaims (n := n) initialClaim roundPolys challenges (0 : Fin (n+1))
    = initialClaim := by
  -- `0 : Fin (n+1)` is definitional equal to `⟨0, Nat.succ_pos n⟩`
  -- so this becomes the definitional equation of generateHonestClaims
  rfl

@[simp] lemma generate_honest_claims_prover_zero
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  generateHonestClaims st.claim (fun i => P.respond st i (challengeSubset r i)) r (0 : Fin (n+1))
    = st.claim := by
  simp

@[simp] lemma proverTranscript_claims_at_zero
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  (proverTranscript st P r).claims st.claim ⟨0, Nat.succ_pos n⟩ = st.claim := by
  simp [proverTranscript, Transcript.claims]


@[simp] lemma proverTranscript_claims_castSucc_zero
  {𝔽 : Type _} {n' : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 (Nat.succ n'))
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := Nat.succ n'))) (r : Fin (Nat.succ n') → 𝔽) :
  (proverTranscript st P r).claims st.claim (Fin.castSucc (⟨0, Nat.succ_pos n'⟩))
    = st.claim := by
  simp [proverTranscript, Transcript.claims]

@[simp] lemma Fin.addCases_left_Fin0
  {α : Type _} {m : ℕ}
  (f : Fin 0 → α) (g : Fin m → α) (i : Fin (0 + m)) :
  Fin.addCases f g i = g (Fin.cast (Nat.zero_add m) i) := by
  cases i with
  | mk k hk =>
      -- hk : k < 0 + m
      -- unfold Fin.addCases and simplify the "k < 0" branch away
      simp [Fin.addCases]


@[simp] lemma addCasesFun_left_Fin0
  {α : Type _} {m : ℕ}
  (f : Fin 0 → α) (g : Fin m → α) :
  addCasesFun f g = (fun i : Fin (0 + m) => g (Fin.cast (Nat.zero_add m) i)) := by
  funext i
  -- unfold addCasesFun to Fin.addCases, then use the simp lemma above
  simp [addCasesFun]

@[simp] lemma Fin.cases_Fin1_apply
  {α : Type _} (a : α) (x : Fin 0 → α) (k : Fin 1) :
  Fin.cases a x k = a := by
  cases k using Fin.cases with
  | zero => rfl
  | succ j =>
      exact (j.elim0)


@[simp] lemma funext_Fin0'
  {α : Type _} (f : Fin 0 → α) :
  f = (fun i => (Fin.elim0 i)) := by
  funext i
  exact (Fin.elim0 i)

@[simp] lemma addCasesFun_Fin0_eq_cons
  {α : Type _} {m : ℕ}
  (g : Fin (m + 1) → α) :
  (fun k : Fin (m + 1) =>
      addCasesFun (fun t : Fin 0 => nomatch t)
        (fun t : Fin (m + 1) => g t)
        (Fin.cast (Nat.zero_add (m+1)).symm k))
    =
  g := by
  funext k
  simp [addCasesFun, Fin.addCases]

@[simp] lemma eval_const0_eq
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => (0 : 𝔽)) q =
    CPoly.CMvPolynomial.eval (fun _ => (0 : 𝔽)) q := by
  rfl

@[simp] lemma eval_const1_eq
  {𝔽 : Type _} [CommRing 𝔽] [DecidableEq 𝔽]
  (q : CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => (1 : 𝔽)) q =
    CPoly.CMvPolynomial.eval (fun _ => (1 : 𝔽)) q := by
  rfl

lemma eval_sum_over_hypercube_recursive
  {𝔽 : Type _} [CommSemiring 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (z : Fin 1 → 𝔽)
  (b0 b1 : 𝔽)
  {m : ℕ}
  (F : (Fin m → 𝔽) → CPoly.CMvPolynomial 1 𝔽) :
  CPoly.CMvPolynomial.eval z
      (sumOverHypercubeRecursive (𝔽 := 𝔽) (β := CPoly.CMvPolynomial 1 𝔽)
        b0 b1 (· + ·) (m := m) F)
    =
  sumOverHypercubeRecursive (𝔽 := 𝔽) (β := 𝔽)
    b0 b1 (· + ·) (m := m) (fun x =>
      CPoly.CMvPolynomial.eval z (F x)) := by
  classical
  exact sum_over_hypercube_recursive_map
    (𝔽 := 𝔽)
    (β := CPoly.CMvPolynomial 1 𝔽)
    (γ := 𝔽)
    (b0 := b0) (b1 := b1)
    (addβ := (· + ·)) (addγ := (· + ·))
    (g := fun q => CPoly.CMvPolynomial.eval z q)
    (hg := fun a b => CPoly.eval_add z a b)
    (m := m)
    (F := F)

@[simp] lemma Fin.cons_eq_cases_const
  {α : Type _} {n : ℕ} (a : α) (x : Fin n → α) :
  (fun i : Fin (n + 1) => (Fin.cons (α := fun _ => α) a x i))
    =
  (fun i : Fin (n + 1) => Fin.cases a x i) := by
  rfl

-- if the verifier accepts and every round polynomial is honest,
-- then the initial claim must equal the honest sum
lemma claim_eq_honest_claim_of_accepts_and_all_rounds_honest
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽)
  (hall :
    ∀ i : Fin n,
      (proverTranscript st P r).roundPolys i
        = honestRoundPoly st.domain (p := st.polynomial) (ch := (proverTranscript st P r).challenges) i)
  (hAcc : AcceptsEvent st.domain st.polynomial st.claim (proverTranscript st P r)) :
  st.claim = honestClaim st.domain (p := st.polynomial) := by
  classical
  let t : Transcript 𝔽 n := proverTranscript st P r

  cases n with
  | zero =>
      have hacc_bool :
          isVerifierAccepts (𝔽 := 𝔽) (n := 0) st.domain st.polynomial st.claim t = true := by
        simpa [AcceptsEvent, t] using hAcc

      have hfinal_ok :
          decide (t.claims st.claim (Fin.last 0) = CPoly.CMvPolynomial.eval t.challenges st.polynomial) = true := by
        simpa [isVerifierAccepts, Transcript.claims, t] using hacc_bool

      have hEq :
          t.claims st.claim (Fin.last 0) = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
        exact of_decide_eq_true hfinal_ok

      have hclaim0 : t.claims st.claim (Fin.last 0) = st.claim := by
        simpa [t] using
          (proverTranscript_claims_at_zero (st := st) (P := P) (r := r))

      have htrue0 :
          honestClaim st.domain (p := st.polynomial) = CPoly.CMvPolynomial.eval (fun i : Fin 0 => i.elim0) st.polynomial := by
        simp [honestClaim, residualSum]

      have hchal0 : t.challenges = (fun i : Fin 0 => i.elim0) := by
        funext i; exact i.elim0

      calc
        st.claim = CPoly.CMvPolynomial.eval (fun i : Fin 0 => i.elim0) st.polynomial := by
          have : st.claim = CPoly.CMvPolynomial.eval t.challenges st.polynomial := by
            have : st.claim = t.claims st.claim (Fin.last 0) := by simpa [hclaim0]
            exact this.trans (hEq.trans (by rfl))
          simpa [hchal0] using this
        _ = honestClaim st.domain (p := st.polynomial) := by
          simp [htrue0]

  | succ n' =>
      let i0 : Fin (Nat.succ n') := ⟨0, Nat.succ_pos n'⟩

      have hround :
          verifierCheck st.domain (indDegreeK st.polynomial i0) (t.claims st.claim i0.castSucc) (t.roundPolys i0) = true ∧
          t.claims st.claim i0.succ = nextClaim (t.challenges i0) (t.roundPolys i0) := by
        simpa [t] using
          acceptsEvent_round_facts (𝔽 := 𝔽) (n := Nat.succ n') st.domain (p := st.polynomial) (claim := st.claim) (t := t) (i := i0) (by
            simpa [t] using hAcc)

      have hcheck :
          verifierCheck st.domain (indDegreeK st.polynomial i0) (t.claims st.claim i0.castSucc) (t.roundPolys i0) = true :=
        hround.1

      -- Turn verifierCheck = true into domain foldl sum identity
      have hsum :
          (st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0
            =
           t.claims st.claim i0.castSucc)
          ∧
          CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ (t.roundPolys i0) ≤ indDegreeK st.polynomial i0 := by
        simpa using
          (verifier_check_eq_true_iff (𝔽 := 𝔽)
            st.domain
            (maxDegree := indDegreeK st.polynomial i0)
            (roundClaim := t.claims st.claim i0.castSucc)
            (roundP := t.roundPolys i0)).1 hcheck

      have hsum0 :
          st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0
          =
          t.claims st.claim i0.castSucc :=
        hsum.1

      -- round 0 poly is honest by hall
      have hi0 :
          t.roundPolys i0 = honestRoundPoly st.domain (p := st.polynomial) (ch := t.challenges) i0 := by
        simpa [t, proverTranscript] using hall i0

      -- claims at castSucc-zero is st.claim
      have hclaim0 : t.claims st.claim i0.castSucc = st.claim := by
        simpa [t] using
          (proverTranscript_claims_castSucc_zero
            (st := st) (P := P) (r := r))

      -- domain foldl of honest round 0 = honestClaim
      have htrue :
          st.domain.foldl (fun acc a =>
            acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
              (honestRoundPoly st.domain (p := st.polynomial) (ch := t.challenges) i0)) 0
          =
          honestClaim st.domain (p := st.polynomial) := by
        simpa [t, i0] using honest_round0_domain_sum_eq_honest_claim st.domain (p := st.polynomial) (r := r)

      -- Finish: st.claim = (domain sum of t.roundPolys 0) = honestClaim
      calc
        st.claim = t.claims st.claim i0.castSucc := by simp [hclaim0]
        _ = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) (t.roundPolys i0)) 0 := by
              symm; exact hsum0
        _ = st.domain.foldl (fun acc a =>
              acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a)
                (honestRoundPoly st.domain (p := st.polynomial) (ch := t.challenges) i0)) 0 := by
              simp [hi0]
        _ = honestClaim st.domain (p := st.polynomial) := htrue

-- key reduction: if the claim is dishonest but the verifier accepts,
-- then some round must have a bad polynomial (contrapositive of completeness)
lemma accepts_on_challenges_dishonest_implies_bad
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽)
  (hDish : st.claim ≠ honestClaim st.domain (p := st.polynomial))
  (hAcc : AcceptsEvent st.domain st.polynomial st.claim (proverTranscript st P r)) :
  BadTranscriptEvent st.domain st.polynomial (proverTranscript st P r) := by
  classical

  -- Pin canonical BEq/LawfulBEq locally (so honestRoundPoly types line up).
  letI : BEq 𝔽 := instBEqOfDecidableEq
  letI : LawfulBEq 𝔽 := by classical exact (inferInstance)

  let t : Transcript 𝔽 n := proverTranscript st P r

  by_contra hNoBad

  -- from ¬BadTranscriptEvent, all rounds are honest
  have hall :
      ∀ i : Fin n,
        t.roundPolys i = honestRoundPoly st.domain (p := st.polynomial) (ch := t.challenges) i :=
    all_rounds_honest_of_not_bad (p := st.polynomial) (t := t) st.domain hNoBad

  -- transport to the exact "hall" shape for the bridge lemma (proverTranscript ...).challenges
  have hall' :
      ∀ i : Fin n,
        (proverTranscript st P r).roundPolys i
          =
        honestRoundPoly st.domain (p := st.polynomial) (ch := (proverTranscript st P r).challenges) i := by
    intro i
    -- t is definitional equal to the prover transcript
    simpa [t] using hall i

  have hEq : st.claim = honestClaim st.domain (p := st.polynomial) :=
    claim_eq_honest_claim_of_accepts_and_all_rounds_honest
      (st := st) (P := P) (r := r)
      (hall := hall') (hAcc := hAcc)

  exact hDish hEq
