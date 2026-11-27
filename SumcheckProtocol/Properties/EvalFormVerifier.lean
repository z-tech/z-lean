import SumcheckProtocol.Src.EvalFormVerifier
import SumcheckProtocol.Properties.Theorems.Completeness

/-!
# Evaluation-form verifier: equivalence with the symbolic verifier

Results about `isEvalVerifierAccepts` (`Src/EvalFormVerifier.lean`).

* `isEvalVerifierAccepts_eq_decode` — for **every** evaluation-form
  transcript (adversarial values, lists of any length, any stop round
  `k`), the evaluation-form verdict equals the symbolic verdict on the
  decoded transcript `t.decode`.
* `isVerifierAccepts_eq_encode` — for every symbolic transcript whose
  round polynomials meet the round degree bounds, the symbolic verdict
  equals the evaluation-form verdict on its node values.
* `isEvalVerifierAccepts_encode_of_accepts` — the degree hypothesis is
  implied by symbolic acceptance, so every accepted symbolic transcript is
  accepted in evaluation form.
* `honest_eval_accepts_on_challenges_k` — evaluation-form completeness of
  the honest prover, transferred from `honest_accepts_on_challenges_k`.

Decoding uses Mathlib's `Lagrange.interpolate` on proof side only; the
verifier evaluates with `BarycentricDomain.eval`, proved equal to it by
CompPoly (`BarycentricDomain.eval_eq_interpolate_eval`). Uniqueness of
the interpolant for the encode direction is `Lagrange.eq_interpolate`.
-/

open CompPoly.CPolynomial.CLagrange (BarycentricDomain)

namespace EvalFormVerifier

-- The bridge lemmas do not use `DecidableEq`; the verifier does.
set_option linter.unusedSectionVars false

variable {𝔽 : Type*} [Field 𝔽] [DecidableEq 𝔽]

/-! ## Boundary parser -/

lemma tupleOf?_ofFn {d : ℕ} (f : Fin (d + 1) → 𝔽) : tupleOf? d (List.ofFn f) = some f := by
  have h : (List.ofFn f).toArray.size = d + 1 := by simp
  unfold tupleOf?
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  funext j
  simp only [List.getElem_toArray, List.getElem_ofFn]

/-! ## Univariate bridge

A `CMvPolynomial 1 𝔽` is a univariate polynomial: transport along
`CPoly.fromCMvPolynomial` and `MvPolynomial.uniqueAlgEquiv`. Both maps
preserve evaluation, and the degree in the single variable is the natural
degree. -/

/-- The univariate polynomial `P` as a one-variable `CMvPolynomial`
(proof side only). -/
noncomputable def ofUnivariate (P : Polynomial 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.toCMvPolynomial ((MvPolynomial.uniqueAlgEquiv 𝔽 (Fin 1)).symm P)

/-- A one-variable `CMvPolynomial` as a univariate polynomial. -/
noncomputable def toUnivariate (q : CPoly.CMvPolynomial 1 𝔽) : Polynomial 𝔽 :=
  MvPolynomial.uniqueAlgEquiv 𝔽 (Fin 1) (CPoly.fromCMvPolynomial q)

lemma eval_uniqueAlgEquiv (P : MvPolynomial (Fin 1) 𝔽) (r : 𝔽) :
    (MvPolynomial.uniqueAlgEquiv 𝔽 (Fin 1) P).eval r = MvPolynomial.eval (fun _ => r) P := by
  rw [Polynomial.eval, MvPolynomial.eval₂_uniqueAlgEquiv (a := fun _ => r)]
  rfl

lemma eval_ofUnivariate (P : Polynomial 𝔽) (r : 𝔽) :
    CPoly.CMvPolynomial.eval (fun _ => r) (ofUnivariate P) = P.eval r := by
  rw [ofUnivariate, CPoly.eval_equiv, CPoly.fromCMvPolynomial_toCMvPolynomial,
    ← eval_uniqueAlgEquiv, AlgEquiv.apply_symm_apply]

lemma eval_toUnivariate (q : CPoly.CMvPolynomial 1 𝔽) (r : 𝔽) :
    (toUnivariate q).eval r = CPoly.CMvPolynomial.eval (fun _ => r) q := by
  rw [toUnivariate, eval_uniqueAlgEquiv, CPoly.eval_equiv]

/-- In one variable, `degreeOf` is the natural degree. -/
lemma degreeOf_eq_natDegree_uniqueAlgEquiv (P : MvPolynomial (Fin 1) 𝔽) :
    MvPolynomial.degreeOf 0 P = (MvPolynomial.uniqueAlgEquiv 𝔽 (Fin 1) P).natDegree := by
  apply le_antisymm
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    apply Polynomial.le_natDegree_of_ne_zero
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    have hm' : m = Finsupp.single default (m 0) := Finsupp.unique_single m
    rw [← hm']
    exact MvPolynomial.mem_support_iff.mp hm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    by_contra hne
    have hmem : Finsupp.single default N ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
    have hle := (MvPolynomial.degreeOf_le_iff (n := 0) (f := P)).mp le_rfl _ hmem
    have h0 : (Finsupp.single (default : Fin 1) N) 0 = N := Finsupp.single_eq_same
    rw [h0] at hle
    omega

lemma degreeOf_ofUnivariate (P : Polynomial 𝔽) :
    CPoly.CMvPolynomial.degreeOf 0 (ofUnivariate P) = P.natDegree := by
  rw [congrFun (CPoly.degreeOf_equiv (S := 𝔽)) 0, ofUnivariate,
    CPoly.fromCMvPolynomial_toCMvPolynomial, degreeOf_eq_natDegree_uniqueAlgEquiv,
    AlgEquiv.apply_symm_apply]

lemma natDegree_toUnivariate (q : CPoly.CMvPolynomial 1 𝔽) :
    (toUnivariate q).natDegree = CPoly.CMvPolynomial.degreeOf 0 q := by
  rw [congrFun (CPoly.degreeOf_equiv (S := 𝔽)) 0, toUnivariate,
    degreeOf_eq_natDegree_uniqueAlgEquiv]

/-! ## Interpolant degree -/

lemma injOn_nodes {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1)) :
    Set.InjOn D.nodes ↑(Finset.univ : Finset (Fin (d + 1))) :=
  fun _ _ _ _ h => D.nodes_injective h

/-- `d + 1` values on distinct nodes have an interpolant of degree at most `d`. -/
lemma natDegree_interpolate_le {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1)) (y : Fin (d + 1) → 𝔽) :
    (Lagrange.interpolate Finset.univ D.nodes y).natDegree ≤ d := by
  have h := Lagrange.degree_interpolate_lt y (injOn_nodes D)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp h N hN

/-! ## Decoding

A well-formed list decodes to its Lagrange interpolant. A malformed list
decodes to `X^(d+1)`, which the symbolic verifier rejects by its degree
check, as the evaluation-form verifier rejects the list by its length
check (`isVerifierAccepts_eq_false_of_round`,
`isEvalVerifierAccepts_eq_false_of_malformed`). Decoding round `i` reads
only round `i`'s list, not its challenge. -/

/-- Univariate decoding of a received list. -/
noncomputable def decodeUnivariate {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    (ys : List 𝔽) : Polynomial 𝔽 :=
  match tupleOf? d ys with
  | some y => Lagrange.interpolate Finset.univ D.nodes y
  | none => Polynomial.X ^ (d + 1)

/-- Symbolic round polynomial decoded from a received list. -/
noncomputable def decodeMessage {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    (ys : List 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  ofUnivariate (decodeUnivariate D ys)

lemma eval_decodeMessage_of_some {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    {ys : List 𝔽} {y : Fin (d + 1) → 𝔽} (h : tupleOf? d ys = some y) (a : 𝔽) :
    CPoly.CMvPolynomial.eval (fun _ => a) (decodeMessage D ys) = D.eval y a := by
  rw [decodeMessage, eval_ofUnivariate]
  simp only [decodeUnivariate, h]
  exact (D.eval_eq_interpolate_eval y a).symm

/-- On a well-formed list, the decoded polynomial at the challenge is the
evaluation-form next claim. -/
lemma nextClaim_decodeMessage_of_some {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    {ys : List 𝔽} {y : Fin (d + 1) → 𝔽} (h : tupleOf? d ys = some y) (r : 𝔽) :
    nextClaim r (decodeMessage D ys) = evalMessage D ys r := by
  rw [nextClaim, eval_decodeMessage_of_some D h, evalMessage, h]

lemma evalVerifierCheck_of_none {d : ℕ} (domain : List 𝔽) (D : BarycentricDomain 𝔽 (d + 1))
    (roundClaim : 𝔽) {ys : List 𝔽} (h : tupleOf? d ys = none) :
    evalVerifierCheck domain D roundClaim ys = false := by
  simp [evalVerifierCheck, h]

/-- The symbolic round check on the decoded polynomial is the
evaluation-form round check, for every received list and claim. -/
lemma verifierCheck_decodeMessage {d : ℕ} (domain : List 𝔽) (D : BarycentricDomain 𝔽 (d + 1))
    (roundClaim : 𝔽) (ys : List 𝔽) :
    verifierCheck domain d roundClaim (decodeMessage D ys) =
      evalVerifierCheck domain D roundClaim ys := by
  cases h : tupleOf? d ys with
  | none =>
      have hdeg : CPoly.CMvPolynomial.degreeOf 0 (decodeMessage D ys) = d + 1 := by
        rw [decodeMessage, degreeOf_ofUnivariate]
        simp only [decodeUnivariate, h]
        exact Polynomial.natDegree_X_pow (d + 1)
      simp [verifierCheck, evalVerifierCheck_of_none domain D roundClaim h, hdeg]
  | some y =>
      have hdeg : CPoly.CMvPolynomial.degreeOf 0 (decodeMessage D ys) ≤ d := by
        rw [decodeMessage, degreeOf_ofUnivariate]
        simp only [decodeUnivariate, h]
        exact natDegree_interpolate_le D y
      simp [verifierCheck, evalVerifierCheck, h, hdeg, eval_decodeMessage_of_some D h]

/-! ## Simulation -/

/-- The two verifiers agree on transcripts whose rounds agree: equal
challenges, equal round verdicts for every claim, and equal values at the
challenge. The claims of round `i + 1` depend only on round `i`, so no
induction over rounds is needed. -/
theorem isEvalVerifierAccepts_eq_of_rounds [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k)) (initialClaim : 𝔽)
    (t : EvalTranscript 𝔽 k.val) (s : Transcript 𝔽 k.val)
    (hch : s.challenges = t.challenges)
    (hcheck : ∀ i c, verifierCheck domain (roundDegree p k i) c (s.roundPolys i) =
      evalVerifierCheck domain (nodes i) c (t.roundEvals i))
    (hnext : ∀ i, nextClaim (t.challenges i) (s.roundPolys i) =
      evalMessage (nodes i) (t.roundEvals i) (t.challenges i)) :
    isEvalVerifierAccepts k domain p nodes initialClaim t =
      isVerifierAccepts k domain p initialClaim s := by
  have hclaims : t.claims (roundDegree p k) nodes initialClaim = s.claims initialClaim := by
    funext ⟨j, hj⟩
    cases j with
    | zero => rfl
    | succ j =>
        simp only [EvalTranscript.claims, Transcript.claims, generateHonestClaims]
        rw [← hnext, hch]
  unfold isEvalVerifierAccepts isVerifierAccepts
  simp only [hclaims, ← hcheck, ← hnext, hch]
  rfl

/-! ## Rejection of malformed rounds -/

/-- The evaluation-form verifier rejects a transcript with a malformed
round, whatever the other rounds and the claims. -/
theorem isEvalVerifierAccepts_eq_false_of_malformed {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k)) (initialClaim : 𝔽)
    (t : EvalTranscript 𝔽 k.val) (i : Fin k.val)
    (h : tupleOf? (roundDegree p k i) (t.roundEvals i) = none) :
    isEvalVerifierAccepts k domain p nodes initialClaim t = false := by
  unfold isEvalVerifierAccepts
  rw [Bool.and_eq_false_iff]
  left
  apply Bool.eq_false_iff.mpr
  intro hall
  have hi := List.all_eq_true.mp hall i (List.mem_finRange i)
  simp [evalVerifierCheck_of_none domain (nodes i) _ h] at hi

/-- The symbolic verifier rejects a transcript with a round that fails its
check for every claim. -/
theorem isVerifierAccepts_eq_false_of_round [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (initialClaim : 𝔽) (s : Transcript 𝔽 k.val) (i : Fin k.val)
    (h : ∀ c, verifierCheck domain (roundDegree p k i) c (s.roundPolys i) = false) :
    isVerifierAccepts k domain p initialClaim s = false := by
  unfold isVerifierAccepts
  rw [Bool.and_eq_false_iff]
  left
  apply Bool.eq_false_iff.mpr
  intro hall
  have hi := List.all_eq_true.mp hall i (List.mem_finRange i)
  have hc := h (s.claims initialClaim (Fin.castSucc i))
  simp only [roundDegree] at hc
  rw [hc, Bool.false_and] at hi
  exact Bool.false_ne_true hi

/-! ## Representation theorem: decoding -/

/-- The symbolic transcript decoded from an evaluation-form transcript,
with round degree bounds `deg`. Round `i` depends only on round `i`'s
list. -/
noncomputable def _root_.EvalTranscript.decode {n : ℕ} (t : EvalTranscript 𝔽 n)
    (deg : Fin n → ℕ) (nodes : RoundNodes 𝔽 deg) : Transcript 𝔽 n where
  roundPolys i := decodeMessage (nodes i) (t.roundEvals i)
  challenges := t.challenges

/-- **Representation theorem.** For every evaluation-form transcript — any
received values, lists of any length, any stop round `k` — the
evaluation-form verdict is the symbolic verdict on the decoded transcript. -/
theorem isEvalVerifierAccepts_eq_decode [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k)) (initialClaim : 𝔽) (t : EvalTranscript 𝔽 k.val) :
    isEvalVerifierAccepts k domain p nodes initialClaim t =
      isVerifierAccepts k domain p initialClaim (t.decode (roundDegree p k) nodes) := by
  by_cases hwf : ∀ i, ∃ y, tupleOf? (roundDegree p k i) (t.roundEvals i) = some y
  · -- Well-formed: the rounds agree, so the verdicts agree.
    exact isEvalVerifierAccepts_eq_of_rounds k domain p nodes initialClaim t
      (t.decode (roundDegree p k) nodes) rfl
      (fun i c => verifierCheck_decodeMessage domain (nodes i) c (t.roundEvals i))
      (fun i => nextClaim_decodeMessage_of_some (nodes i) (hwf i).choose_spec _)
  · -- Malformed round `i`: both verifiers reject.
    push Not at hwf
    obtain ⟨i, hi⟩ := hwf
    have hnone : tupleOf? (roundDegree p k i) (t.roundEvals i) = none :=
      Option.eq_none_iff_forall_ne_some.mpr hi
    rw [isEvalVerifierAccepts_eq_false_of_malformed k domain p nodes initialClaim t i hnone,
      isVerifierAccepts_eq_false_of_round k domain p initialClaim
        (t.decode (roundDegree p k) nodes) i fun c =>
        (verifierCheck_decodeMessage domain (nodes i) c (t.roundEvals i)).trans
          (evalVerifierCheck_of_none domain (nodes i) c hnone)]

/-! ## Encoding direction -/

lemma degree_toUnivariate_lt {d : ℕ} {q : CPoly.CMvPolynomial 1 𝔽}
    (hq : CPoly.CMvPolynomial.degreeOf 0 q ≤ d) :
    (toUnivariate q).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
  rw [Finset.card_univ, Fintype.card_fin]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  rw [natDegree_toUnivariate]
  exact_mod_cast Nat.lt_succ_of_le hq

/-- Uniqueness: a round polynomial meeting the degree bound is reproduced
everywhere by the barycentric interpolant of its node values. -/
lemma evalMessage_encodeMessage {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    {q : CPoly.CMvPolynomial 1 𝔽} (hq : CPoly.CMvPolynomial.degreeOf 0 q ≤ d) (r : 𝔽) :
    evalMessage D (encodeMessage D q) r = nextClaim r q := by
  have huniq := Lagrange.eq_interpolate (injOn_nodes D) (degree_toUnivariate_lt hq)
  simp only [eval_toUnivariate] at huniq
  rw [evalMessage, encodeMessage, tupleOf?_ofFn]
  dsimp only
  rw [D.eval_eq_interpolate_eval, ← huniq, eval_toUnivariate, nextClaim]

lemma evalVerifierCheck_encodeMessage {d : ℕ} (domain : List 𝔽)
    (D : BarycentricDomain 𝔽 (d + 1)) (roundClaim : 𝔽)
    {q : CPoly.CMvPolynomial 1 𝔽} (hq : CPoly.CMvPolynomial.degreeOf 0 q ≤ d) :
    evalVerifierCheck domain D roundClaim (encodeMessage D q) =
      verifierCheck domain d roundClaim q := by
  have hval : ∀ a, evalMessage D (encodeMessage D q) a =
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) q := evalMessage_encodeMessage D hq
  have ht : tupleOf? d (encodeMessage D q) =
      some fun j => CPoly.CMvPolynomial.eval (fun _ => D.nodes j) q := tupleOf?_ofFn _
  have hval' : ∀ a, D.eval (fun j => CPoly.CMvPolynomial.eval (fun _ => D.nodes j) q) a =
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) q := fun a => by
    have := hval a
    rwa [evalMessage, ht] at this
  simp only [evalVerifierCheck, ht]
  simp [verifierCheck, hval', hq]

/-- **Encoding direction.** A symbolic transcript whose round polynomials
meet the round degree bounds has the same verdict as its node values.
The degree hypothesis cannot be dropped: node values forget the excess
degree that the symbolic verifier rejects. -/
theorem isVerifierAccepts_eq_encode [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k)) (initialClaim : 𝔽) (t : Transcript 𝔽 k.val)
    (hdeg : ∀ i, CPoly.CMvPolynomial.degreeOf 0 (t.roundPolys i) ≤ roundDegree p k i) :
    isVerifierAccepts k domain p initialClaim t =
      isEvalVerifierAccepts k domain p nodes initialClaim (t.encode (roundDegree p k) nodes) :=
  (isEvalVerifierAccepts_eq_of_rounds k domain p nodes initialClaim _ t rfl
    (fun i c => (evalVerifierCheck_encodeMessage domain _ c (hdeg i)).symm)
    (fun i => (evalMessage_encodeMessage _ (hdeg i) _).symm)).symm

/-- Symbolic acceptance implies the round degree bounds. -/
lemma degreeOf_le_of_accepts [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (initialClaim : 𝔽) (t : Transcript 𝔽 k.val)
    (h : isVerifierAccepts k domain p initialClaim t = true) (i : Fin k.val) :
    CPoly.CMvPolynomial.degreeOf 0 (t.roundPolys i) ≤ roundDegree p k i :=
  ((verifier_check_eq_true_iff _ _ _ _).mp
    (acceptsEvent_round_facts_k k domain p initialClaim t i h).1).2

/-- Every transcript accepted by the symbolic verifier is accepted, after
encoding, by the evaluation-form verifier. -/
theorem isEvalVerifierAccepts_encode_of_accepts [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k)) (initialClaim : 𝔽) (t : Transcript 𝔽 k.val)
    (h : isVerifierAccepts k domain p initialClaim t = true) :
    isEvalVerifierAccepts k domain p nodes initialClaim (t.encode (roundDegree p k) nodes) = true := by
  rw [← isVerifierAccepts_eq_encode k domain p nodes initialClaim t
    (degreeOf_le_of_accepts k domain p initialClaim t h)]
  exact h

/-- **Evaluation-form completeness.** For every stop round `k` and every
challenge vector, the honest prover's messages, sent as node values, are
accepted by the evaluation-form verifier. -/
theorem honest_eval_accepts_on_challenges_k [Fintype 𝔽] {n : ℕ}
    (k : Fin (n + 1)) (st : SumcheckProtocolStatement 𝔽 n)
    (hclaim : st.claim = honestClaim st.domain st.polynomial)
    (nodes : RoundNodes 𝔽 (roundDegree st.polynomial k)) (r : Fin k.val → 𝔽) :
    isEvalVerifierAccepts k st.domain st.polynomial nodes st.claim
      ((proverTranscript k st (sumcheckHonestProver k) r).encode
        (roundDegree st.polynomial k) nodes) = true :=
  isEvalVerifierAccepts_encode_of_accepts k st.domain st.polynomial nodes st.claim _
    ((AcceptsOnChallenges_unfold k st (sumcheckHonestProver k) r).mp
      (honest_accepts_on_challenges_k k st hclaim r))

end EvalFormVerifier
