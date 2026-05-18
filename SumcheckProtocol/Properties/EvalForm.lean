import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange

import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Multivariate.MvPolyEquiv

import SumcheckProtocol.Src.EvalForm
import SumcheckProtocol.Properties.Lemmas.HonestRoundProofs

/-!
# Evaluation-form honest prover (Phase 1, proofs)

Consistency lemma + Lagrange interpolation corollary for the eval-form
honest prover defined in `SumcheckProtocol/Src/EvalForm.lean`.

* `eval_honestProverMessageAt_eq_honestProverMessageEvalsAt` is the
  consistency lemma: evaluating the symbolic round poly at a field
  point `c` agrees with the eval-form value at `c`.
* `lagrange_interpolate_eq_eval_at_node` is the corollary used by the
  verifier: at any of the `d+1` distinct nodes `xs k`, the Lagrange
  interpolation through `(xs k, evalsAt c)` agrees with the symbolic
  evaluation at that same node.

## Reduction from spec

The spec's interpolation corollary asks for a *pointwise* equality
`eval (fun _ => r) (honestProverMessageAt …) = (interpolate xs evals).eval r`
for every field point `r`, given `d ≥ degreeOf 0 (honestProverMessageAt …)`.
Proving the universal-`r` form requires a noncomputable bridge between
`CPoly.CMvPolynomial 1 𝔽` and Mathlib's `Polynomial 𝔽`. We provide the
bridge here as `toUnivariate`, route it through `MvPolynomial.finOneEquiv`,
and prove

* `eval_toUnivariate` — evaluation coherence,
* `natDegree_toUnivariate_le` — degree-tracking via
  `MvPolynomial.natDegree_finSuccEquiv`.

The universal-`r` corollary `eval_honestProverMessageAt_eq_interpolate_eval`
then follows from `Lagrange.eq_interpolate_of_eval_eq` plus the at-the-nodes
form `lagrange_interpolate_eq_eval_at_node`, which we keep as the operational
statement (the verifier actually only checks the d+1 nodes).
-/

open CPoly

variable {𝔽 : Type _}

/--
Bridge between two equivalent `addCasesFun` shapes of the same
evaluation point: snocing `c` onto the left vs consing `c` onto the
right.

Specialised to `m = numOpenVars i` to avoid `Fin.cast` plumbing — this
is the only shape we actually use in the consistency proof below.
-/
private lemma point_snoc_eq_cons
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽) (c : 𝔽)
  (x : Fin (numOpenVars (n := n) i) → 𝔽) :
  (fun k : Fin n =>
      addCasesFun (Fin.snoc challenges c) x
        (Fin.cast (snoc_split_eq (n := n) i).symm k))
    =
  (fun k : Fin n =>
      addCasesFun
        (fun t : Fin i.val => challenges t)
        (fun t : Fin (numOpenVars (n := n) i + 1) =>
          Fin.cases c x t)
        (Fin.cast (honest_split_eq (n := n) i).symm k)) := by
  classical
  funext k
  have hkn : k.val < n := k.isLt
  by_cases hlt : k.val < i.val
  · -- Position k.val < i.val: both sides return challenges at k.val.
    have hLlt : k.val < i.val + 1 := Nat.lt_of_lt_of_le hlt (Nat.le_succ _)
    have hLfin : (Fin.cast (snoc_split_eq (n := n) i).symm k)
        = Fin.castAdd (numOpenVars (n := n) i) ⟨k.val, hLlt⟩ := by
      apply Fin.ext; rfl
    have hRfin : (Fin.cast (honest_split_eq (n := n) i).symm k)
        = Fin.castAdd (numOpenVars (n := n) i + 1) ⟨k.val, hlt⟩ := by
      apply Fin.ext; rfl
    rw [hLfin, hRfin]
    have hLval : addCasesFun (Fin.snoc challenges c) x
        (Fin.castAdd (numOpenVars (n := n) i) ⟨k.val, hLlt⟩)
          = (Fin.snoc challenges c : Fin (i.val + 1) → 𝔽) ⟨k.val, hLlt⟩ :=
      Fin.addCases_left (motive := fun _ => 𝔽) ⟨k.val, hLlt⟩
    have hRval : addCasesFun
        (fun t : Fin i.val => challenges t)
        (fun t : Fin (numOpenVars (n := n) i + 1) => Fin.cases c x t)
        (Fin.castAdd (numOpenVars (n := n) i + 1) ⟨k.val, hlt⟩)
          = challenges ⟨k.val, hlt⟩ :=
      Fin.addCases_left (motive := fun _ => 𝔽) ⟨k.val, hlt⟩
    rw [hLval, hRval]
    -- Fin.snoc challenges c at index k.val (< i.val) returns challenges at k.val.
    have hcastSucc : (⟨k.val, hLlt⟩ : Fin (i.val + 1))
        = Fin.castSucc ⟨k.val, hlt⟩ := by
      apply Fin.ext; rfl
    rw [hcastSucc, Fin.snoc_castSucc]
  · push_neg at hlt
    by_cases heq : k.val = i.val
    · -- Position is exactly i: both sides yield c.
      have hLlt : k.val < i.val + 1 := by omega
      have hLfin : (Fin.cast (snoc_split_eq (n := n) i).symm k)
          = Fin.castAdd (numOpenVars (n := n) i) ⟨k.val, hLlt⟩ := by
        apply Fin.ext; rfl
      have hRfin : (Fin.cast (honest_split_eq (n := n) i).symm k)
          = Fin.natAdd i.val
              (⟨0, Nat.succ_pos _⟩ : Fin (numOpenVars (n := n) i + 1)) := by
        apply Fin.ext
        show k.val = i.val + 0
        omega
      rw [hLfin, hRfin]
      have hLval : addCasesFun (Fin.snoc challenges c) x
          (Fin.castAdd (numOpenVars (n := n) i) ⟨k.val, hLlt⟩)
            = (Fin.snoc challenges c : Fin (i.val + 1) → 𝔽) ⟨k.val, hLlt⟩ :=
        Fin.addCases_left (motive := fun _ => 𝔽) ⟨k.val, hLlt⟩
      have hRval : addCasesFun
          (fun t : Fin i.val => challenges t)
          (fun t : Fin (numOpenVars (n := n) i + 1) => Fin.cases c x t)
          (Fin.natAdd i.val (⟨0, Nat.succ_pos _⟩ : Fin (numOpenVars (n := n) i + 1)))
            = Fin.cases (motive := fun _ => 𝔽) c x
                (⟨0, Nat.succ_pos _⟩ : Fin (numOpenVars (n := n) i + 1)) :=
        Fin.addCases_right (motive := fun _ => 𝔽) ⟨0, Nat.succ_pos _⟩
      rw [hLval, hRval]
      -- Fin.snoc challenges c at the last position returns c.
      have hsnoc_at_last :
          (Fin.snoc challenges c : Fin (i.val + 1) → 𝔽) ⟨k.val, hLlt⟩ = c := by
        have hkv_eq : (⟨k.val, hLlt⟩ : Fin (i.val + 1)) = Fin.last i.val := by
          apply Fin.ext; exact heq
        rw [hkv_eq, Fin.snoc_last]
      rw [hsnoc_at_last]
      -- Fin.cases c x at index 0 returns c.
      rfl
    · -- Position is strictly past i: k.val > i.val.
      have hgt : i.val < k.val := lt_of_le_of_ne hlt (Ne.symm heq)
      have hLge : i.val + 1 ≤ k.val := hgt
      let dL : ℕ := k.val - (i.val + 1)
      have hdL : dL < numOpenVars (n := n) i := by
        have hke : k.val < (i.val + 1) + numOpenVars (n := n) i := by
          have := snoc_split_eq (n := n) i
          omega
        show k.val - (i.val + 1) < numOpenVars (n := n) i
        omega
      have hLfin : (Fin.cast (snoc_split_eq (n := n) i).symm k)
          = Fin.natAdd (i.val + 1)
              (⟨dL, hdL⟩ : Fin (numOpenVars (n := n) i)) := by
        apply Fin.ext
        show k.val = (i.val + 1) + (k.val - (i.val + 1))
        omega
      let dR : ℕ := k.val - i.val
      have hdR : dR < numOpenVars (n := n) i + 1 := by
        have hk_lt : k.val < i.val + (numOpenVars (n := n) i + 1) := by
          have := honest_split_eq (n := n) i
          omega
        show k.val - i.val < numOpenVars (n := n) i + 1
        omega
      have hRfin : (Fin.cast (honest_split_eq (n := n) i).symm k)
          = Fin.natAdd i.val (⟨dR, hdR⟩ : Fin (numOpenVars (n := n) i + 1)) := by
        apply Fin.ext
        show k.val = i.val + (k.val - i.val)
        omega
      rw [hLfin, hRfin]
      have hLval : addCasesFun (Fin.snoc challenges c) x
          (Fin.natAdd (i.val + 1) ⟨dL, hdL⟩) = x ⟨dL, hdL⟩ :=
        Fin.addCases_right (motive := fun _ => 𝔽) ⟨dL, hdL⟩
      have hdR_ne : dR ≠ 0 := by
        show k.val - i.val ≠ 0
        omega
      have hdR_eq : dR = dL + 1 := by
        show k.val - i.val = (k.val - (i.val + 1)) + 1
        omega
      have hcases_at :
          Fin.cases (motive := fun _ => 𝔽) c x
              (⟨dR, hdR⟩ : Fin (numOpenVars (n := n) i + 1))
            = x ⟨dL, hdL⟩ := by
        have hsubst :
            (⟨dR, hdR⟩ : Fin (numOpenVars (n := n) i + 1))
              = Fin.succ (⟨dL, hdL⟩ : Fin (numOpenVars (n := n) i)) := by
          apply Fin.ext
          show dR = dL + 1
          exact hdR_eq
        rw [hsubst]
        simp
      have hRval : addCasesFun
          (fun t : Fin i.val => challenges t)
          (fun t : Fin (numOpenVars (n := n) i + 1) => Fin.cases c x t)
          (Fin.natAdd i.val ⟨dR, hdR⟩) =
          Fin.cases (motive := fun _ => 𝔽) c x ⟨dR, hdR⟩ :=
        Fin.addCases_right (motive := fun _ => 𝔽) ⟨dR, hdR⟩
      rw [hLval, hRval, hcases_at]

variable [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/--
Consistency lemma: evaluating the symbolic round poly at field point
`c` equals the eval-form value at `c`. This is the operational guarantee
that the eval-form path agrees with the symbolic specification.

Proof outline: extend `challenges` to a full vector `r : Fin n → 𝔽`,
apply `eval_honest_round_poly_eq_sum_eval`, then bridge the two
`addCasesFun` shapes via `point_snoc_eq_cons`.
-/
theorem eval_honestProverMessageAt_eq_honestProverMessageEvalsAt
  {n : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (c : 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => c)
      (honestProverMessageAt domain p i challenges)
    =
  honestProverMessageEvalsAt domain p i challenges c := by
  classical
  let r : Fin n → 𝔽 := fun k =>
    if h : k.val < i.val then challenges ⟨k.val, h⟩ else 0
  have hch : challengeSubset r i = challenges := by
    funext t
    have hlt : t.val < i.val := t.isLt
    show (if h : t.val < i.val then challenges ⟨t.val, h⟩ else 0) = challenges t
    rw [dif_pos hlt]
  -- Apply the heavy lemma with full vector r.
  have hheavy :=
    eval_honest_round_poly_eq_sum_eval (𝔽 := 𝔽) (n := n) domain
      (p := p) (r := r) (i := i) (a := c)
  -- honestRoundPoly is definitionally honestProverMessageAt with challengeSubset.
  -- Combined with hch, it equals honestProverMessageAt with challenges.
  have hLHS :
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => c)
          (honestRoundPoly domain (p := p) (ch := r) i)
        =
      CPoly.CMvPolynomial.eval (fun _ : Fin 1 => c)
          (honestProverMessageAt domain p i challenges) := by
    show CPoly.CMvPolynomial.eval (fun _ : Fin 1 => c)
        (honestProverMessageAt domain p i (challengeSubset r i))
      = CPoly.CMvPolynomial.eval (fun _ : Fin 1 => c)
          (honestProverMessageAt domain p i challenges)
    rw [hch]
  -- Establish the consistency by chaining hLHS and hheavy via transitivity.
  -- Goal: eval (fun _ => c) (honestProverMessageAt domain p i challenges)
  --     = honestProverMessageEvalsAt domain p i challenges c
  refine hLHS.symm.trans (hheavy.trans ?_)
  -- Goal: sumOverDomainRecursive ... (cons-shape) = honestProverMessageEvalsAt ...
  unfold honestProverMessageEvalsAt residualSumWithOpenVars
  apply sum_over_domain_recursive_congr
  intro x
  congr 1
  -- The challengeSubset form (using r) equals challenges.
  have hch_pt :
      (fun t : Fin i.val => r ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) = challenges := by
    funext t
    have hlt : t.val < i.val := t.isLt
    show (if h : t.val < i.val then challenges ⟨t.val, h⟩ else 0) = challenges t
    rw [dif_pos hlt]
  rw [hch_pt]
  -- The honestSplitEqCast identity is propositionally equal to honest_split_eq for m = numOpenVars i.
  have hsplit_cast :
      honestSplitEqCast (n := n) i (numOpenVars (n := n) i) rfl
        = honest_split_eq (n := n) i := rfl
  rw [hsplit_cast]
  -- Apply the helper: snoc-form = cons-form.
  exact (point_snoc_eq_cons (n := n) i challenges c x).symm

/--
Pointwise interpolation corollary at the interpolation nodes.

Given `d+1` distinct points `xs : Fin (d+1) → 𝔽`, the Lagrange
interpolant through `(xs k, evals)` agrees with the symbolic round poly
at every node `xs k`, where
`evals k = honestProverMessageEvalsAt … (xs k)`.

Operationally this is what the verifier needs: it samples the prover's
evaluation tuple, builds the Lagrange interpolant, and queries it at
its own challenge — a quantity that is itself the Lagrange interpolation
evaluated at the challenge. The pointwise statement here is the key
correctness ingredient: at each of the `d+1` nodes the interpolation
value matches the symbolic eval, by `Lagrange.eval_interpolate_at_node`
plus the consistency lemma above.

(See the file-level docstring for why we reduce the spec's universal-`r`
form to this nodewise form.)
-/
theorem lagrange_interpolate_eq_eval_at_node
  {n d : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (xs : Fin (d + 1) → 𝔽)
  (hxs : Set.InjOn xs (Finset.univ : Finset (Fin (d + 1))))
  (k : Fin (d + 1)) :
  (Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) xs
      (fun j => honestProverMessageEvalsAt domain p i challenges (xs j))).eval (xs k)
    =
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => xs k)
      (honestProverMessageAt domain p i challenges) := by
  classical
  rw [eval_honestProverMessageAt_eq_honestProverMessageEvalsAt]
  exact Lagrange.eval_interpolate_at_node
    (v := xs)
    (r := fun j => honestProverMessageEvalsAt domain p i challenges (xs j))
    hxs (Finset.mem_univ k)

/-! ### Univariate bridge for the universal-`r` interpolation form

To upgrade the at-the-nodes corollary to the universal-`r` form, we
bridge `CPoly.CMvPolynomial 1 𝔽` to Mathlib's univariate `Polynomial 𝔽`
via `MvPolynomial.finOneEquiv`. The bridge is noncomputable, but for
the proof obligations we only need:

* evaluation coherence (`eval_toUnivariate`),
* `natDegree` is bounded by `degreeOf 0` (`natDegree_toUnivariate_le`),

both of which follow from `MvPolynomial.eval_eq_eval_mv_eval'`,
`MvPolynomial.natDegree_finSuccEquiv`, and
`Polynomial.natDegree_map_eq_of_injective`.
-/

/-- Bridge `CMvPolynomial 1 𝔽 → Polynomial 𝔽` via `fromCMvPolynomial`
followed by `MvPolynomial.finOneEquiv`. Noncomputable. -/
noncomputable def toUnivariate (q : CPoly.CMvPolynomial 1 𝔽) : Polynomial 𝔽 :=
  MvPolynomial.finOneEquiv 𝔽 (CPoly.fromCMvPolynomial q)

omit [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] in
private lemma const_one_eq_finCons (r : 𝔽) :
    (fun _ : Fin 1 => r) = (Fin.cons r Fin.elim0 : Fin (0 + 1) → 𝔽) := by
  funext i
  fin_cases i; rfl

omit [Fintype 𝔽] [DecidableEq 𝔽] in
private lemma eval_finOneEquiv (q : MvPolynomial (Fin 1) 𝔽) (r : 𝔽) :
    Polynomial.eval r (MvPolynomial.finOneEquiv 𝔽 q)
      = MvPolynomial.eval (fun _ => r) q := by
  classical
  -- Use `eval_eq_eval_mv_eval'` with `s := Fin.elim0`.
  have hsplit :=
    MvPolynomial.eval_eq_eval_mv_eval' (R := 𝔽) (n := 0) (s := Fin.elim0) (y := r) q
  -- Rewrite (fun _ => r) into Fin.cons form.
  have hcons : MvPolynomial.eval (fun _ : Fin 1 => r) q
      = MvPolynomial.eval (Fin.cons r Fin.elim0 : Fin (0 + 1) → 𝔽) q := by
    rw [const_one_eq_finCons (𝔽 := 𝔽) r]
  rw [hcons, hsplit]
  -- Goal: Polynomial.eval r (finOneEquiv 𝔽 q)
  --     = Polynomial.eval r (Polynomial.map (eval Fin.elim0) (finSuccEquiv 𝔽 0 q))
  -- finOneEquiv = (finSuccEquiv 0).trans (mapAlgEquiv (isEmptyAlgEquiv 𝔽 (Fin 0))).
  -- Both ring homs MvPolynomial (Fin 0) 𝔽 → 𝔽 (the AlgEquiv image and `eval Fin.elim0`)
  -- agree on `C a` and have empty variable set, so they're equal as ring homs.
  unfold MvPolynomial.finOneEquiv
  have hRingEq : ((MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toAlgHom : _ →+* _)
      = MvPolynomial.eval (Fin.elim0 : Fin 0 → 𝔽) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; exact i.elim0
  simp only [AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv]
  -- Now we need Polynomial.map of two equal ring homs to give the same result.
  rw [show (((MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)) : _ →+* _) : _ →+* _)
        = MvPolynomial.eval (Fin.elim0 : Fin 0 → 𝔽) from hRingEq]

omit [Fintype 𝔽] [DecidableEq 𝔽] in
/-- Evaluation coherence for the univariate bridge. -/
lemma eval_toUnivariate (q : CPoly.CMvPolynomial 1 𝔽) (r : 𝔽) :
    Polynomial.eval r (toUnivariate q)
      = CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r) q := by
  classical
  unfold toUnivariate
  rw [eval_finOneEquiv]
  -- CPoly.eval_equiv: q.eval vals = (fromCMvPolynomial q).eval vals
  exact (CPoly.eval_equiv (R := 𝔽) (n := 1) (p := q) (vals := fun _ => r)).symm

omit [Fintype 𝔽] [DecidableEq 𝔽] in
/-- `natDegree` of the univariate bridge is bounded by `degreeOf 0`. -/
lemma natDegree_toUnivariate_le (q : CPoly.CMvPolynomial 1 𝔽) :
    (toUnivariate q).natDegree ≤ CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q := by
  classical
  unfold toUnivariate
  -- finOneEquiv = (finSuccEquiv 0).trans (mapAlgEquiv (isEmptyAlgEquiv 𝔽 (Fin 0)))
  unfold MvPolynomial.finOneEquiv
  -- After unfolding, the value equals
  --   Polynomial.map (isEmptyAlgEquiv 𝔽 (Fin 0)) (finSuccEquiv 𝔽 0 (fromCMvPolynomial q))
  -- so its natDegree equals (finSuccEquiv …).natDegree by injectivity of the map.
  have hMap :
      (Polynomial.map (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.toRingHom
        (MvPolynomial.finSuccEquiv (R := 𝔽) 0
          (CPoly.fromCMvPolynomial (R := 𝔽) q))).natDegree
        = (MvPolynomial.finSuccEquiv (R := 𝔽) 0
            (CPoly.fromCMvPolynomial (R := 𝔽) q)).natDegree := by
    apply Polynomial.natDegree_map_eq_of_injective
    exact (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.injective
  -- Identify `(MvPolynomial.finSuccEquiv 𝔽 0 _).natDegree` with `degreeOf 0 _`.
  have hSucc :
      (MvPolynomial.finSuccEquiv (R := 𝔽) 0
        (CPoly.fromCMvPolynomial (R := 𝔽) q)).natDegree
        = MvPolynomial.degreeOf (R := 𝔽) (σ := Fin 1) 0
            (CPoly.fromCMvPolynomial (R := 𝔽) q) :=
    MvPolynomial.natDegree_finSuccEquiv (R := 𝔽) (n := 0)
      (CPoly.fromCMvPolynomial (R := 𝔽) q)
  -- Bridge MvPolynomial.degreeOf back to CPoly.CMvPolynomial.degreeOf.
  have hCPoly : MvPolynomial.degreeOf (R := 𝔽) (σ := Fin 1) 0
      (CPoly.fromCMvPolynomial (R := 𝔽) q)
      = CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q :=
    (congrArg (fun f => f (0 : Fin 1))
      (CPoly.degreeOf_equiv (p := q) (S := 𝔽))).symm
  -- Reduce the goal to `_ ≤ _` via the equalities above.
  show (Polynomial.map (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.toRingHom
        (MvPolynomial.finSuccEquiv (R := 𝔽) 0
          (CPoly.fromCMvPolynomial (R := 𝔽) q))).natDegree
      ≤ CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
  rw [hMap, hSucc, hCPoly]

/--
Universal-`r` interpolation corollary (Phase 1 follow-up).

Under the degree hypothesis `degreeOf 0 (honestProverMessageAt … ) ≤ d`,
for **every** field point `r : 𝔽`, the symbolic round polynomial
evaluated at `r` agrees with the Lagrange interpolation through the
`d+1` evaluation pairs `(xs k, evals (xs k))` evaluated at `r`.

Proof: bridge to `Polynomial 𝔽` via `toUnivariate`, where eval and
degree both agree (`eval_toUnivariate`, `natDegree_toUnivariate_le`).
Then the Lagrange uniqueness lemma `Lagrange.eq_interpolate_of_eval_eq`
identifies the bridge with the Lagrange interpolant.
-/
theorem eval_honestProverMessageAt_eq_interpolate_eval
  {n d : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (xs : Fin (d + 1) → 𝔽)
  (hxs : Set.InjOn xs (Finset.univ : Finset (Fin (d + 1))))
  (hdeg :
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
      (honestProverMessageAt domain p i challenges) ≤ d)
  (r : 𝔽) :
  CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r)
      (honestProverMessageAt domain p i challenges)
    =
  (Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) xs
      (fun k =>
        honestProverMessageEvalsAt domain p i challenges (xs k))).eval r := by
  classical
  set P := honestProverMessageAt domain p i challenges with hP
  set Pu := toUnivariate P with hPu
  -- Pu.natDegree ≤ d, so Pu.degree < d + 1 = (Finset.univ : Finset (Fin (d+1))).card.
  have hNat : Pu.natDegree ≤ d := by
    have := natDegree_toUnivariate_le (𝔽 := 𝔽) (q := P)
    exact le_trans this hdeg
  have hCard : ((Finset.univ : Finset (Fin (d + 1))) : Finset (Fin (d + 1))).card = d + 1 := by
    simp
  have hDeg : Pu.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [hCard]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree)
      (by exact_mod_cast Nat.lt_succ_of_le hNat)
  -- Eval coherence at every node.
  have hEvalNode : ∀ k ∈ (Finset.univ : Finset (Fin (d + 1))),
      Polynomial.eval (xs k) Pu
        = honestProverMessageEvalsAt domain p i challenges (xs k) := by
    intro k _
    rw [hPu, eval_toUnivariate, hP,
        eval_honestProverMessageAt_eq_honestProverMessageEvalsAt]
  -- Apply Lagrange uniqueness: Pu = interpolate Finset.univ xs values.
  have hInterp :
      Pu = Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) xs
            (fun k => honestProverMessageEvalsAt domain p i challenges (xs k)) :=
    Lagrange.eq_interpolate_of_eval_eq
      (r := fun k => honestProverMessageEvalsAt domain p i challenges (xs k))
      hxs hDeg hEvalNode
  -- Evaluate both sides at r and use eval coherence on the LHS.
  have hLHS : CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r) P
      = Polynomial.eval r Pu := by
    rw [hPu, eval_toUnivariate]
  rw [show CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r)
      (honestProverMessageAt domain p i challenges)
      = CPoly.CMvPolynomial.eval (fun _ : Fin 1 => r) P from by rfl]
  rw [hLHS, hInterp]
