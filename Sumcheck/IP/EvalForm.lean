import InteractiveProtocol.Src.Protocol
import Sumcheck.Src
import Sumcheck.Properties.EvalForm
import Sumcheck.IP.Statement

/-!
# IP-native eval-form sumcheck instance (Phase 4)

A parallel `PublicCoinProtocol` instance whose `ProverMessage` is the
round polynomial in **evaluation form** `Fin (d+1) → 𝔽` (the round
polynomial's values at `d+1` interpolation nodes), rather than the
symbolic `CMvPolynomial 1 𝔽`.

## Layer overview

* `SumcheckStatementEvalForm` bundles the claim, the multivariate poly,
  the global degree bound `d`, the `d+1` interpolation nodes, and a
  proof that the verifier's domain is a subset of the node image.
* `sumcheckProtocolEvalForm` is the `PublicCoinProtocol` instance:
  per-round messages live in `Fin (d+1) → 𝔽`; the verifier reconstructs
  the round polynomial by Lagrange interpolation only when it needs to
  evaluate at the verifier's challenge.
* `sumcheckHonestProverEvalForm` ships round messages computed via the
  Phase-1 deliverable `honestProverMessageEvalsAt` — pure sums over the
  domain, no symbolic-polynomial allocation.

## Reduction to the symbolic instance

We provide an explicit transcript-level mapping
`evalFormToSymbolicTranscript` that converts an eval-form transcript to
a symbolic one by Lagrange-interpolating each round's eval tuple. The
direct iff between the two verifiers' acceptance Props requires a
non-trivial univariate ↔ multivariate-1 polynomial bridge (the
"type-conversion swamp" from Phase 1's spec) which is left to a
follow-up phase.

The deliverables here therefore stop at the **floor** scoped in the
plan: definitions for the protocol instance, transcript shape, honest
prover, verifier, and the Lagrange-evaluation key lemma at the
interpolation nodes.
-/

open CPoly

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-- Statement bundle for the eval-form instance.

A uniform global degree `d` is used (rather than per-round), because
`PublicCoinProtocol.ProverMessage : Fin n → Type*` cannot depend on the
statement value — Lean's universe / motive constraints force the type
of each round's message to be determined by `n` and `d` alone. For
sumcheck the natural per-round bound `indDegreeK polynomial i` is
upper-bounded by any global `d` satisfying `degree_le`, so this is
strictly an upper bound, not a structural restriction. -/
structure SumcheckStatementEvalForm
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n d : ℕ) where
  domain         : List 𝔽
  claim          : 𝔽
  polynomial     : CMvPolynomial n 𝔽
  evalPoints     : Fin (d + 1) → 𝔽
  evalPoints_inj : Function.Injective evalPoints
  domain_sub     : ∀ x ∈ domain, ∃ k, evalPoints k = x
  degree_le      : ∀ i : Fin n, indDegreeK polynomial i ≤ d

/-- Sumcheck claim correctness in the eval-form bundle. -/
def sumcheckClaimIsCorrectEvalForm {𝔽 : Type} {n d : ℕ}
    [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d) : Prop :=
  st.claim = honestClaim st.domain st.polynomial

/-- The eval-form `PublicCoinProtocol` instance.

Per the design plan:
* `ProverMessage i := Fin (d+1) → 𝔽` (evaluations at `d+1` distinguished
  interpolation nodes).
* `Transcript` packs round-evals and challenges.
* `verifierAccepts` delegates to `isVerifierAcceptsEvalForm`. -/
noncomputable def sumcheckProtocolEvalForm
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    PublicCoinProtocol (SumcheckStatementEvalForm 𝔽 n d) 𝔽 n where
  ProverMessage := fun _ => Fin (d + 1) → 𝔽
  Transcript    := TranscriptEvalForm 𝔽 n d
  mkTranscript  := fun msgs chs =>
    { roundsEvals := msgs, challenges := chs }
  challenges    := fun tr => tr.challenges
  proverMessage := fun tr i => tr.roundsEvals i
  verifierAccepts := fun st tr =>
    isVerifierAcceptsEvalForm (𝔽 := 𝔽) (n := n) (d := d)
      st.domain st.evalPoints st.evalPoints_inj st.domain_sub
      st.polynomial st.claim tr
  verifierDecides := fun _ _ => Classical.propDecidable _
  challenges_mk := fun _ _ => rfl
  proverMessage_mk := fun _ _ _ => rfl

/-- The honest sumcheck prover in eval form.

At round `i`, with prior challenges `chs`, the prover sends the tuple
`fun k => honestProverMessageEvalsAt domain p i chs (evalPoints k)`,
i.e. the round polynomial's values at each of the `d+1` interpolation
nodes. -/
noncomputable def sumcheckHonestProverEvalForm
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)) where
  respond := fun st i chs k =>
    honestProverMessageEvalsAt (𝔽 := 𝔽) (n := n)
      st.domain st.polynomial i chs (st.evalPoints k)

/-! ## Reduction infrastructure

Helpers that map between eval-form and symbolic representations of a
single round message. The forward direction (`evaluateRound`) is
straightforward and computable; the inverse (`interpolateRound`) goes
through Mathlib's `Lagrange.interpolate` and is `noncomputable`.
-/

/-- Evaluate a symbolic round polynomial at the `d+1` interpolation
nodes, producing the eval-form representation. -/
def evaluateRound
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (q : CMvPolynomial 1 𝔽) : Fin (d + 1) → 𝔽 :=
  fun k => CMvPolynomial.eval (fun _ : Fin 1 => evalPoints k) q

/-- The Lagrange interpolant `Polynomial 𝔽` produced by an eval-form
round message at the `d+1` interpolation nodes. Used by the verifier
to evaluate at its random challenge. -/
noncomputable def interpolateRound
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (qEvals : Fin (d + 1) → 𝔽) : Polynomial 𝔽 :=
  Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) evalPoints qEvals

/-- The Lagrange-interpolant agrees with `qEvals` at every interpolation
node — direct application of `Lagrange.eval_interpolate_at_node`. -/
theorem interpolateRound_eval_at_node
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (qEvals : Fin (d + 1) → 𝔽) (k : Fin (d + 1)) :
    (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).eval (evalPoints k)
      = qEvals k := by
  classical
  unfold interpolateRound
  have hinjOn : Set.InjOn evalPoints
      (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hinj h
  exact Lagrange.eval_interpolate_at_node (v := evalPoints) (r := qEvals)
    hinjOn (Finset.mem_univ k)

/-- For honest input, the Lagrange interpolant evaluated at a domain
element `a ∈ domain` equals `honestProverMessageEvalsAt … a`.

This is the operational lemma underlying the eval-form sum-on-domain
check: by `domain_sub`, every `a ∈ domain` lies in the node image,
where the interpolant agrees with the prover's eval tuple by
`interpolateRound_eval_at_node`. -/
theorem interpolateRound_eval_on_domain
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (domain : List 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x)
    (p : CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    {a : 𝔽} (ha : a ∈ domain) :
    (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints
        (fun k => honestProverMessageEvalsAt
          domain p i challenges (evalPoints k))).eval a
      =
    honestProverMessageEvalsAt domain p i challenges a := by
  classical
  rcases domain_sub a ha with ⟨k, hk⟩
  rw [← hk]
  exact interpolateRound_eval_at_node (𝔽 := 𝔽) (d := d)
    evalPoints hinj
    (fun j => honestProverMessageEvalsAt domain p i challenges (evalPoints j)) k

/-! ## Adversary transport

An adversary against the symbolic instance can be transported to one
against the eval-form instance by composing with `evaluateRound`. The
converse direction would use `interpolateRound`, but its
`Polynomial 𝔽 → CMvPolynomial 1 𝔽` step requires a univariate-vs-
multivariate-1 polynomial bridge that lives outside the present scope
(see file-level docstring).
-/

/-- Transport an eval-form statement to a symbolic one. -/
def evalFormToStatement {𝔽 : Type} {n d : ℕ}
    [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d) : SumcheckStatement 𝔽 n :=
  { domain := st.domain
    claim := st.claim
    polynomial := st.polynomial }

@[simp] lemma evalFormToStatement_domain {𝔽 : Type} {n d : ℕ}
    [Field 𝔽] [DecidableEq 𝔽] (st : SumcheckStatementEvalForm 𝔽 n d) :
    (evalFormToStatement st).domain = st.domain := rfl

@[simp] lemma evalFormToStatement_claim {𝔽 : Type} {n d : ℕ}
    [Field 𝔽] [DecidableEq 𝔽] (st : SumcheckStatementEvalForm 𝔽 n d) :
    (evalFormToStatement st).claim = st.claim := rfl

@[simp] lemma evalFormToStatement_polynomial {𝔽 : Type} {n d : ℕ}
    [Field 𝔽] [DecidableEq 𝔽] (st : SumcheckStatementEvalForm 𝔽 n d) :
    (evalFormToStatement st).polynomial = st.polynomial := rfl

/-- A symbolic prover induces an eval-form prover by applying
`evaluateRound` to its round polynomial. -/
noncomputable def liftSymbolicProver
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n))) :
    Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)) where
  respond := fun st i chs k =>
    CMvPolynomial.eval (fun _ : Fin 1 => st.evalPoints k)
      (P.respond (evalFormToStatement st) i chs)

/-! ## Honest-prover correctness ingredient (per-round)

We expose the operational core of completeness: for an honest prover,
the eval-form sum-on-domain check at round `i` evaluates to the
symbolic round-`i` honest claim. This is a direct corollary of the
Phase-1 consistency lemma `eval_honestProverMessageAt_eq_honestProverMessageEvalsAt`
plus `Lagrange.eval_interpolate_at_node`.

The full chain consistency (i.e., the next-claim link in eval-form
matching the next-claim link in symbolic) requires the univariate ↔
multivariate-1 polynomial bridge referenced above and is therefore
left as Phase 5+ work. -/

/-- Generic `List.foldl` congruence: if `f acc a = g acc a` for every
`a ∈ L` and every accumulator, then `L.foldl f = L.foldl g` from any
starting accumulator. -/
private theorem foldl_congr_of_pointwise
    {α β : Type _} {L : List α} {f g : β → α → β}
    (h : ∀ a ∈ L, ∀ acc, f acc a = g acc a) :
    ∀ acc, L.foldl f acc = L.foldl g acc := by
  induction L with
  | nil => intro _; rfl
  | cons a t ih =>
    intro acc
    have hpta : ∀ acc', f acc' a = g acc' a := fun acc' =>
      h a (by simp) acc'
    have ht : ∀ b ∈ t, ∀ acc', f acc' b = g acc' b := fun b hb acc' =>
      h b (by simp [hb]) acc'
    simp only [List.foldl]
    rw [hpta acc]
    exact ih ht (g acc a)

/-- For the honest eval-form prover at round `i`, the eval-form
sum-on-domain function equals the symbolic sum-on-domain of the
honest round polynomial — i.e., the per-round eval-form check is
correct (per `domain_sub`-induced lookup). -/
theorem sumOnDomain_honest_eq_symbolic
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽) :
    sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
      st.domain st.evalPoints st.evalPoints_inj st.domain_sub
      (fun k => honestProverMessageEvalsAt
        st.domain st.polynomial i challenges (st.evalPoints k))
    =
    st.domain.foldl (fun acc a =>
      acc + CMvPolynomial.eval (fun _ : Fin 1 => a)
        (honestProverMessageAt st.domain st.polynomial i challenges)) 0 := by
  classical
  unfold sumOnDomainEvalForm
  -- Show the two folds agree pointwise on the domain.
  -- LHS folds `interp.eval a`; RHS folds `eval(a) (symPoly)`.
  -- For each `a ∈ domain`, both equal `honestProverMessageEvalsAt … a`.
  set f_l : 𝔽 → 𝔽 → 𝔽 := fun acc a =>
    acc + (interpolateRound (𝔽 := 𝔽) (d := d) st.evalPoints
            (fun k => honestProverMessageEvalsAt
              st.domain st.polynomial i challenges (st.evalPoints k))).eval a
  set f_r : 𝔽 → 𝔽 → 𝔽 := fun acc a =>
    acc + CMvPolynomial.eval (fun _ : Fin 1 => a)
      (honestProverMessageAt st.domain st.polynomial i challenges)
  -- Rewrite goal to match f_l, f_r form.
  show st.domain.foldl f_l 0 = st.domain.foldl f_r 0
  -- f_l a = f_r a for all a ∈ domain, using interpolateRound_eval_on_domain
  -- and eval_honestProverMessageAt_eq_honestProverMessageEvalsAt (in reverse).
  have hpt : ∀ a, a ∈ st.domain → ∀ acc, f_l acc a = f_r acc a := by
    intro a ha acc
    show acc + _ = acc + _
    congr 1
    -- interpolant.eval a = honestProverMessageEvalsAt … a
    rw [interpolateRound_eval_on_domain
        (𝔽 := 𝔽) (n := n) (d := d) st.domain
        st.evalPoints st.evalPoints_inj st.domain_sub
        st.polynomial i challenges ha]
    -- honestProverMessageEvalsAt … a = eval (fun _ => a) (honestProverMessageAt …)
    exact (eval_honestProverMessageAt_eq_honestProverMessageEvalsAt
      (𝔽 := 𝔽) (n := n) st.domain st.polynomial i challenges a).symm
  -- Reduce to a generic foldl-congruence statement (no `st` in scope).
  exact foldl_congr_of_pointwise (L := st.domain) (f := f_l) (g := f_r) hpt 0
