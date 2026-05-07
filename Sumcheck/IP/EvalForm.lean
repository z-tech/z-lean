import InteractiveProtocol.Src.Protocol
import InteractiveProtocol.Properties.Soundness
import Sumcheck.Src
import Sumcheck.Properties.EvalForm
import Sumcheck.IP.Statement
import Sumcheck.IP.InteractiveProtocol
import Sumcheck.Properties.Theorems
import Sumcheck.Properties.Events
import Sumcheck.Properties.Probability
import Sumcheck.Properties.Lemmas.SoundnessLemmas

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

We provide an explicit transcript-level mapping via
`liftEvalToSymbolic` (single round) and `liftEvalProverToSymbolic`
(prover), bridging eval-form transcripts to symbolic ones by Lagrange
interpolation. Both perfect completeness
(`sumcheck_hasPerfectCompleteness_evalForm`) and soundness
(`sumcheck_hasSoundnessError_evalForm_uniform`, conditional on a
uniform per-round degree predicate) are derived through this bridge.
The uniform-degree hypothesis is what aligns the eval-form
verifier's "≤ d" interpolant bound with the symbolic verifier's
per-round `degreeOf 0 ≤ indDegreeK p i` check.
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

/-! ## Phase 4 extension: full lift theorems

Beyond the floor delivered above, we now close:

* `interpolate_evaluate_round_trip` — left-inverse round-trip:
  for any eval tuple `qEvals`, evaluating its Lagrange interpolant at
  the nodes recovers `qEvals`.
* `evaluate_interpolate_round_trip_honest` — right-inverse round-trip,
  restricted to honest round polynomials. The general univariate ↔
  multivariate-1 round-trip is gated by `eval_honestProverMessageAt_eq_interpolate_eval`
  from Phase 1 polish; we expose the eval-equivalence form.
* `verifierAccepts_iff_honest` — the eval-form verifier accepts the
  honest eval-form transcript iff the symbolic verifier accepts the
  honest symbolic transcript at the same challenges (specialised
  bidirectional reduction, sufficient for completeness).
* `evalForm_accepts_implies_symbolic_accepts` — adversary transport in
  the soundness direction: for any eval-form adversary `P`, eval-form
  acceptance entails acceptance of a constructed symbolic adversary
  `liftEvalProverToSymbolic P` with the same statement.
* `sumcheck_hasPerfectCompleteness_evalForm`,
  `sumcheck_hasSoundnessError_evalForm` — the IP-framework
  completeness / soundness instances for the eval-form protocol.
-/

/-- **Round-trip 1** (forward): the Lagrange interpolant of `qEvals` at
the `d+1` distinct nodes recovers `qEvals` when re-evaluated at those
nodes. Direct corollary of `interpolateRound_eval_at_node`. -/
theorem interpolate_evaluate_round_trip
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (qEvals : Fin (d + 1) → 𝔽) :
    (fun k => Polynomial.eval (evalPoints k)
        (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals))
      = qEvals := by
  funext k
  exact interpolateRound_eval_at_node (𝔽 := 𝔽) (d := d)
    evalPoints hinj qEvals k

/-- **Round-trip 2** (backward, eval-equivalence form): for the honest
round polynomial `q := honestProverMessageAt … `, interpolating its
node-evaluations through the `d+1` distinct interpolation points
yields a polynomial that agrees with `q` at every field point.

This is the right-inverse direction modulo the type bridge: the
interpolant lives in `Polynomial 𝔽` while `q` lives in
`CMvPolynomial 1 𝔽`, but they agree under evaluation thanks to
`eval_honestProverMessageAt_eq_interpolate_eval` (Phase 1 polish).

A general statement for arbitrary `q : CMvPolynomial 1 𝔽` would also
hold but requires the same univariate bridge applied to a generic
polynomial; we only need the honest-prover case for the
soundness/completeness lifts. -/
theorem evaluate_interpolate_round_trip_honest
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (domain : List 𝔽)
    (p : CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (hdeg : CMvPolynomial.degreeOf (0 : Fin 1)
      (honestProverMessageAt domain p i challenges) ≤ d)
    (r : 𝔽) :
    Polynomial.eval r
      (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints
        (fun k => honestProverMessageEvalsAt
          domain p i challenges (evalPoints k)))
      =
    CMvPolynomial.eval (fun _ : Fin 1 => r)
      (honestProverMessageAt domain p i challenges) := by
  classical
  have hinjOn : Set.InjOn evalPoints (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hinj h
  -- Bridge through the universal-`r` interpolation theorem (Phase 1 polish).
  have h := eval_honestProverMessageAt_eq_interpolate_eval
    (𝔽 := 𝔽) (n := n) (d := d) domain p i challenges
    evalPoints hinjOn hdeg r
  -- `interpolateRound` is exactly `Lagrange.interpolate Finset.univ evalPoints _`.
  exact h.symm

/-! ### Verifier-accept iff (honest direction)

For honest-prover eval-form transcripts at any challenges `r`, the
eval-form verifier accepts iff the symbolic verifier accepts the
honest symbolic transcript at the same challenges. This is the
specialised bidirectional reduction; the version for arbitrary
adversaries is reduced via `evalForm_accepts_implies_symbolic_accepts`
below.
-/

/-- The honest eval-form transcript at challenges `r`. Identical in
data to the eval-form prover transcript for `sumcheckHonestProverEvalForm`,
spelled out so the symbolic-side equivalence is direct. -/
private noncomputable def honestEvalFormTranscript
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d) (r : Fin n → 𝔽) :
    TranscriptEvalForm 𝔽 n d :=
  { roundsEvals := fun i k =>
      honestProverMessageEvalsAt st.domain st.polynomial i
        (challengeSubset r i) (st.evalPoints k)
    challenges := r }

/-- The honest symbolic transcript at challenges `r`. Same data as
`generateHonestTranscript` from `Src/Transcript.lean`. -/
private noncomputable def honestSymbolicTranscript
    {𝔽 : Type} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st_sym : SumcheckStatement 𝔽 n) (r : Fin n → 𝔽) :
    Transcript 𝔽 n :=
  { roundPolys := fun i =>
      honestProverMessageAt st_sym.domain st_sym.polynomial i (challengeSubset r i)
    challenges := r }

/-- Per-round acceptance equivalence at the honest prover (sum-on-domain
direction): the eval-form sum-on-domain check holds iff the symbolic
sum-on-domain check holds, given matching round claims. -/
private theorem honest_round_check_iff
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (claim_i : 𝔽) :
    sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
      st.domain st.evalPoints st.evalPoints_inj st.domain_sub
      (fun k => honestProverMessageEvalsAt
        st.domain st.polynomial i challenges (st.evalPoints k))
      = claim_i
    ↔
    st.domain.foldl (fun acc a =>
      acc + CMvPolynomial.eval (fun _ : Fin 1 => a)
        (honestProverMessageAt st.domain st.polynomial i challenges)) 0
      = claim_i := by
  rw [sumOnDomain_honest_eq_symbolic st i challenges]

/-- For honest claim chains, the eval-form `nextClaimEvalForm` agrees
with the symbolic `nextClaim` of the honest round polynomial. -/
private theorem honest_nextClaim_eq
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (c : 𝔽)
    (hdeg : CMvPolynomial.degreeOf (0 : Fin 1)
      (honestProverMessageAt st.domain st.polynomial i challenges) ≤ d) :
    nextClaimEvalForm (𝔽 := 𝔽) (d := d) st.evalPoints
      (fun k => honestProverMessageEvalsAt
        st.domain st.polynomial i challenges (st.evalPoints k)) c
      =
    nextClaim c
      (honestProverMessageAt st.domain st.polynomial i challenges) := by
  classical
  unfold nextClaimEvalForm nextClaim
  -- LHS: `(Lagrange.interpolate … evalPoints _).eval c`.
  -- RHS: `CMvPolynomial.eval (fun _ => c) (honestProverMessageAt …)`.
  -- Bridge by `eval_honestProverMessageAt_eq_interpolate_eval`.
  have hinjOn : Set.InjOn st.evalPoints (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => st.evalPoints_inj h
  exact (eval_honestProverMessageAt_eq_interpolate_eval
    (𝔽 := 𝔽) (n := n) (d := d) st.domain st.polynomial i challenges
    st.evalPoints hinjOn hdeg c).symm

/-! ### Lift: completeness

We package the per-round equivalences into a full bidirectional
verifier-accepts iff for the honest prover at any challenge, then
lift `sumcheck_hasPerfectCompleteness` through it.
-/

/-- The eval-form transcript's intermediate claims agree with the
symbolic transcript's intermediate claims, for the **honest** transcripts
at the same challenges. The proof is by induction on the claim index
through `generateHonestClaimsEvalForm`/`generateHonestClaims`. -/
private theorem claims_evalForm_eq_claims_sym
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {st : SumcheckStatementEvalForm 𝔽 n d}
    {r : Fin n → 𝔽}
    (j : Fin (n + 1))
    (hdeg_round : ∀ i : Fin n, ∀ chs : Fin i.val → 𝔽,
      CMvPolynomial.degreeOf (0 : Fin 1)
        (honestProverMessageAt st.domain st.polynomial i chs) ≤ d) :
    ((sumcheckProtocolEvalForm.mkTranscript
        (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
      : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim j
    =
    (honestSymbolicTranscript (evalFormToStatement st) r).claims st.claim j := by
  classical
  rcases j with ⟨jv, hjv⟩
  match jv, hjv with
  | 0, _ => rfl
  | k + 1, hjv =>
    have hkn : k < n := Nat.lt_of_succ_lt_succ hjv
    let i : Fin n := ⟨k, hkn⟩
    have hLHS_step :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim ⟨k + 1, hjv⟩
          = nextClaimEvalForm (𝔽 := 𝔽) (d := d) st.evalPoints
              (fun kk => honestProverMessageEvalsAt st.domain st.polynomial i
                (challengeSubset r i) (st.evalPoints kk))
              (r i) := rfl
    have hRHS_step :
        (honestSymbolicTranscript (evalFormToStatement st) r).claims st.claim ⟨k + 1, hjv⟩
          = nextClaim (r i)
              (honestProverMessageAt st.domain st.polynomial i (challengeSubset r i)) := rfl
    rw [hLHS_step, hRHS_step]
    exact honest_nextClaim_eq st i (challengeSubset r i) (r i) (hdeg_round i _)

/-- The eval-form verifier accepts the honest eval-form transcript
**at every challenge tuple** when the claim is correct. The proof
proceeds by directly checking each acceptance ingredient (per-round
sum-on-domain identity, nextClaim chain, final equality), reusing
the symbolic `perfect_completeness` ingredients via the bridges above. -/
theorem honest_evalForm_accepts_at
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (hCorrect : sumcheckClaimIsCorrectEvalForm st)
    (r : Fin n → 𝔽) :
    sumcheckProtocolEvalForm.verifierAccepts st
      (generateTranscript sumcheckProtocolEvalForm st
        sumcheckHonestProverEvalForm r) := by
  classical
  -- Unfold to `isVerifierAcceptsEvalForm` of the honest transcript.
  show isVerifierAcceptsEvalForm (𝔽 := 𝔽) (n := n) (d := d)
    st.domain st.evalPoints st.evalPoints_inj st.domain_sub
    st.polynomial st.claim
    (sumcheckProtocolEvalForm.mkTranscript
      (fun i => sumcheckHonestProverEvalForm.respond st i (challengeSubset r i)) r)
  -- The honest symbolic transcript at the same challenges accepts
  -- (by the existing perfect_completeness ingredient).
  let t_sym : Transcript 𝔽 n := honestSymbolicTranscript
    (evalFormToStatement st) r
  have hSymAcc : AcceptsEvent st.domain st.polynomial st.claim t_sym := by
    -- Use the perfect_completeness ingredient: every honest transcript is accepted.
    have hCorrect' : st.claim = honestClaim st.domain st.polynomial := hCorrect
    rw [hCorrect']
    -- Cast `t_sym` to the form generateHonestTranscript produces.
    have hsym_eq : t_sym
        = generateHonestTranscript (𝔽 := 𝔽) (n := n) st.domain st.polynomial
            (honestClaim st.domain st.polynomial) r := by
      simp [t_sym, honestSymbolicTranscript, generateHonestTranscript,
        evalFormToStatement]
    rw [hsym_eq]
    -- Apply the honest-transcript ingredient by reproducing it directly:
    -- the honest transcript is accepted for every r.
    simp only [AcceptsEvent, isVerifierAccepts, Transcript.claims, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro i _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · simp only [verifierCheck, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨?_, ?_⟩
        · exact honest_transcript_sum_identity st.domain st.polynomial r i
        · -- Degree bound: honestRoundPoly degree ≤ indDegreeK
          have hpoly :
              (generateHonestTranscript st.domain st.polynomial
                (honestClaim st.domain st.polynomial) r).roundPolys i =
              honestRoundPoly st.domain (p := st.polynomial) (ch := r) i := by
            simp [generateHonestTranscript, honestRoundPoly, honestProverMessageAt]
          rw [hpoly]
          exact honest_round_poly_degree_le_ind_degree_k st.domain st.polynomial r i
      · -- claims i.succ = nextClaim …
        have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
        simp only [generateHonestTranscript, generateHonestClaims, nextClaim, hsuc]
    · -- final claim
      simp only [decide_eq_true_eq]
      exact honest_transcript_final_eq_eval n st.domain st.polynomial r
  -- Now translate the symbolic acceptance into eval-form acceptance.
  -- Strategy: induction-free unfolding — both `isVerifierAccepts` (Bool)
  -- and `isVerifierAcceptsEvalForm` (Prop) decompose into the same per-round
  -- ingredients via the bridge lemmas.
  have hSymAcc' :
      isVerifierAccepts st.domain st.polynomial st.claim t_sym = true := hSymAcc
  -- Unpack the symbolic acceptance.
  rw [isVerifierAccepts, Bool.and_eq_true] at hSymAcc'
  obtain ⟨hSymRounds, hSymFinal⟩ := hSymAcc'
  rw [List.all_eq_true] at hSymRounds
  -- Helper: degreeOf bound on honest round poly via indDegreeK and st.degree_le.
  have hdeg_round : ∀ i : Fin n, ∀ chs : Fin i.val → 𝔽,
      CMvPolynomial.degreeOf (0 : Fin 1)
        (honestProverMessageAt st.domain st.polynomial i chs) ≤ d := by
    intro i chs
    -- Use `degree_honest_prover_message_at_le_of_per_b` via `honest_round_poly_degree_le_ind_degree_k`,
    -- but the latter takes `r : Fin n → 𝔽` and gives bound for `challengeSubset r i`.
    -- We need it for arbitrary `chs`. Construct an `r` whose first i values are chs.
    let r' : Fin n → 𝔽 := fun k =>
      if h : k.val < i.val then chs ⟨k.val, h⟩ else 0
    have hsub : challengeSubset r' i = chs := by
      funext t
      have hlt : t.val < i.val := t.isLt
      show (if h : t.val < i.val then chs ⟨t.val, h⟩ else 0) = chs t
      rw [dif_pos hlt]
    have hbound :=
      honest_round_poly_degree_le_ind_degree_k st.domain st.polynomial r' i
    -- honestRoundPoly = honestProverMessageAt … (challengeSubset r' i) = … chs.
    have heq : honestRoundPoly st.domain (p := st.polynomial) (ch := r') i
        = honestProverMessageAt st.domain st.polynomial i chs := by
      unfold honestRoundPoly
      rw [hsub]
    rw [heq] at hbound
    exact le_trans hbound (st.degree_le i)
  -- Build per-round eval-form checks from the symbolic per-round checks.
  -- Eval-form transcript matches `mkTranscript` reduction.
  -- claims_eval at any j equals claims_sym at j when round-evals are honest.
  -- We prove this by induction on j.
  let claims_sym : Fin (n + 1) → 𝔽 := t_sym.claims st.claim
  -- Now produce `claims_eval` and prove agreement.
  refine ⟨?_, ?_⟩
  · -- per-round acceptance
    intro i
    -- Use the per-round honest equivalence.
    have hSymRound_i := hSymRounds i (List.mem_finRange i)
    rw [Bool.and_eq_true, decide_eq_true_eq] at hSymRound_i
    obtain ⟨hSymCheck_i, hSymNext_i⟩ := hSymRound_i
    -- hSymCheck_i: verifierCheck domain (indDegreeK p i) (claims_sym i.castSucc) (t_sym.roundPolys i)
    rw [verifierCheck, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      at hSymCheck_i
    obtain ⟨hSumIdent_i, _⟩ := hSymCheck_i
    -- hSumIdent_i: domain.foldl ... = claims_sym i.castSucc
    -- The eval-form roundsEvals at i = honestProverMessageEvalsAt … (st.evalPoints k).
    -- Build the eval-form `claims i.castSucc` and show it matches claims_sym i.castSucc.
    -- Then use `sumOnDomain_honest_eq_symbolic` + `hSumIdent_i`.
    refine ⟨?_, ?_⟩
    · -- verifierCheckEvalForm
      unfold verifierCheckEvalForm
      -- After unfolding, the goal is sumOnDomainEvalForm = claims_eval (Fin.castSucc i).
      -- The needed equality reduces to sumOnDomain_honest_eq_symbolic = claims_sym (Fin.castSucc i)
      -- combined with claims_eval (Fin.castSucc i) = claims_sym (Fin.castSucc i).
      have hclaims_eq :
          ((sumcheckProtocolEvalForm.mkTranscript
              (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
            : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.castSucc i)
          = claims_sym (Fin.castSucc i) := by
        exact (claims_evalForm_eq_claims_sym (st := st) (r := r) (Fin.castSucc i) hdeg_round)
      rw [hclaims_eq]
      -- Replace eval-form roundsEvals by definition: matches the honest values.
      have hroundEvals_def :
          ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
            : TranscriptEvalForm 𝔽 n d)).roundsEvals i
          = (fun k => honestProverMessageEvalsAt st.domain st.polynomial i
              (challengeSubset r i) (st.evalPoints k)) := rfl
      rw [hroundEvals_def]
      -- Now: sumOnDomainEvalForm (honestProverMessageEvalsAt …) = claims_sym i.castSucc
      rw [sumOnDomain_honest_eq_symbolic st i (challengeSubset r i)]
      -- And on the symbolic side, the honest sum identity gives this.
      -- But t_sym.roundPolys i = honestProverMessageAt st.domain st.polynomial i (challengeSubset r i).
      have hrp : t_sym.roundPolys i =
          honestProverMessageAt st.domain st.polynomial i (challengeSubset r i) := rfl
      rw [hrp] at hSumIdent_i
      exact hSumIdent_i
    · -- claims_eval i.succ = nextClaimEvalForm (roundsEvals i) (challenges i)
      -- This is just unfolding via the recursive case of generateHonestClaimsEvalForm.
      have hsuc : i.succ = ⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩ := Fin.ext rfl
      simp only [TranscriptEvalForm.claims, generateHonestClaimsEvalForm, hsuc]
  · -- final acceptance: claims_eval (Fin.last n) = polynomial.eval challenges
    -- Reduce via claims_evalForm_eq_claims_sym at Fin.last and the symbolic final.
    have hclaims_eq_last :
        ((sumcheckProtocolEvalForm.mkTranscript
          (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
        : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.last n)
        = claims_sym (Fin.last n) := by
      exact (claims_evalForm_eq_claims_sym (st := st) (r := r) (Fin.last n) hdeg_round)
    rw [hclaims_eq_last]
    -- claims_sym (Fin.last n) = CMvPolynomial.eval challenges p (by symbolic final acceptance).
    rw [decide_eq_true_eq] at hSymFinal
    -- `t_sym.challenges = r` — show the eval-form challenges also equal `r`.
    have heval : ((sumcheckProtocolEvalForm.mkTranscript
        (fun j => sumcheckHonestProverEvalForm.respond st j (challengeSubset r j)) r
      : TranscriptEvalForm 𝔽 n d)).challenges = r := rfl
    rw [heval]
    exact hSymFinal

/-- **Phase 4 deliverable**: perfect-completeness lift for the eval-form
sumcheck protocol. Direct from `honest_evalForm_accepts_at`: every
challenge tuple makes the eval-form verifier accept the honest
eval-form transcript when the claim is correct. -/
theorem sumcheck_hasPerfectCompleteness_evalForm
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    hasPerfectCompleteness
      (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d))
      sumcheckClaimIsCorrectEvalForm
      sumcheckHonestProverEvalForm := by
  intro st hCorrect
  classical
  -- The accept event is a Prop; show it holds for every r.
  have hAll : ∀ r : Fin n → 𝔽,
      sumcheckProtocolEvalForm.verifierAccepts st
        (generateTranscript sumcheckProtocolEvalForm st sumcheckHonestProverEvalForm r) :=
    fun r => honest_evalForm_accepts_at (𝔽 := 𝔽) (n := n) (d := d) st hCorrect r
  -- probAccept = probEvent of an always-true predicate = 1.
  -- Reuse the existing `probOverChallenges`-of-tautology pattern from
  -- `Properties/Theorems/Completeness.lean`.
  show probEvent (C := 𝔽) (n := n)
    (fun r => sumcheckProtocolEvalForm.verifierAccepts st
      (generateTranscript sumcheckProtocolEvalForm st sumcheckHonestProverEvalForm r))
    = 1
  letI : DecidablePred (fun r : Fin n → 𝔽 =>
      sumcheckProtocolEvalForm.verifierAccepts st
        (generateTranscript sumcheckProtocolEvalForm st sumcheckHonestProverEvalForm r)) :=
    Classical.decPred _
  have hfilter :
      (allChallenges 𝔽 n).filter (fun r => sumcheckProtocolEvalForm.verifierAccepts st
        (generateTranscript sumcheckProtocolEvalForm st sumcheckHonestProverEvalForm r))
      = (allChallenges 𝔽 n) := by
    ext r
    simp [hAll r]
  -- |allChallenges| > 0 for the field-valued challenge space.
  have hcard_pos : 0 < (allChallenges 𝔽 n).card := by
    rw [show (allChallenges 𝔽 n).card = Fintype.card (Fin n → 𝔽) from rfl]
    exact Fintype.card_pos
  -- Goal: probEvent … = 1.  Reduce probEvent to (filter.card / Ω.card) = 1.
  have hQ_pos : (0 : ℚ) < ((allChallenges 𝔽 n).card : ℚ) := by exact_mod_cast hcard_pos
  show ((allChallenges 𝔽 n).filter
      (fun r => sumcheckProtocolEvalForm.verifierAccepts st
        (generateTranscript sumcheckProtocolEvalForm st sumcheckHonestProverEvalForm r))).card
        / ((allChallenges 𝔽 n).card : ℚ)
      = 1
  rw [hfilter]
  exact div_self (ne_of_gt hQ_pos)


/-! ### Lift: soundness

We provide the adversary-transport definitions
`liftEvalToSymbolic` (single round) and `liftEvalProverToSymbolic`
(prover) needed for the soundness lift, and prove the eval-equivalence
that underpins it.

The naïve lift through symbolic soundness is blocked when
`indDegreeK st.polynomial i < d` for some round `i`: the Lagrange
interpolant of the eval-form prover's `Fin (d+1) → 𝔽` tuple has degree
≤ d, which is a strictly weaker bound than the symbolic verifier's
per-round `degreeOf 0 ≤ indDegreeK p i` check. We close this gap by
adding a uniform-degree predicate `UniformDegreePoly d p :=
∀ i, indDegreeK p i = d` and proving the conditional
`sumcheck_hasSoundnessError_evalForm_uniform`: under uniform-d, the
eval-form instance has soundness error ≤ `d * n / |𝔽|`, lifted from
`sumcheck_hasSoundnessError`.
-/

/-- Convert an eval tuple to a `CMvPolynomial 1 𝔽` via Lagrange
interpolation. Used by `liftEvalProverToSymbolic` to transport
eval-form adversaries to the symbolic protocol. -/
noncomputable def liftEvalToSymbolic
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (qEvals : Fin (d + 1) → 𝔽) : CMvPolynomial 1 𝔽 :=
  CPoly.toCMvPolynomial (R := 𝔽) (n := 1)
    ((MvPolynomial.finOneEquiv 𝔽).symm
      (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals))

/-- An eval-form adversary lifts to a symbolic adversary by Lagrange-
interpolating each round's eval tuple, then bridging to
`CMvPolynomial 1 𝔽`. -/
noncomputable def liftEvalProverToSymbolic
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d))) :
    SumcheckStatementEvalForm 𝔽 n d → Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)) :=
  fun st0 => {
    respond := fun _ i chs =>
      liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints
        (P.respond st0 i chs)
  }

/-- Bridge identity: `toUnivariate` (the Phase-1 univariate bridge)
inverts the construction of `liftEvalToSymbolic`. The result is the
Lagrange interpolant directly. -/
theorem toUnivariate_liftEvalToSymbolic
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽) (qEvals : Fin (d + 1) → 𝔽) :
    toUnivariate (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints qEvals)
      = interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals := by
  unfold toUnivariate liftEvalToSymbolic
  rw [CPoly.fromCMvPolynomial_toCMvPolynomial]
  exact AlgEquiv.apply_symm_apply _ _

/-- Eval-equivalence: evaluating the lifted symbolic round polynomial
at `x` agrees with evaluating the Lagrange interpolant at `x`. This
is the operational core of the soundness lift: per-round checks on
both sides reduce to the same scalar quantities at the verifier's
challenge. -/
theorem eval_liftEvalToSymbolic
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽) (qEvals : Fin (d + 1) → 𝔽) (x : 𝔽) :
    CMvPolynomial.eval (fun _ : Fin 1 => x)
        (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints qEvals)
      =
    (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).eval x := by
  rw [← toUnivariate_liftEvalToSymbolic evalPoints qEvals]
  exact (eval_toUnivariate (𝔽 := 𝔽)
    (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints qEvals) x).symm

/-! ### Degree bound on the lifted symbolic round polynomial

The Lagrange interpolant of a `Fin (d+1) → 𝔽` tuple has natDegree ≤ d.
The lifted `CMvPolynomial 1 𝔽` therefore has `degreeOf 0 ≤ d`. This
provides the symbolic verifier's degree-check input under uniform-d.
-/

/-- The Lagrange interpolant has natDegree ≤ d. -/
theorem natDegree_interpolateRound_le
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (qEvals : Fin (d + 1) → 𝔽) :
    (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).natDegree ≤ d := by
  classical
  have hinjOn : Set.InjOn evalPoints (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hinj h
  have hdeg : (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).degree
      < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    unfold interpolateRound
    exact Lagrange.degree_interpolate_lt _ hinjOn
  have hcard : ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) = (d + 1 : ℕ) := by
    simp
  rw [hcard] at hdeg
  -- `degree p < (d+1 : WithBot ℕ)` ⟹ `natDegree p ≤ d`.
  -- Use Polynomial.natDegree_le_iff_degree_le.
  by_cases hzero : interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals = 0
  · rw [hzero, Polynomial.natDegree_zero]; exact Nat.zero_le _
  · -- For nonzero p, degree < d+1 implies natDegree < d+1.
    have : (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).natDegree < d + 1 := by
      have hnd_eq : (interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).degree
          = ((interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals).natDegree : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hzero]
      rw [hnd_eq] at hdeg
      exact_mod_cast hdeg
    exact Nat.lt_succ_iff.mp this

/-- `natDegree` of the univariate bridge equals `degreeOf 0` of the
underlying multivariate-1 polynomial. The `≤` direction is in
`natDegree_toUnivariate_le`; we now establish the reverse direction
needed for `degreeOf_liftEvalToSymbolic_le`. -/
private theorem degreeOf_le_natDegree_toUnivariate
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
    (q : CMvPolynomial 1 𝔽) :
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q ≤ (toUnivariate q).natDegree := by
  classical
  unfold toUnivariate
  unfold MvPolynomial.finOneEquiv
  -- The chain mirrors `natDegree_toUnivariate_le`, with `≤` replaced by `≥`.
  have hMap :
      (Polynomial.map (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.toRingHom
        (MvPolynomial.finSuccEquiv (R := 𝔽) 0
          (CPoly.fromCMvPolynomial (R := 𝔽) q))).natDegree
        = (MvPolynomial.finSuccEquiv (R := 𝔽) 0
            (CPoly.fromCMvPolynomial (R := 𝔽) q)).natDegree := by
    apply Polynomial.natDegree_map_eq_of_injective
    exact (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.injective
  have hSucc :
      (MvPolynomial.finSuccEquiv (R := 𝔽) 0
        (CPoly.fromCMvPolynomial (R := 𝔽) q)).natDegree
        = MvPolynomial.degreeOf (R := 𝔽) (σ := Fin 1) 0
            (CPoly.fromCMvPolynomial (R := 𝔽) q) :=
    MvPolynomial.natDegree_finSuccEquiv (R := 𝔽) (n := 0)
      (CPoly.fromCMvPolynomial (R := 𝔽) q)
  have hCPoly : MvPolynomial.degreeOf (R := 𝔽) (σ := Fin 1) 0
      (CPoly.fromCMvPolynomial (R := 𝔽) q)
      = CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q :=
    (congrArg (fun f => f (0 : Fin 1))
      (CPoly.degreeOf_equiv (p := q) (S := 𝔽))).symm
  show CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q
      ≤ (Polynomial.map (MvPolynomial.isEmptyAlgEquiv 𝔽 (Fin 0)).toRingEquiv.toRingHom
        (MvPolynomial.finSuccEquiv (R := 𝔽) 0
          (CPoly.fromCMvPolynomial (R := 𝔽) q))).natDegree
  rw [hMap, hSucc, hCPoly]

/-- Degree bound for the lifted symbolic round polynomial.

The eval-form `qEvals : Fin (d+1) → 𝔽` interpolates to a univariate
polynomial of natDegree ≤ d, so the lifted `CMvPolynomial 1 𝔽` has
`degreeOf 0 ≤ d`. -/
theorem degreeOf_liftEvalToSymbolic_le
    {𝔽 : Type} {d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (evalPoints : Fin (d + 1) → 𝔽)
    (hinj : Function.Injective evalPoints)
    (qEvals : Fin (d + 1) → 𝔽) :
    CPoly.CMvPolynomial.degreeOf (0 : Fin 1)
        (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints qEvals) ≤ d := by
  classical
  set q := liftEvalToSymbolic (𝔽 := 𝔽) (d := d) evalPoints qEvals with hq
  have h1 : CPoly.CMvPolynomial.degreeOf (0 : Fin 1) q ≤ (toUnivariate q).natDegree :=
    degreeOf_le_natDegree_toUnivariate (𝔽 := 𝔽) q
  have h2 : toUnivariate q = interpolateRound (𝔽 := 𝔽) (d := d) evalPoints qEvals := by
    rw [hq]; exact toUnivariate_liftEvalToSymbolic evalPoints qEvals
  rw [h2] at h1
  exact le_trans h1 (natDegree_interpolateRound_le evalPoints hinj qEvals)

/-! ### Uniform-degree predicate and conditional soundness lift

We package the uniform-degree assumption used to align the symbolic
verifier's per-round `degreeOf 0 ≤ indDegreeK p i` check with the
eval-form interpolant's `≤ d` bound. The conditional theorem
`sumcheck_hasSoundnessError_evalForm_uniform` then lifts symbolic
soundness through `liftEvalProverToSymbolic`.
-/

/-- Uniform per-round individual degree: every variable's `indDegreeK`
equals the global bound `d`. Under this hypothesis, the eval-form
verifier's degree budget aligns exactly with the symbolic verifier's
budget per round. -/
def UniformDegreePoly {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (d : ℕ) (p : CMvPolynomial n 𝔽) : Prop :=
  ∀ i : Fin n, indDegreeK p i = d

/-- Under uniform-d, `maxIndDegree p = d` (when `n > 0`; for `n = 0`
the soundness error is `0 = 0` trivially). -/
private theorem maxIndDegree_eq_of_uniform
    {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    {d : ℕ} {p : CMvPolynomial n 𝔽}
    (hUni : UniformDegreePoly d p) (hn : 0 < n) :
    maxIndDegree p = d := by
  classical
  unfold maxIndDegree
  have hpt : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i p = d := by
    intro i; have := hUni i; simpa [indDegreeK] using this
  have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, by simp⟩
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    rw [hpt i]
  · rcases huniv_nonempty with ⟨i, hi⟩
    calc d = CPoly.CMvPolynomial.degreeOf i p := (hpt i).symm
      _ ≤ (Finset.univ : Finset (Fin n)).sup (fun j => CPoly.CMvPolynomial.degreeOf j p) :=
          Finset.le_sup (f := fun j => CPoly.CMvPolynomial.degreeOf j p) hi

/-- Per-round symbolic verifier check passes for the lifted prover's
output, given uniform-d on the statement polynomial. -/
private theorem symbolic_verifierCheck_of_evalForm
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (hUni : UniformDegreePoly d st.polynomial)
    (i : Fin n)
    (qEvals : Fin (d + 1) → 𝔽)
    (roundClaim : 𝔽)
    (hSum : sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
        st.domain st.evalPoints st.evalPoints_inj st.domain_sub qEvals = roundClaim) :
    verifierCheck st.domain (indDegreeK st.polynomial i) roundClaim
        (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints qEvals) = true := by
  classical
  -- verifierCheck is a Bool decided over a conjunction of two Props.
  unfold verifierCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · -- sum-on-domain identity for the lifted polynomial.
    -- `sumOnDomainEvalForm` folds the interpolant's eval; the symbolic side
    -- folds `eval (fun _ => a) (liftEvalToSymbolic …)`, which equals the
    -- interpolant's eval at `a` by `eval_liftEvalToSymbolic`.
    have hEq :
        st.domain.foldl (fun acc a => acc + CMvPolynomial.eval (fun _ : Fin 1 => a)
            (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints qEvals)) 0
        = sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
            st.domain st.evalPoints st.evalPoints_inj st.domain_sub qEvals := by
      unfold sumOnDomainEvalForm
      -- Both folds equal each other pointwise via `eval_liftEvalToSymbolic`.
      let f_l : 𝔽 → 𝔽 → 𝔽 := fun acc a =>
        acc + CMvPolynomial.eval (fun _ : Fin 1 => a)
          (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints qEvals)
      let f_r : 𝔽 → 𝔽 → 𝔽 := fun acc a =>
        acc + (interpolateRound (𝔽 := 𝔽) (d := d) st.evalPoints qEvals).eval a
      show st.domain.foldl f_l 0 = st.domain.foldl f_r 0
      exact foldl_congr_of_pointwise (L := st.domain) (f := f_l) (g := f_r)
        (fun a _ acc => by
          show acc + _ = acc + _
          congr 1
          exact eval_liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints qEvals a) 0
    rw [hEq]; exact hSum
  · -- degree-bound: `degreeOf 0 (lift …) ≤ indDegreeK p i = d`.
    have hUni_i : indDegreeK st.polynomial i = d := hUni i
    rw [hUni_i]
    exact degreeOf_liftEvalToSymbolic_le (𝔽 := 𝔽) (d := d)
      st.evalPoints st.evalPoints_inj qEvals

/-- The lifted symbolic transcript at challenges `r` from an eval-form
prover `P`, expressed in the symbolic-protocol shape. -/
private noncomputable def liftedSymbolicTranscript
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)))
    (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  { roundPolys := fun i =>
      liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
        (P.respond st i (challengeSubset r i))
    challenges := r }

/-- Eval-form claim chain matches the lifted symbolic claim chain
at all positions `j : Fin (n+1)`. This is the bridge that lets us
move per-round `roundClaim` data between the two sides. -/
private theorem claims_evalForm_eq_claims_lifted
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)))
    (r : Fin n → 𝔽)
    (j : Fin (n + 1)) :
    ((sumcheckProtocolEvalForm.mkTranscript
        (fun i => P.respond st i (challengeSubset r i)) r
      : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim j
    =
    (liftedSymbolicTranscript st P r).claims st.claim j := by
  classical
  rcases j with ⟨jv, hjv⟩
  match jv, hjv with
  | 0, _ => rfl
  | k + 1, hjv =>
    have hkn : k < n := Nat.lt_of_succ_lt_succ hjv
    let i : Fin n := ⟨k, hkn⟩
    -- LHS unfolds to `nextClaimEvalForm st.evalPoints (P.respond …) (r i)`.
    have hLHS_step :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim ⟨k + 1, hjv⟩
          = nextClaimEvalForm (𝔽 := 𝔽) (d := d) st.evalPoints
              (P.respond st i (challengeSubset r i)) (r i) := rfl
    -- RHS unfolds to `nextClaim (r i) (liftEvalToSymbolic … (P.respond …))`.
    have hRHS_step :
        (liftedSymbolicTranscript st P r).claims st.claim ⟨k + 1, hjv⟩
          = nextClaim (r i)
              (liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
                (P.respond st i (challengeSubset r i))) := rfl
    rw [hLHS_step, hRHS_step]
    -- nextClaimEvalForm = (interpolant).eval r_i; nextClaim = CMvPolynomial.eval (fun _ => r_i) lift.
    -- Equal by `eval_liftEvalToSymbolic`.
    unfold nextClaimEvalForm nextClaim
    rw [show (Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) st.evalPoints
              (P.respond st i (challengeSubset r i)))
            = interpolateRound (𝔽 := 𝔽) (d := d) st.evalPoints
                (P.respond st i (challengeSubset r i)) from rfl]
    exact (eval_liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
      (P.respond st i (challengeSubset r i)) (r i)).symm

/-- **Adversary transport** (soundness direction): if the eval-form
verifier accepts the eval-form transcript at `r`, then the symbolic
verifier accepts the lifted symbolic transcript at `r`.

Requires the uniform-degree hypothesis `UniformDegreePoly d
st.polynomial` to satisfy the symbolic verifier's per-round degree
check. -/
theorem evalForm_accepts_implies_symbolic_accepts
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (hUni : UniformDegreePoly d st.polynomial)
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)))
    (r : Fin n → 𝔽) :
    sumcheckProtocolEvalForm.verifierAccepts st
      (generateTranscript sumcheckProtocolEvalForm st P r) →
    sumcheckProtocol.verifierAccepts (evalFormToStatement st)
      (generateTranscript sumcheckProtocol (evalFormToStatement st)
        (liftEvalProverToSymbolic (𝔽 := 𝔽) (n := n) (d := d) st.evalPoints P st) r) := by
  intro hEvalAcc
  classical
  -- Eval-form acceptance is a Prop; unpack it.
  have hEvalAcc' :
      isVerifierAcceptsEvalForm (𝔽 := 𝔽) (n := n) (d := d)
        st.domain st.evalPoints st.evalPoints_inj st.domain_sub
        st.polynomial st.claim
        (sumcheckProtocolEvalForm.mkTranscript
          (fun i => P.respond st i (challengeSubset r i)) r) := hEvalAcc
  unfold isVerifierAcceptsEvalForm at hEvalAcc'
  obtain ⟨hRounds, hFinal⟩ := hEvalAcc'
  -- The symbolic transcript we need to show acceptance for.
  let t_sym : Transcript 𝔽 n := liftedSymbolicTranscript st P r
  -- Symbolic acceptance is `isVerifierAccepts … = true`.
  show isVerifierAccepts (evalFormToStatement st).domain
      (evalFormToStatement st).polynomial (evalFormToStatement st).claim
      { roundPolys :=
          fun i => liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
            (P.respond st i (challengeSubset r i)),
        challenges := r } = true
  -- This transcript is exactly `t_sym`.
  show isVerifierAccepts st.domain st.polynomial st.claim t_sym = true
  unfold isVerifierAccepts
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · intro i _
    -- per-round symbolic check
    rcases hRounds i with ⟨hSumOk, hNextOk⟩
    -- Eval-form claims at i.castSucc = lifted symbolic claims at i.castSucc.
    have hclaims_eq_castSucc :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.castSucc i)
          = t_sym.claims st.claim (Fin.castSucc i) :=
      claims_evalForm_eq_claims_lifted st P r (Fin.castSucc i)
    -- Eval-form claims at i.succ = lifted symbolic claims at i.succ.
    have hclaims_eq_succ :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim i.succ
          = t_sym.claims st.claim i.succ :=
      claims_evalForm_eq_claims_lifted st P r i.succ
    -- Eval-form `verifierCheckEvalForm` reduces the claim equation to
    -- `sumOnDomainEvalForm = (eval-form claim at i.castSucc)`.
    have hSumOk' : sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
        st.domain st.evalPoints st.evalPoints_inj st.domain_sub
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d).roundsEvals i)
        = ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.castSucc i) := by
      have h := hSumOk
      unfold verifierCheckEvalForm at h
      exact h
    -- Map LHS to lifted symbolic claim.
    rw [hclaims_eq_castSucc] at hSumOk'
    -- The eval-form roundsEvals at i = `P.respond st i (challengeSubset r i)`.
    have hroundEvals_def :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).roundsEvals i
          = P.respond st i (challengeSubset r i) := rfl
    rw [hroundEvals_def] at hSumOk'
    refine ⟨?_, ?_⟩
    · -- verifierCheck …
      have hLifted_round : t_sym.roundPolys i =
          liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
            (P.respond st i (challengeSubset r i)) := rfl
      rw [hLifted_round]
      exact symbolic_verifierCheck_of_evalForm st hUni i
        (P.respond st i (challengeSubset r i))
        (t_sym.claims st.claim (Fin.castSucc i))
        hSumOk'
    · -- next-claim equality.
      -- Eval-form: claims i.succ = nextClaimEvalForm … = (lifted) nextClaim …
      -- After rewriting the eval-form claim at `i.succ` to lifted, the equation
      -- transports through the same `eval_liftEvalToSymbolic` bridge.
      rw [← hclaims_eq_succ]
      have hroundEvals_def :
          ((sumcheckProtocolEvalForm.mkTranscript
              (fun j => P.respond st j (challengeSubset r j)) r
            : TranscriptEvalForm 𝔽 n d)).roundsEvals i
            = P.respond st i (challengeSubset r i) := rfl
      have hch_def :
          ((sumcheckProtocolEvalForm.mkTranscript
              (fun j => P.respond st j (challengeSubset r j)) r
            : TranscriptEvalForm 𝔽 n d)).challenges i = r i := rfl
      have hNextOk' : ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim i.succ
            = nextClaimEvalForm (𝔽 := 𝔽) (d := d) st.evalPoints
                (P.respond st i (challengeSubset r i)) (r i) := by
        rw [hroundEvals_def, hch_def] at hNextOk; exact hNextOk
      rw [hNextOk']
      -- nextClaimEvalForm = (interpolant).eval r_i = nextClaim r_i (lift …).
      unfold nextClaimEvalForm nextClaim
      have htsym_round : t_sym.roundPolys i =
          liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
            (P.respond st i (challengeSubset r i)) := rfl
      have htsym_ch : t_sym.challenges i = r i := rfl
      rw [htsym_round, htsym_ch]
      rw [show (Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) st.evalPoints
                (P.respond st i (challengeSubset r i)))
              = interpolateRound (𝔽 := 𝔽) (d := d) st.evalPoints
                  (P.respond st i (challengeSubset r i)) from rfl]
      exact (eval_liftEvalToSymbolic (𝔽 := 𝔽) (d := d) st.evalPoints
        (P.respond st i (challengeSubset r i)) (r i)).symm
  · -- final claim: claims (last n) = polynomial.eval challenges.
    have hclaims_eq_last :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.last n)
          = t_sym.claims st.claim (Fin.last n) :=
      claims_evalForm_eq_claims_lifted st P r (Fin.last n)
    have hch_last :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).challenges = r := rfl
    have hFinal' :
        ((sumcheckProtocolEvalForm.mkTranscript
            (fun j => P.respond st j (challengeSubset r j)) r
          : TranscriptEvalForm 𝔽 n d)).claims st.evalPoints st.claim (Fin.last n)
          = CMvPolynomial.eval r st.polynomial := by
      rw [hch_last] at hFinal; exact hFinal
    rw [hclaims_eq_last] at hFinal'
    -- Lifted t_sym.challenges = r and polynomial = (evalFormToStatement st).polynomial.
    show t_sym.claims st.claim (Fin.last n)
        = CMvPolynomial.eval t_sym.challenges (evalFormToStatement st).polynomial
    have ht_ch : t_sym.challenges = r := rfl
    rw [ht_ch]; exact hFinal'

/-! ### Conditional soundness lift -/

/-- Sumcheck claim correctness coincides on eval-form and symbolic
sides via `evalFormToStatement`. -/
private theorem sumcheckClaim_eval_iff_symbolic
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d) :
    sumcheckClaimIsCorrectEvalForm st ↔
      sumcheckClaimIsCorrect (evalFormToStatement st) := by
  unfold sumcheckClaimIsCorrectEvalForm sumcheckClaimIsCorrect
  rfl

/-- **Conditional soundness lift**: under the uniform-degree predicate
`UniformDegreePoly d st.polynomial`, the eval-form sumcheck instance's
soundness error is bounded by `d * n / |𝔽|`.

The bound `(n : ℚ) * (d : ℚ) / |𝔽|` is, under uniform-d, exactly
`soundnessError st.polynomial`; we keep the `d`-spelled bound to make
the statement independent of the polynomial's actual `maxIndDegree`.

The proof transports each false eval-form prover to a symbolic one via
`liftEvalProverToSymbolic`, then applies `sumcheck_hasSoundnessError`.
Uniform-d aligns the symbolic verifier's per-round degree budget with
the eval-form interpolant's `≤ d` bound (see
`degreeOf_liftEvalToSymbolic_le`), which is what makes
`evalForm_accepts_implies_symbolic_accepts` succeed.

The uniform-d hypothesis is supplied as a **direct argument**
(rather than being baked into a per-statement `isTrue`), since
`hasSoundnessError`'s contract requires the bound to hold for every
non-true statement, and uniform-d is a structural property orthogonal
to claim correctness. -/
theorem sumcheck_hasSoundnessError_evalForm_uniform
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckStatementEvalForm 𝔽 n d)
    (hUni : UniformDegreePoly d st.polynomial)
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)))
    (hFalse : ¬ sumcheckClaimIsCorrectEvalForm st) :
    probAccept (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)) st P
      ≤ (n : ℚ) * (d : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
  classical
  -- Lift to symbolic adversary.
  set st_sym : SumcheckStatement 𝔽 n := evalFormToStatement st
  set P_sym : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)) :=
    liftEvalProverToSymbolic (𝔽 := 𝔽) (n := n) (d := d) st.evalPoints P st
  have hClaim_sym : ¬ sumcheckClaimIsCorrect st_sym := by
    intro hC
    exact hFalse ((sumcheckClaim_eval_iff_symbolic (st := st)).mpr hC)
  -- Symbolic soundness gives us `probAccept symbolic ≤ soundnessError p`.
  have hSym :=
    sumcheck_hasSoundnessError (𝔽 := 𝔽) (n := n) st_sym P_sym hClaim_sym
  -- Pointwise transport: eval-form acceptance ⟹ symbolic acceptance.
  have hImp : ∀ r : Fin n → 𝔽,
      sumcheckProtocolEvalForm.verifierAccepts st
        (generateTranscript sumcheckProtocolEvalForm st P r) →
      sumcheckProtocol.verifierAccepts st_sym
        (generateTranscript sumcheckProtocol st_sym P_sym r) :=
    fun r => evalForm_accepts_implies_symbolic_accepts st hUni P r
  -- probAccept eval ≤ probAccept symbolic via prob_over_challenges_mono.
  have hMono :
      probAccept (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := d)) st P
        ≤ probAccept (sumcheckProtocol (𝔽 := 𝔽) (n := n)) st_sym P_sym := by
    unfold probAccept
    exact prob_over_challenges_mono (𝔽 := 𝔽) (n := n) hImp
  -- Bound: soundnessError = n * maxIndDegree / |𝔽| ≤ n * d / |𝔽| under uniform-d.
  have hBound : soundnessError st.polynomial
      ≤ (n : ℚ) * (d : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
    unfold soundnessError
    have hMax_le : (maxIndDegree st.polynomial : ℚ) ≤ (d : ℚ) := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · -- n = 0: maxIndDegree = sup over empty Fin 0 = 0.
        subst hn0
        simp [maxIndDegree]
      · have := maxIndDegree_eq_of_uniform (𝔽 := 𝔽) hUni hnpos
        rw [this]
    have hN_nn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    have hF_nn : (0 : ℚ) ≤ (fieldSize (𝔽 := 𝔽) : ℚ) := by
      exact_mod_cast Nat.zero_le _
    have hMul_le : (n : ℚ) * (maxIndDegree st.polynomial : ℚ)
        ≤ (n : ℚ) * (d : ℚ) := by
      exact mul_le_mul_of_nonneg_left hMax_le hN_nn
    exact div_le_div_of_nonneg_right hMul_le hF_nn
  -- Glue.
  exact le_trans hMono (le_trans hSym hBound)

/-- Under uniform-d, `(n * d) / |𝔽|` coincides with
`soundnessError st.polynomial`. (Sanity-check corollary, not used in
the main lift.) -/
theorem soundnessError_eq_of_uniform
    {𝔽 : Type} {n d : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {p : CMvPolynomial n 𝔽}
    (hUni : UniformDegreePoly d p) (hn : 0 < n) :
    soundnessError p = (n : ℚ) * (d : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ) := by
  unfold soundnessError
  rw [maxIndDegree_eq_of_uniform (𝔽 := 𝔽) hUni hn]
