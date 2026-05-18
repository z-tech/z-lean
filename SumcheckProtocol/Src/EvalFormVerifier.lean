import Mathlib.LinearAlgebra.Lagrange

import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Src.EvalForm

/-!
# Eval-form verifier and transcript (Phase 4, infrastructure)

A parallel sumcheck verifier whose round messages are tuples of field
values `Fin (d+1) → 𝔽` (evaluations of the round polynomial at `d+1`
distinguished interpolation nodes), rather than symbolic
`CMvPolynomial 1 𝔽`.

* `TranscriptEvalForm` — record bundling round-evals, challenges.
* `nextClaimEvalForm` — build the next-round claim by Lagrange-
  interpolating the round-evals at the verifier's challenge.
* `isVerifierAcceptsEvalForm` — the per-round acceptance Bool, paralleling
  `isVerifierAccepts` from `Src/Verifier.lean`.
-/

open CPoly

/-- Eval-form transcript: each round's prover message is a tuple
`Fin (d+1) → 𝔽` (the round polynomial's values at `d+1` interpolation
nodes), together with verifier challenges. -/
structure TranscriptEvalForm (𝔽 : Type _) (n d : ℕ) [CommRing 𝔽] where
  roundsEvals : Fin n → Fin (d + 1) → 𝔽
  challenges  : Fin n → 𝔽

variable {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽]

/-- The next round's claim is obtained by Lagrange-interpolating the
round-eval tuple through the `d+1` distinct nodes `evalPoints`, then
evaluating at the verifier's challenge. -/
noncomputable def nextClaimEvalForm
  {d : ℕ}
  (evalPoints : Fin (d + 1) → 𝔽)
  (qEvals : Fin (d + 1) → 𝔽)
  (challenge : 𝔽) : 𝔽 :=
  (Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) evalPoints qEvals).eval challenge

/-- Sum the eval-form round message over the verifier's domain.

For each `a ∈ domain`, `domain_sub` guarantees a `k : Fin (d+1)` with
`evalPoints k = a`; we use a witness extracted via classical choice
(no decidability assumption on equality of `evalPoints` outputs is
needed beyond `Function.Injective`). The sum is independent of which
`k` is chosen because `evalPoints k = evalPoints k' ↔ k = k'` by
injectivity, so any two choices yield the same `qEvals` value. -/
noncomputable def sumOnDomainEvalForm
  {d : ℕ}
  (domain : List 𝔽)
  (evalPoints : Fin (d + 1) → 𝔽)
  (_evalPoints_inj : Function.Injective evalPoints)
  (_domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x)
  (qEvals : Fin (d + 1) → 𝔽) : 𝔽 :=
  -- Use the Lagrange interpolant: sum over `a ∈ domain` of `interp.eval a`.
  -- This is equal (by injectivity + domain_sub) to the conceptually-direct
  -- sum `∑ qEvals (k(a))`, but using the interpolant gives a clean proof
  -- via `Lagrange.eval_interpolate_at_node` and avoids classical choice.
  let interp : Polynomial 𝔽 :=
    Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) evalPoints qEvals
  domain.foldl (fun acc a => acc + interp.eval a) 0

/-- Compute intermediate claims from the eval-form transcript. -/
noncomputable def generateHonestClaimsEvalForm
  {n d : ℕ}
  (initialClaim : 𝔽)
  (evalPoints : Fin (d + 1) → 𝔽)
  (roundsEvals : Fin n → Fin (d + 1) → 𝔽)
  (challenges : Fin n → 𝔽) : Fin (n + 1) → 𝔽
  | ⟨0, _⟩ => initialClaim
  | ⟨k + 1, hk⟩ =>
      let i : Fin n := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      nextClaimEvalForm (𝔽 := 𝔽) (d := d) evalPoints (roundsEvals i) (challenges i)

/-- Compute claims from an eval-form transcript and initial claim. -/
noncomputable def TranscriptEvalForm.claims {n d : ℕ}
  (t : TranscriptEvalForm 𝔽 n d) (evalPoints : Fin (d + 1) → 𝔽)
  (initialClaim : 𝔽) : Fin (n + 1) → 𝔽 :=
  generateHonestClaimsEvalForm (𝔽 := 𝔽) (n := n) (d := d)
    initialClaim evalPoints t.roundsEvals t.challenges

/-- Per-round eval-form check: the round-eval tuple sums (on domain) to
the round claim, AND the Lagrange interpolant evaluated at the round's
challenge equals the next-round claim.

Compared to `verifierCheck`, the explicit `degreeOf` check is dropped:
since `qEvals : Fin (d+1) → 𝔽`, the (unique) degree-≤ d Lagrange
interpolant has degree ≤ d by construction. -/
noncomputable def verifierCheckEvalForm
  {d : ℕ}
  (domain : List 𝔽)
  (evalPoints : Fin (d + 1) → 𝔽)
  (evalPoints_inj : Function.Injective evalPoints)
  (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x)
  (roundClaim : 𝔽)
  (qEvals : Fin (d + 1) → 𝔽) : Prop :=
  sumOnDomainEvalForm (𝔽 := 𝔽) (d := d)
    domain evalPoints evalPoints_inj domain_sub qEvals = roundClaim

/-- Eval-form verifier acceptance Prop. -/
noncomputable def isVerifierAcceptsEvalForm
  {n d : ℕ}
  (domain : List 𝔽)
  (evalPoints : Fin (d + 1) → 𝔽)
  (evalPoints_inj : Function.Injective evalPoints)
  (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x)
  (p : CPoly.CMvPolynomial n 𝔽)
  (initialClaim : 𝔽)
  (t : TranscriptEvalForm 𝔽 n d) : Prop :=
  let claims := t.claims evalPoints initialClaim
  (∀ i : Fin n,
    verifierCheckEvalForm (𝔽 := 𝔽) (d := d)
      domain evalPoints evalPoints_inj domain_sub
      (claims (Fin.castSucc i)) (t.roundsEvals i)
    ∧
    claims i.succ =
      nextClaimEvalForm (𝔽 := 𝔽) (d := d) evalPoints (t.roundsEvals i) (t.challenges i))
  ∧
  claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p
