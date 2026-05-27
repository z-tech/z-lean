import VectorCommitment.Properties.Probability.RandomOracle
import Mathlib.Data.ENNReal.Basic

/-!
# RO probability lemmas: collision bound and fresh-query uniformity

This file states the two textbook probability facts the four
ROM-instance files (`BindingROM`, `ExtractabilityROM`, `HidingROM`,
`EquivocationROM`) all reduce to:

* **`birthdayBound`** — among `n` independent uniform samples from a
  finite set `R`, the probability that two of the samples coincide is
  at most `n · (n - 1) / (2 · |R|)`. Specialised to `R = List.Vector
  Bool κ` this is the classic `n² / 2^(κ+1)` form.

* **`RO_fresh_uniform`** — in the lazy-sampling RO, the response to a
  query not yet in the cache is distributed uniformly on `spec.Range`.

## Status

Both lemmas are stated and their proofs are **deferred with `sorry`**.
The statements are precise; closing the bodies requires standard
mathlib PMF / outer-measure / union-bound machinery and is a real but
non-novel probability-library project.

The instance files (`BindingROM`, `ExtractabilityROM`, `HidingROM`,
`EquivocationROM`) treat these as known facts and propagate their
sorries upward. Closing the proofs here will close all four
probabilistic security theorems.
-/

namespace VectorCommitment.Probability

open OracleComp

/-- The concrete error expression every ROM instance carries.
    `κ` is the digest bit-length; `q` is the adversary's RO query budget. -/
noncomputable def collisionBound (κ q : Nat) : ENNReal :=
  (q * (q - 1) : ENNReal) / 2 ^ (κ + 1)

/-- **Birthday bound.** Among `n` independent uniform samples from a
    finite, nonempty range `R`, the probability that some pair of
    samples coincides is at most `n · (n - 1) / (2 · |R|)`.

    *Specialisation:* when `R = List.Vector Bool κ` (`|R| = 2^κ`) the
    bound becomes `collisionBound κ n`.

    *Proof:* union bound over `(n choose 2)` pairs, each pair coinciding
    with probability `1 / |R|` by independence of uniform samples.
    Deferred (see file-level docstring). -/
theorem birthdayBound (n : Nat) {R : Type} [Fintype R] [Nonempty R] :
    (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
      {f | ∃ i j : Fin n, i ≠ j ∧ f i = f j}
      ≤ (n * (n - 1) : ENNReal) / (2 * Fintype.card R) := by
  sorry

/-- Specialisation to κ-bit digests: the birthday bound is exactly
    `collisionBound κ n = n(n-1)/2^(κ+1)`. Reduction to `birthdayBound`. -/
theorem birthdayBound_kappa (κ n : Nat) {R : Type}
    [Fintype R] [Nonempty R] (h_card : Fintype.card R = 2 ^ κ) :
    (PMF.uniformOfFintype (Fin n → R)).toOuterMeasure
      {f | ∃ i j : Fin n, i ≠ j ∧ f i = f j}
      ≤ collisionBound κ n := by
  -- Reduce to `birthdayBound`, then rewrite `2 * |R| = 2^(κ+1)` via h_card.
  refine (birthdayBound n).trans ?_
  unfold collisionBound
  rw [h_card]
  -- Goal: ↑n * (↑n - 1) / (2 * ↑(2^κ)) ≤ ↑n * (↑n - 1) / 2^(κ+1)
  -- Reduce to equality of denominators.
  have h_denom : (2 : ENNReal) * ((2 ^ κ : ℕ) : ENNReal) = (2 : ENNReal) ^ (κ + 1) := by
    push_cast
    rw [pow_succ, mul_comm]
  rw [h_denom]

/-- **Fresh-query uniformity.** In the lazy-sampling RO, the response
    to a query *not yet in the cache* is distributed uniformly on
    `spec.Range`, projecting `(value, ending log)` to just the value.

    *Proof:* immediate from the `none` branch of `OracleComp.query`. -/
theorem RO_fresh_uniform {spec : OracleSpec}
    (d : spec.Domain) (log : QueryLog spec)
    (h_novel : log.lookup d = none) :
    ((OracleComp.query d log).map Prod.fst) =
      PMF.uniformOfFintype spec.Range := by
  show ((OracleComp.query d log).map Prod.fst) = _
  unfold OracleComp.query
  rw [h_novel]
  -- Goal: ((PMF.uniformOfFintype spec.Range).bind (fun r => PMF.pure (r, log.append d r))).map Prod.fst = _
  rw [PMF.map_bind]
  -- Now each summand: (PMF.pure (r, log.append d r)).map Prod.fst = PMF.pure r
  simp only [PMF.pure_map]
  -- Goal: (PMF.uniformOfFintype spec.Range).bind (fun r => PMF.pure r) = _
  exact PMF.bind_pure _

end VectorCommitment.Probability
