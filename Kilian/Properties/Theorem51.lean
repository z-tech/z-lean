/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Src.Honest
import VectorCommitment.Src.Security.PositionBinding

/-!
# Theorem 5.1 — soundness of Kilian's protocol

Statement of the main soundness theorem from
[eprint 2024/1434, *Untangling the Security of Kilian's Protocol*](https://eprint.iacr.org/2024/1434)
(Chiesa, Dall'Agnol, Guan, Spooner, Yogev), Section 5.

## The theorem

For a PCP `P` with soundness error `ε_PCP(n)` and proof length `ℓ(n)`,
and a vector commitment `V` with position-binding error `ε_VC(κ, q)`,
Kilian's compiled 3-message argument satisfies, for every adversary `A`
and every `ε > 0`:

  argumentError A n ≤ ε_PCP(n) + ε_VC(κ, q) + ε.

## Proof structure (per 2024/1434, §5.2)

1. **The reductor `R` (Construction 5.5).** Given an argument prover
   `A`, the reductor samples `N = ℓ/ε` independent verifier challenges,
   runs `A` on each, and post-processes the resulting transcripts into
   a single candidate PCP string `Π̃`. Concretely: at each position the
   reductor records the values `A` revealed at that position across the
   `N` runs, then majority-votes (or samples one — the exact rule
   matters only for constants).

2. **Lemma 5.3** (the technical core). Bound the probability of the bad
   event `B = {Π̃ rejects ∧ argument accepts ∧ VC openings check}` by
   `ε_VC(κ, q) + ε`. Two subcases:

   * **`q ∈ Q ∩ Q̃` with disagreeing answers.** The argument prover
     and the reductor's witness disagree on the value at some queried
     position both of them sampled. The disagreement, together with
     both openings checking under `V.check`, is a position-binding
     break — bounded by `bindingError κ q` via `[HasPositionBinding V]`.

   * **`q ∈ Q \ Q̃`** (the verifier queried a position the reductor
     never saw). Bounded by `ℓ/N = ε` via the elementary inequality
     `δ · (1 - δ)^N ≤ 1/N` and a union bound over `ℓ` positions.

3. **Total probability decomposition.**

       Pr[arg accepts ∧ x ∉ L]
         = Pr[arg accepts ∧ PCP-V accepts on Π̃]
         + Pr[arg accepts ∧ PCP-V rejects on Π̃]
         ≤ ε_PCP(n) + Lemma 5.3.

   Yielding the claimed bound.

## Status

The theorem is stated against the abstract `HasPositionBinding`
typeclass, so the `bindingError` term is a real (non-sorry) value as
soon as a ROM-instance under
`VectorCommitment/Properties/Probability/Instances/BindingROM.lean`
closes its sorries. The theorem's proof body itself is deferred (two
sorries: `argumentError`, `kilian_soundness`); closing them is the next
major chunk of work and depends on having the cryptographic experiment
infrastructure (an `Adversary` type richer than the placeholder below,
plus a probability measure on its output).
-/

namespace Kilian

/-- A Kilian-protocol adversary against the compiled 3-message argument.

    Currently a placeholder (`Unit`-shaped) to support the abstract
    statement of Theorem 5.1. The full type is an interactive
    computation that produces a `(Commitment, Values, Proof)` reply to
    any verifier challenge; expanding this requires either an
    `OracleComp`-style monad or an explicit transcript-prefix
    representation. Future work. -/
structure Adversary (P V : Type) [PCPSystem P] [VectorCommitment V] where
  /-- Placeholder field. -/
  placeholder : Unit

variable {P V : Type} [PCPSystem P] [VectorCommitment V] [HasPositionBinding V]
  [KilianCompatible P V]

/-- The compiled argument's soundness error against an adversary `A`
    for statements of size `n`.

    The honest definition is the probability that `A`, when run against
    the verifier on a non-instance of size `n`, makes the verifier
    accept. Currently `:= sorry` (placeholder ENNReal value) until the
    `Adversary` type is fleshed out and the experiment defined. -/
noncomputable def argumentError (A : Adversary P V) (n : ℕ) : ENNReal :=
  sorry

/-- **Theorem 5.1 of [eprint 2024/1434].**
    Kilian's compiled argument from a PCP `P` and a vector commitment
    `V` has soundness error bounded by `ε_PCP(n) + ε_VC(κ, q) + ε`.

    Binds on `[HasPositionBinding V]` abstractly, so the `bindingError`
    term is a real model-instantiated value (ROM, standard-model
    Pedersen, etc.) at the use site.

    Proof body deferred — see file-level docstring for the structure. -/
theorem kilian_soundness
    (κ q n : ℕ) (ε : ENNReal) (A : Adversary P V) :
    argumentError A n ≤
      PCPSystem.soundnessError P n +
      HasPositionBinding.bindingError (V := V) κ q + ε := by
  sorry

end Kilian
