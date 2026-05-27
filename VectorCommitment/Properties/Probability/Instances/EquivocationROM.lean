/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Equivocation
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Theorems.Equivocation

/-!
# ROM instance: equivocation for RO-derived Merkle commitments

Discharges `HasEquivocation (MerkleCommitment (ROHasherValue κ) S)` in
the *programmable* random-oracle model.

## What this instance asserts

There exists a simulator pair `(RootSim, OpeningSim)`:

* `RootSim` outputs a uniformly-random placeholder root, no message
  committed.
* `OpeningSim`, given the placeholder root and an opening request
  `(I, m[I])`, *programs* the RO at the path/copath nodes so the
  reconstruction walks up to the placeholder root.

The (Real, Ideal) distributions are statistically close with bound

    ε_equiv ≤ Q · d · q / 2^κ + Q² / 2^s

where `Q` is the number of openings, `d = depth(S)`, `q` the
adversary's RO query budget, `s` the salt size. The first term is the
programming-collision event: the adversary already queried a node-input
the simulator wants to program. The second is salt freshness.

## Status

This is the lone substantive `sorry` in `Properties/Theorems/Equivocation.lean`
(the legacy statement returns `True`). Closing the ROM instance here
requires *first* extending the lazy-sampling RO model in
`Properties/Probability/RandomOracle.lean` with a **programmable**
variant — an `OracleComp` operation that pre-populates entries in
`QueryLog` before sampling continues from there. The skeleton is
straightforward; the rigorous coupling argument is the work.

## Reduction sketch

1. Build the simulator as an `OracleComp` that produces a fresh root,
   then on each opening request: pick a fresh salt, set leaf-input →
   placeholder digest, and program internal-node inputs along the path.
2. The bad event is "the adversary's distinguishing advantage."
3. Decompose into the union of: (a) programming-failure (programmed
   point already queried) and (b) salt-collision.
4. Both bounded by `Probability.birthdayBound_kappa` at the appropriate
   parameters.

## Open work for the student

This is the hardest of the four ROM instances. It depends on:

* **A programmable RO extension** to `OracleComp` — currently the model
  only supports lazy sampling, no programming. Suggested extension:
  expose `OracleComp.program : Domain → Range → OracleComp _ Unit` that
  inserts into the cache; prove that "for unqueried inputs, programmed
  ≡ lazy-sample" up to `q / |Range|` per programmed point.

* **The simulator construction** itself, plus the coupling argument
  showing real ≈ ideal.

* **Replacing the legacy `mt_equivocation := sorry`** in
  `Properties/Theorems/Equivocation.lean` with a real distributional
  statement — currently it returns `True`, which has no probabilistic
  content.
-/

namespace VectorCommitment.Probability.Instances

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- Equivocation for the RO-derived Merkle commitment. -/
noncomputable instance :
    HasEquivocation (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  EquivocationAdversary := fun _ _ =>
    OracleComp (ROHasher.MerkleROSpec κ) Bool
  equivocationAdvantage := sorry
  equivocationError := fun _ q => Probability.collisionBound κ q
  equivocation_bound := sorry

end VectorCommitment.Probability.Instances
