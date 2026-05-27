/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic

/-!
# Equivocation — abstract security obligation

This file declares `HasEquivocation`. The property: there exists a
*simulator pair* `(RootSim, OpeningSim)` — operating in whatever
"trapdoor" the model provides (programmable RO for ROM Merkle; trapdoor
key for algebraic commitments like Pedersen / KZG) — such that for every
adversary the two distributions

  Real:  (C, td) ← Commit(m);  π ← Open(td, I);   output (C, m[I], π)
  Ideal: (C, st) ← RootSim();  π ← OpeningSim(st, I, m[I]);  output (...)

are computationally close.

This is strictly stronger than hiding. A hiding commitment merely
doesn't leak `m`; an equivocable commitment is one the simulator can
commit *without knowing `m`* and later open arbitrarily. The stronger
property is what a zero-knowledge argument's simulator uses: it doesn't
hold the witness, so it commits blind and opens to whatever the IOPP
simulator hands it.

**Not all VCs are equivocable.** Merkle commitments achieve equivocation
only in the ROM, via RO programming. Hash-based commitments in the
*standard model* cannot be equivocable — this is a mathematical fact,
not a formalization limitation. Algebraic commitments (Pedersen, KZG)
achieve equivocation in the standard model under their own algebraic
assumptions.

Model-specific instances live under:
  * `VectorCommitment/Properties/Probability/Instances/EquivocationROM.lean`
  * `VectorCommitment/Properties/StandardModel/Instances/EquivocationPedersen.lean`
        (reserved — would require Pedersen, not Merkle)
-/

/-- Equivocation obligation. -/
class HasEquivocation (V : Type) [VectorCommitment V] where
  /-- The equivocation-game distinguisher. The model's instance defines
      the simulator `(RootSim, OpeningSim)` and the game shape (how many
      real-vs-simulated transcripts the distinguisher sees). -/
  EquivocationAdversary : (κ q : ℕ) → Type
  /-- The distinguisher's advantage in the real-vs-ideal experiment. -/
  equivocationAdvantage : ∀ {κ q}, EquivocationAdversary κ q → ENNReal
  /-- The model-specific upper bound.
      ROM Merkle: `Q · d · q / 2 ^ κ + Q² / 2 ^ s` —
        programming-collision (the adversary already queried a node the
        simulator wants to program) plus salt freshness.
      Standard-model Pedersen: a DL-game reduction. -/
  equivocationError : (κ q : ℕ) → ENNReal
  /-- The central guarantee. -/
  equivocation_bound :
    ∀ {κ q} (A : EquivocationAdversary κ q),
      equivocationAdvantage A ≤ equivocationError κ q
