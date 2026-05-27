/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic

/-!
# Hiding — abstract security obligation

This file declares `HasHiding`. The property: a commitment, together with
openings at a chosen index set, reveals nothing about the values at
*unopened* positions beyond what those openings disclose.

The standard distinguishing game:
  1. Adversary picks two messages `m₀, m₁` of the same length and an
     index set `I` it wants opened.
  2. Challenger samples `b ←$ {0,1}`, commits to `m_b`, opens at `I`.
  3. Adversary, given the commitment + openings, outputs a guess `b'`.
  4. Advantage = `|Pr[b' = b] − 1/2|`.

The bound is "bounded-query hiding": hiding holds as long as the
adversary sees at most some `Q` openings (which becomes the IOPP's query
complexity in the compiled protocol). The bound captures both `Q` (the
number of openings) and `q` (the underlying oracle/computational budget).

Model-specific instances live under:
  * `VectorCommitment/Properties/Probability/Instances/HidingROM.lean`
  * `VectorCommitment/Properties/StandardModel/Instances/…`        (reserved)
-/

/-- Hiding obligation. -/
class HasHiding (V : Type) [VectorCommitment V] where
  /-- The hiding-game adversary. The model's instance defines the
      precise game shape (number of openings revealed, computational
      model, etc.). -/
  HidingAdversary : (κ q : ℕ) → Type
  /-- The adversary's distinguishing advantage in the hiding game. -/
  hidingAdvantage : ∀ {κ q}, HidingAdversary κ q → ENNReal
  /-- The model-specific upper bound.
      ROM Merkle with salt size `s`, message length `ℓ`, `Q` openings:
        `ε_hide ≤ q · ℓ / 2 ^ s + Q² / 2 ^ s`
        (oracle hits a salted-leaf input + revealed-salt collisions).
      Standard-model under one-way `H`: `Adv_H^OW(B)` for some reduction
      `B`. -/
  hidingError : (κ q : ℕ) → ENNReal
  /-- The central guarantee. -/
  hiding_bound :
    ∀ {κ q} (A : HidingAdversary κ q),
      hidingAdvantage A ≤ hidingError κ q
