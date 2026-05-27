/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic

/-!
# Position binding — abstract security obligation

This file declares the model-agnostic typeclass `HasPositionBinding`.
The property: no adversary, in any computational model the instance
specifies, can produce two distinct accepting openings of the same
position of a single commitment.

A security model discharges this class by:
  * supplying an `Adversary` type capturing its computational shape
    (ROM: an `OracleComp` returning a candidate break;
     standard model: a runtime-bounded reduction to an assumption),
  * defining the adversary's binding advantage,
  * exhibiting an `Error` bound and proving the advantage is below it.

Model-specific instances live under:
  * `VectorCommitment/Properties/Probability/Instances/BindingROM.lean`
  * `VectorCommitment/Properties/StandardModel/Instances/BindingCR.lean`  (reserved)

Higher-level protocol theorems (Kilian's Theorem 5.1, BCS soundness,
IOPP compilations) consume this class abstractly and stay
model-neutral.
-/

namespace VectorCommitment.Security

open VectorCommitment

/-- A position-binding break: a commitment together with two singleton
    openings of the same position that disagree on the revealed value.

    Each opening is `(value, proof)`; the values differ; the verifier
    accepts both. Validity against a specific `vk` is captured by
    `BindingBreak.IsValid` below.

    A break does not by itself carry the verifier key — the binding game
    samples the key and then asks the adversary to produce a break that
    is valid against it. -/
structure BindingBreak (V : Type) [VectorCommitment V] where
  commitment : Commitment V
  index      : Index V
  value₀     : Alphabet V
  value₁     : Alphabet V
  proof₀     : Proof V
  proof₁     : Proof V

/-- A break is *valid* against verifier key `vk` when both singleton
    openings pass `check` and reveal distinct values. -/
def BindingBreak.IsValid {V : Type} [VectorCommitment V]
    (vk : VerifierKey V) (b : BindingBreak V) : Prop :=
  b.value₀ ≠ b.value₁ ∧
  check vk b.commitment [b.index] [b.value₀] b.proof₀ = true ∧
  check vk b.commitment [b.index] [b.value₁] b.proof₁ = true

end VectorCommitment.Security

/-- Position-binding obligation, layered on top of the operational
    `VectorCommitment` interface.

    Game parameters:
      * `κ` — security parameter (digest length in the ROM, group
              order / hash output length in the standard model).
      * `q` — adversary resource budget (RO queries in the ROM,
              runtime bound in the standard model).

    An `instance` for a concrete commitment type `V` under a chosen
    security model discharges the four fields below. -/
class HasPositionBinding (V : Type) [VectorCommitment V] where
  /-- The adversary type at security parameter `κ` and resource
      budget `q`.

      Each model picks this concretely:
        * ROM: `OracleComp spec (BindingBreak V)` for the RO spec.
        * Standard model: a runtime-bounded reduction returning a
          `BindingBreak V` together with a witness to the assumption
          break it forces. -/
  BindingAdversary : (κ q : ℕ) → Type
  /-- The probability that running `A` yields a *valid* break, taken
      over `A`'s own coins together with any randomness the model
      supplies (lazy oracle samples in the ROM, assumption-game coins
      in the standard model). -/
  bindingAdvantage : ∀ {κ q}, BindingAdversary κ q → ENNReal
  /-- The model-specific upper bound on `bindingAdvantage`.

      Examples:
        * ROM Merkle:        `q * (q - 1) / 2 ^ (κ + 1)`  (birthday).
        * Standard-model CR: `Adv_H^CR(B)` for some reduction `B`. -/
  bindingError : (κ q : ℕ) → ENNReal
  /-- The central guarantee: every adversary's advantage is at most
      the model-specific error term. -/
  binding_bound :
    ∀ {κ q} (A : BindingAdversary κ q),
      bindingAdvantage A ≤ bindingError κ q
