/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Trait
import Mathlib.Data.ENNReal.Basic

/-!
# Straightline extractability — abstract security obligation

This file declares `HasStraightlineExtractor`. The property: there exists
an extractor that, reading only the model's "trace" (RO query log in the
ROM, internal-state record in the standard model), outputs a candidate
underlying string `m̃` such that every accepting opening the adversary
later produces is consistent with `m̃` — i.e. `value[i] = m̃[i]` at every
opened position.

This is strictly stronger than position binding. Position binding gives a
*partial* function on opened positions; extractability gives a *total*
string fixed before any opening. The total string is what an IOP/PCP
soundness reduction needs to quantify over.

"Straightline" = the extractor does not rewind the adversary; it reads
the model's trace once and outputs. This is what lets the extractor
compose with Fiat–Shamir (round-by-round knowledge soundness), per
[eprint 2024/1434, Untangling the Security of Kilian's Protocol].

Model-specific instances live under:
  * `VectorCommitment/Properties/Probability/Instances/ExtractabilityROM.lean`
  * `VectorCommitment/Properties/StandardModel/Instances/…`            (reserved)
-/

/-- Straightline extractability obligation. Game parameters as in
    `HasPositionBinding`. -/
class HasStraightlineExtractor (V : Type) [VectorCommitment V] where
  /-- The extraction-game adversary. The model's instance defines what
      "extraction failure" means concretely: typically, the adversary
      produces an accepting opening at some index whose revealed value
      differs from what the model's straightline extractor outputs from
      the trace. -/
  ExtractionAdversary : (κ q : ℕ) → Type
  /-- The probability that running `A` under the model's randomness
      yields a successful break of the extractor: an accepting opening
      whose value disagrees with the extractor's claim about that
      position. -/
  extractionFailureAdvantage : ∀ {κ q}, ExtractionAdversary κ q → ENNReal
  /-- The model-specific upper bound.
      ROM Merkle: `q * (q - 1) / 2 ^ (κ + 1)` — same collision bound as
        binding, since absent any RO collision the root pins down a unique
        tree and hence a unique `m̃`.
      Standard-model: a reduction-based bound to a knowledge or one-way
        assumption (no straightline form in general). -/
  extractionError : (κ q : ℕ) → ENNReal
  /-- The central guarantee. -/
  extraction_bound :
    ∀ {κ q} (A : ExtractionAdversary κ q),
      extractionFailureAdvantage A ≤ extractionError κ q
