/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Extractability
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Theorems.Extractability

/-!
# ROM instance: straightline extractability for RO-derived Merkle commitments

Discharges `HasStraightlineExtractor (MerkleCommitment (ROHasherValue κ) S)`
for every digest length `κ` and Merkle shape `S`, in the random-oracle
model.

## What straightline extractability adds over binding

Binding gives a *partial* function on opened positions; extractability
upgrades this to a *total* string `m̃` fixed before any opening — what
IOP/PCP soundness reductions actually need (per
[eprint 2024/1434, Theorem 5.1]).

In the ROM, the straightline extractor reads the `QueryLog`
(`Properties/Probability/RandomOracle.lean`): given a committed root,
walk the cache to find the query whose response is the root, recurse on
its children, and so on. Any subtree the prover never queried becomes
"⊥", and the prover cannot open into it without finding a hash
collision.

## Reduction sketch

Same shape as binding:

1. Bad-event decomposition: extraction failure ⇒ collision OR
   structural-extractability violation.
2. Collision case bounded by `Probability.birthdayBound_kappa`.
3. Structural case ruled out by `mt_multi_extractability` from
   `Properties/Theorems/Extractability.lean` (under
   collision-free hashes the extractor's output uniquely determines
   `m̃`).

## Open work for the student

* **`extractionFailureAdvantage`**: define the probability that the
  adversary produces an accepting opening at some index `i` whose
  revealed value disagrees with the value the straightline extractor
  outputs for `i`, given the adversary's RO trace. Requires defining
  the extractor itself — a function `QueryLog → Commitment → Index →
  Option Alphabet` that walks the cache.

* **`extraction_bound`**: discharge the reduction sketch. Same
  collision bound as binding (`q · (q - 1) / 2^(κ + 1)`); the structural
  case invokes `mt_multi_extractability`.
-/

namespace VectorCommitment.Probability.Instances

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- Straightline extractability for the RO-derived Merkle commitment. -/
noncomputable instance :
    HasStraightlineExtractor (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  ExtractionAdversary := fun _ _ =>
    OracleComp (ROHasher.MerkleROSpec κ)
      (VectorCommitment.Commitment (MerkleCommitment (ROHasher.ROHasherValue κ) S) ×
       List (VectorCommitment.Index (MerkleCommitment (ROHasher.ROHasherValue κ) S)) ×
       List (VectorCommitment.Alphabet (MerkleCommitment (ROHasher.ROHasherValue κ) S)) ×
       VectorCommitment.Proof (MerkleCommitment (ROHasher.ROHasherValue κ) S))
  extractionFailureAdvantage := sorry
  extractionError := fun _ q => Probability.collisionBound κ q
  extraction_bound := sorry

end VectorCommitment.Probability.Instances
