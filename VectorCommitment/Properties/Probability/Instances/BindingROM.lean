/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.PositionBinding
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Theorems.Binding

/-!
# ROM instance: position binding for RO-derived Merkle commitments

Discharges `HasPositionBinding (MerkleCommitment (ROHasherValue κ) S)`
for every digest length `κ` and Merkle shape `S`, in the random-oracle
model.

## Reduction sketch

The bound `q · (q - 1) / 2^(κ + 1)` is derived in three steps:

1. **Bad-event decomposition.** A valid binding break implies *either*
   the RO had a collision among the queries made during the experiment,
   *or* the break exists under collision-free hashing.

2. **Collision case.** Probability bounded by
   `Probability.birthdayBound_kappa` from `Collision.lean`.

3. **Structural case.** Impossible by the Option-B
   [`mt_binding`](../../Theorems/Binding.lean) theorem: under
   `Function.Injective2 hashLeaf` and `Function.Injective hashNodes`,
   no two distinct accepting openings of the same position exist.

The two `sorry`s below — `bindingAdvantage` and `binding_bound` —
implement this reduction; closing them (modulo `birthdayBound`) gives
a complete ROM proof of position binding.

## Open work for the student

* **`bindingAdvantage`**: define the probability the adversary, when
  run from the empty query log, produces a `BindingBreak` valid against
  the verifier key derived from the sampled oracle. The shape:

      bindingAdvantage A :=
        (OracleComp.simulateQ A).toOuterMeasure
          {b : BindingBreak _ | b.IsValid vk_derived_from_oracle}

  Open question: how to derive `vk` from the oracle. One choice is to
  bake `setup` / `trim` into the experiment monadically; another is to
  parametrize the instance over a default `vk`. Discuss with the
  maintainer before committing.

* **`binding_bound`**: discharge the reduction sketch above. The
  collision case invokes
  `Probability.birthdayBound_kappa κ q (R := List.Vector Bool κ) (by simp)`;
  the structural case invokes `mt_binding` after extracting injectivity
  on the queried inputs from "no RO collision in the trace."
-/

namespace VectorCommitment.Probability.Instances

open VectorCommitment.Security

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- Position binding for the RO-derived Merkle commitment. -/
noncomputable instance :
    HasPositionBinding (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  BindingAdversary := fun _ _ =>
    OracleComp (ROHasher.MerkleROSpec κ)
      (BindingBreak (MerkleCommitment (ROHasher.ROHasherValue κ) S))
  bindingAdvantage := sorry
  bindingError := fun _ q => Probability.collisionBound κ q
  binding_bound := sorry

end VectorCommitment.Probability.Instances
