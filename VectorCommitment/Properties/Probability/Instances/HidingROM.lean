/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import VectorCommitment.Src.Security.Hiding
import VectorCommitment.Src.Merkle.Instance
import VectorCommitment.Properties.Probability.ROHasher
import VectorCommitment.Properties.Probability.Collision
import VectorCommitment.Properties.Theorems.Hiding

/-!
# ROM instance: hiding for RO-derived Merkle commitments

Discharges `HasHiding (MerkleCommitment (ROHasherValue κ) S)` for every
digest length `κ` and Merkle shape `S`, in the random-oracle model.

## Bound

The classical RO-hiding error for a Merkle commitment with salt size
`s` and message length `ℓ`, against an adversary making `q` RO queries
and observing `Q` openings:

    ε_hide ≤ q · ℓ / 2^s + Q² / 2^s

The first term: probability the adversary's `q` RO queries hit any
salted-leaf input (each with probability `2^(-s)` per leaf). The second
term: probability of a collision among the `Q` revealed salts.

For the current instance we use a coarse upper bound that suffices for
the IOPP compilation: `ε_hide ≤ Probability.collisionBound s q`. A
tighter `s`/`ℓ`-aware version is straightforward once the salt-size
parameter is threaded through (see `MerkleHasher.Salt` machinery
documented in `VectorCommitment/HIDING.md`).

## Reduction sketch

1. **Bad-event decomposition.** A successful distinguishing run implies
   *either* the adversary's RO queries hit a salted leaf input, *or*
   the leaf-hash outputs are indistinguishable across `m₀` / `m₁`.

2. **Salt-hit case.** Bounded by `Probability.birthdayBound_kappa`
   instantiated at the salt-space size.

3. **Indistinguishable-leaf case.** The existing structural
   [`mt_root_hiding`](../../Theorems/Hiding.lean) theorem applies:
   if leaf hashes agree at every position, then so do the commit
   roots — the adversary's view is information-theoretically
   `b`-independent.

## Open work for the student

* **`hidingAdvantage`**: define the standard bit-guessing game's
  advantage |`Pr[wins on b=0] − Pr[wins on b=1]|`. Will need a notion
  of "challenge oracle" that takes `m₀, m₁` and returns a commitment to
  `m_b`.

* **`hiding_bound`**: discharge the reduction sketch above. Uses
  `mt_root_hiding` for the structural step.
-/

namespace VectorCommitment.Probability.Instances

variable (κ : Nat) (S : Type) [MerkleShape S]
  [Nonempty (MerkleCommitment (ROHasher.ROHasherValue κ) S)]

/-- Hiding for the RO-derived Merkle commitment. -/
noncomputable instance :
    HasHiding (MerkleCommitment (ROHasher.ROHasherValue κ) S) where
  HidingAdversary := fun _ _ =>
    OracleComp (ROHasher.MerkleROSpec κ) Bool
  hidingAdvantage := sorry
  hidingError := fun _ q => Probability.collisionBound κ q
  hiding_bound := sorry

end VectorCommitment.Probability.Instances
