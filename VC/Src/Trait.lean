-- The abstract `VectorCommitment` typeclass; mirrors ark-vc/src/vc.rs.
-- See VC/DESIGN.md §3.3.

class VectorCommitment (V : Type) where
  Alphabet         : Type
  Index            : Type
  UniversalParams  : Type
  CommitterKey     : Type
  VerifierKey      : Type
  Commitment       : Type
  CommitmentState  : Type
  Proof            : Type
  setup  : (maxLen maxQueries : Nat) → ULift UInt64 → UniversalParams
  trim   : UniversalParams → (len queries : Nat) → CommitterKey × VerifierKey
  commit : CommitterKey → List Alphabet → Commitment × CommitmentState
  «open» : CommitterKey → List Alphabet → Commitment → List Index → List Alphabet →
           CommitmentState → Proof
  check  : VerifierKey → Commitment → List Index → List Alphabet → Proof → Bool

-- Hiding extension. Mirrors ark-vc/src/vc.rs `HidingVectorCommitment` trait.
class HidingVectorCommitment (V : Type) extends VectorCommitment V where
  setup_hiding  : (maxLen maxQueries : Nat) → ULift UInt64 →
                  VectorCommitment.UniversalParams V
  trim_hiding   : VectorCommitment.UniversalParams V → (len queries : Nat) →
                  VectorCommitment.CommitterKey V × VectorCommitment.VerifierKey V
  commit_hiding : VectorCommitment.CommitterKey V → List (VectorCommitment.Alphabet V) →
                  ULift UInt64 →
                  VectorCommitment.Commitment V × VectorCommitment.CommitmentState V
  open_hiding   : VectorCommitment.CommitterKey V → List (VectorCommitment.Alphabet V) →
                  VectorCommitment.Commitment V → List (VectorCommitment.Index V) →
                  List (VectorCommitment.Alphabet V) → VectorCommitment.CommitmentState V →
                  VectorCommitment.Proof V
  check_hiding  : VectorCommitment.VerifierKey V → VectorCommitment.Commitment V →
                  List (VectorCommitment.Index V) → List (VectorCommitment.Alphabet V) →
                  VectorCommitment.Proof V → Bool
