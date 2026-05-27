import VectorCommitment.Src.Merkle.Scheme

-- Mirrors ark-mt/src/capability.rs. Optional capabilities (DESIGN.md §1, rows 9 & 11).

class LocallyUpdatable (V : Type) where
  Trapdoor : Type
  Symbol : Type
  Committed : Type
  update : V → Trapdoor → Committed → Nat → Symbol → Committed × Trapdoor

class LeavesAccessible (V : Type) where
  Trapdoor : Type
  Symbol : Type
  leaves : V → Trapdoor → List Symbol

class Equivocable (V : Type) where
  Trapdoor : Type
  Symbol : Type
  Committed : Type
  Opening : Type
  OpeningProof : Type
  simulateRoot    : V → ULift.{0} UInt64 → Committed × Trapdoor
  simulateOpening : V → Trapdoor → Opening → OpeningProof
