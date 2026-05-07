-- Mirrors ark-mt/src/hasher.rs:33-58. See VC/DESIGN.md §3.1.

class MerkleHasher (H : Type) where
  Symbol : Type
  Digest : Type
  Salt   : Type
  decEqDigest : DecidableEq Digest
  defaultSalt : Inhabited Salt
  /-- Sample a fresh salt from a finite seed. -/
  sampleSalt : H → ULift UInt64 → Salt
  /-- ρ(symbol, salt) at a leaf. -/
  hashLeaf   : H → Symbol → Salt → Digest
  /-- ρ(child₁, …, childₖ) at an internal vertex. -/
  hashNodes  : H → List Digest → Digest
