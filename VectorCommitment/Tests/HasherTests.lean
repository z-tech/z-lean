import Mathlib.Data.ZMod.Basic
import VectorCommitment.Src.Merkle.Hasher

-- Demo hasher over ZMod 65521 (largest prime under 2^16). Computable; suitable
-- for `native_decide` round-trips. Real hashers (Poseidon2, Blake3) are
-- user-supplied.

def DemoHasher : Type := Unit

instance : Inhabited DemoHasher := ⟨()⟩

instance : MerkleHasher DemoHasher where
  Symbol := ZMod 65521
  Digest := ZMod 65521
  Salt := Unit
  decEqDigest := inferInstance
  defaultSalt := ⟨()⟩
  sampleSalt _ _ := ()
  hashLeaf _ x _ := x * 31 + 17
  hashNodes _ cs := cs.foldl (fun acc d => acc * 31 + d) 1
