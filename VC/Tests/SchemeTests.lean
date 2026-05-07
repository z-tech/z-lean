import VC.Src.Merkle.Scheme
import VC.Tests.HasherTests

-- L1 round-trip tests for the demo hasher over `ZMod 65521` and `PerfectBinary`.

namespace VC.Tests.Scheme

open MerkleCommitment

/-- Helper: discard the validating constructor's error branch for tests. -/
private def mkOpening (indices : List Nat)
    (values : List (MerkleHasher.Symbol DemoHasher)) : Opening DemoHasher :=
  match Opening.new (H := DemoHasher) indices values with
  | Sum.inl _ => { indices := [], values := [] }
  | Sum.inr o => o

-- -----------------------------------------------------------------------------
-- 4-leaf round-trip
-- -----------------------------------------------------------------------------

def msg4 : List (ZMod 65521) := [1, 2, 3, 4]
def shape4 : PerfectBinary := PerfectBinary.mk 4
def scheme4 : MerkleCommitment DemoHasher PerfectBinary := ⟨(), shape4⟩

def commitOut4 := scheme4.commit msg4
def openProof4 := scheme4.open msg4 commitOut4.snd [0, 2]
def opening4 : Opening DemoHasher := mkOpening [0, 2] [msg4[0]!, msg4[2]!]

lemma roundtrip4 :
    scheme4.check commitOut4.fst.root opening4 openProof4 = true := by
  native_decide

-- -----------------------------------------------------------------------------
-- 8-leaf round-trip
-- -----------------------------------------------------------------------------

def msg8 : List (ZMod 65521) := [1, 2, 3, 4, 5, 6, 7, 8]
def shape8 : PerfectBinary := PerfectBinary.mk 8
def scheme8 : MerkleCommitment DemoHasher PerfectBinary := ⟨(), shape8⟩

def commitOut8 := scheme8.commit msg8
def openProof8 := scheme8.open msg8 commitOut8.snd [1, 3, 5]
def opening8 : Opening DemoHasher :=
  mkOpening [1, 3, 5] [msg8[1]!, msg8[3]!, msg8[5]!]

lemma roundtrip8 :
    scheme8.check commitOut8.fst.root opening8 openProof8 = true := by
  native_decide

-- -----------------------------------------------------------------------------
-- Negative: tampering with one claimed value flips check to false
-- -----------------------------------------------------------------------------

def tamperedOpening4 : Opening DemoHasher :=
  mkOpening [0, 2] [msg4[0]! + 1, msg4[2]!]

lemma tampered4_rejected :
    scheme4.check commitOut4.fst.root tamperedOpening4 openProof4 = false := by
  native_decide

-- -----------------------------------------------------------------------------
-- L6: deriveVertexSet golden values (book §20 path pruning)
-- -----------------------------------------------------------------------------

/-- For `PerfectBinary 8` and indices `{5, 6}` (heap leaves 12, 13):
    path(5)  = [12, 5, 2, 0],   copath(5)  = [11, 6, 1]
    path(6)  = [13, 6, 2, 0],   copath(6)  = [14, 5, 1]
    deriveVertexSet drops copath entries that lie on any path:
      6 (in path(6)) and 5 (in path(5)) are removed; 11, 1, 14, 1 remain. -/
lemma deriveVertexSet8_5_6 :
    (scheme8.deriveVertexSet [5, 6]).map VertexId.val = [11, 1, 14, 1] := by
  native_decide

/-- For `PerfectBinary 4` and indices `{0, 2}` (heap leaves 3, 5):
    path(0)  = [3, 1, 0],       copath(0)  = [4, 2]
    path(2)  = [5, 2, 0],       copath(2)  = [6, 1]
    Both copath siblings (2 and 1) are interior path vertices for the other
    leaf, so they are dropped. Only the leaf-level siblings 4 and 6 remain. -/
lemma deriveVertexSet4_0_2 :
    (scheme4.deriveVertexSet [0, 2]).map VertexId.val = [4, 6] := by
  native_decide

end VC.Tests.Scheme
