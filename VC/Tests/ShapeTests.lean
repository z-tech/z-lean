import VC.Src.Merkle.Shape

-- L1 golden-value tests for `PerfectBinary` shape methods (book §12 layout).

namespace VC.Tests.Shape

def s4 : PerfectBinary := PerfectBinary.mk 4
def s8 : PerfectBinary := PerfectBinary.mk 8

-- -----------------------------------------------------------------------------
-- 4-leaf perfect binary: 7 vertices, depth 2.
--   layer 0: [0]
--   layer 1: [1, 2]
--   layer 2 (leaves): [3, 4, 5, 6]   ← message indices 0, 1, 2, 3
-- -----------------------------------------------------------------------------

theorem s4_numLeaves   : MerkleShape.numLeaves   s4 = 4         := by native_decide
theorem s4_depth       : MerkleShape.depth       s4 = 2         := by native_decide
theorem s4_numVertices : MerkleShape.numVertices s4 = 7         := by native_decide
theorem s4_leaf0       : MerkleShape.leaf s4 0 = VertexId.mk 3  := by native_decide
theorem s4_leaf3       : MerkleShape.leaf s4 3 = VertexId.mk 6  := by native_decide

-- Path of leaf 2 = vertex 5: [5, 2, 0]
theorem s4_path2 :
    MerkleShape.path s4 2 = [VertexId.mk 5, VertexId.mk 2, VertexId.mk 0] := by
  native_decide

-- Copath of leaf 2 = vertex 5: sibling of 5 is 6, sibling of 2 is 1.
theorem s4_copath2 :
    MerkleShape.copath s4 2 = [VertexId.mk 6, VertexId.mk 1] := by native_decide

-- Internal vertices bottom-up: [2, 1, 0]
theorem s4_internalBU :
    MerkleShape.internalVerticesBottomUp s4 =
      [VertexId.mk 2, VertexId.mk 1, VertexId.mk 0] := by
  native_decide

-- -----------------------------------------------------------------------------
-- 8-leaf perfect binary: 15 vertices, depth 3.
-- -----------------------------------------------------------------------------

theorem s8_numLeaves   : MerkleShape.numLeaves   s8 = 8  := by native_decide
theorem s8_depth       : MerkleShape.depth       s8 = 3  := by native_decide
theorem s8_numVertices : MerkleShape.numVertices s8 = 15 := by native_decide

-- Path of leaf 5 = vertex 12: [12, 5, 2, 0]
theorem s8_path5 :
    MerkleShape.path s8 5 =
      [VertexId.mk 12, VertexId.mk 5, VertexId.mk 2, VertexId.mk 0] := by
  native_decide

-- Copath of leaf 5: sibling of 12 is 11, sibling of 5 is 6, sibling of 2 is 1.
theorem s8_copath5 :
    MerkleShape.copath s8 5 =
      [VertexId.mk 11, VertexId.mk 6, VertexId.mk 1] := by
  native_decide

-- -----------------------------------------------------------------------------
-- L9: PerfectKAry 4 with 16 leaves. Heap-indexed:
--   firstLeafId = (16-1)/(4-1) = 5; numVertices = (16·4 - 1)/(4-1) = 21
--   layer 0: [0]
--   layer 1: [1, 2, 3, 4]
--   layer 2 (leaves): [5..20]   ← message indices 0..15
-- -----------------------------------------------------------------------------

def k4 : PerfectKAry 4 := PerfectKAry.mk 16

theorem k4_numLeaves   : MerkleShape.numLeaves   k4 = 16 := by native_decide
theorem k4_depth       : MerkleShape.depth       k4 = 2  := by native_decide
theorem k4_numVertices : MerkleShape.numVertices k4 = 21 := by native_decide

theorem k4_root : MerkleShape.root k4 = VertexId.mk 0 := by native_decide
theorem k4_leaf0 : MerkleShape.leaf k4 0 = VertexId.mk 5 := by native_decide
theorem k4_leaf5 : MerkleShape.leaf k4 5 = VertexId.mk 10 := by native_decide

-- Path of leaf 5 = vertex 10: parent (10-1)/4 = 2, then 0. So [10, 2, 0].
theorem k4_path5 :
    MerkleShape.path k4 5 = [VertexId.mk 10, VertexId.mk 2, VertexId.mk 0] := by
  native_decide

-- Copath of leaf 5: parent of 10 is 2, children of 2 are [9,10,11,12]; sibs = [9,11,12].
-- Parent of 2 is 0, children of 0 are [1,2,3,4]; sibs = [1,3,4].
theorem k4_copath5 :
    MerkleShape.copath k4 5 =
      [VertexId.mk 9, VertexId.mk 11, VertexId.mk 12,
       VertexId.mk 1, VertexId.mk 3, VertexId.mk 4] := by
  native_decide

-- Children of root: [1, 2, 3, 4]
theorem k4_children0 :
    MerkleShape.children k4 (VertexId.mk 0) =
      [VertexId.mk 1, VertexId.mk 2, VertexId.mk 3, VertexId.mk 4] := by
  native_decide

-- Internal vertices bottom-up: [4, 3, 2, 1, 0]
theorem k4_internalBU :
    MerkleShape.internalVerticesBottomUp k4 =
      [VertexId.mk 4, VertexId.mk 3, VertexId.mk 2, VertexId.mk 1, VertexId.mk 0] := by
  native_decide

-- Vertices at layer 1: [1, 2, 3, 4]
theorem k4_layer1 :
    MerkleShape.verticesAtLayer k4 1 =
      [VertexId.mk 1, VertexId.mk 2, VertexId.mk 3, VertexId.mk 4] := by
  native_decide

-- -----------------------------------------------------------------------------
-- L9: ArbitraryLength with 7 leaves. Recursive ceil/floor split:
--   root(7) → left(4), right(3); left(4) → (2,2); right(3) → (2,1).
--   Pre-order DFS ids:
--     0: root
--       1: left (count 4)
--         2: ll (count 2)
--           3: leaf 0
--           4: leaf 1
--         5: lr (count 2)
--           6: leaf 2
--           7: leaf 3
--       8: right (count 3)
--         9: rl (count 2)
--           10: leaf 4
--           11: leaf 5
--         12: leaf 6
--   numVertices = 13, depth = 3 (leaf 0 path is 3→2→1→0).
-- -----------------------------------------------------------------------------

def a7 : ArbitraryLength := ArbitraryLength.mk 7

theorem a7_numLeaves   : MerkleShape.numLeaves   a7 = 7  := by native_decide
theorem a7_numVertices : MerkleShape.numVertices a7 = 13 := by native_decide
theorem a7_depth       : MerkleShape.depth       a7 = 3  := by native_decide

theorem a7_root : MerkleShape.root a7 = VertexId.mk 0 := by native_decide

-- leafToVid = [3, 4, 6, 7, 10, 11, 12]
theorem a7_leaf0 : MerkleShape.leaf a7 0 = VertexId.mk 3  := by native_decide
theorem a7_leaf6 : MerkleShape.leaf a7 6 = VertexId.mk 12 := by native_decide

-- Path of leaf 0 (vertex 3) up to root: [3, 2, 1, 0]
theorem a7_path0 :
    MerkleShape.path a7 0 =
      [VertexId.mk 3, VertexId.mk 2, VertexId.mk 1, VertexId.mk 0] := by
  native_decide

-- Path of leaf 6 (vertex 12): [12, 8, 0]
theorem a7_path6 :
    MerkleShape.path a7 6 =
      [VertexId.mk 12, VertexId.mk 8, VertexId.mk 0] := by
  native_decide

-- Copath of leaf 0: at v=3, parent=2, sib=4. At v=2, parent=1, sib=5.
-- At v=1, parent=0, sib=8. So [4, 5, 8].
theorem a7_copath0 :
    MerkleShape.copath a7 0 =
      [VertexId.mk 4, VertexId.mk 5, VertexId.mk 8] := by
  native_decide

-- Internal vertices bottom-up (post-order DFS): [2, 5, 1, 9, 8, 0]
theorem a7_internalBU :
    MerkleShape.internalVerticesBottomUp a7 =
      [VertexId.mk 2, VertexId.mk 5, VertexId.mk 1,
       VertexId.mk 9, VertexId.mk 8, VertexId.mk 0] := by
  native_decide

-- For binary trees: |internals| = |leaves| - 1.
theorem a7_internal_count :
    (MerkleShape.internalVerticesBottomUp a7).length = 6 := by native_decide

-- isLeaf checks: vertex 3 is a leaf, vertex 0 is not.
theorem a7_leaf_check_3 : MerkleShape.isLeaf a7 (VertexId.mk 3) = true := by
  native_decide
theorem a7_leaf_check_0 : MerkleShape.isLeaf a7 (VertexId.mk 0) = false := by
  native_decide

end VC.Tests.Shape
