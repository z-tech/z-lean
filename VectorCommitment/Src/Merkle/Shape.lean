-- Mirrors ark-mt/src/shape.rs. See VectorCommitment/DESIGN.md §3.2.

structure VertexId where
  val : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

class MerkleShape (S : Type) where
  numLeaves : S → Nat
  depth : S → Nat
  numVertices : S → Nat
  root : S → VertexId
  leaf : S → Nat → VertexId
  children : S → VertexId → List VertexId
  isLeaf : S → VertexId → Bool
  path : S → Nat → List VertexId
  copath : S → Nat → List VertexId
  internalVerticesBottomUp : S → List VertexId
  verticesAtLayer : S → Nat → List VertexId

-- Concrete shape stubs. PerfectBinary has a real body at L1; the other two stay
-- placeholders until L9.

structure PerfectBinary where
  numLeaves : Nat
  deriving Repr, Inhabited

namespace PerfectBinary

/-- Compute `log₂ n` rounded down. Assumes `n ≥ 1`; returns `0` on `n = 0`. -/
def log2Floor (n : Nat) : Nat :=
  if h : n ≤ 1 then 0
  else 1 + log2Floor (n / 2)
decreasing_by
  simp_wf
  omega

/-- Depth of the perfect-binary tree (= ⌈log₂ numLeaves⌉ = log₂ for powers of 2). -/
def depth (s : PerfectBinary) : Nat := log2Floor s.numLeaves

/-- Total vertices = 2·numLeaves - 1 (perfect binary tree). -/
def numVertices (s : PerfectBinary) : Nat :=
  if s.numLeaves = 0 then 0 else 2 * s.numLeaves - 1

/-- Heap-indexed BFS: leaf for message index `i ∈ [0, n)` is vertex `n - 1 + i`. -/
def leafVertex (s : PerfectBinary) (i : Nat) : VertexId :=
  VertexId.mk (s.numLeaves - 1 + i)

/-- Children of vertex `v`: `[2v+1, 2v+2]` if internal, `[]` if leaf. -/
def childrenOf (s : PerfectBinary) (v : VertexId) : List VertexId :=
  let n := s.numLeaves
  if v.val + 1 ≥ n then []  -- leaf vertices live at indices [n-1, 2n-2]
  else [VertexId.mk (2 * v.val + 1), VertexId.mk (2 * v.val + 2)]

/-- `true` iff `v` is a leaf vertex (one of the bottom layer). -/
def isLeafOf (s : PerfectBinary) (v : VertexId) : Bool :=
  decide (s.numLeaves ≤ v.val + 1) && decide (v.val + 1 ≤ 2 * s.numLeaves - 1 + 1)

/-- Path from leaf `i` up to root (inclusive of both endpoints). Bottom-up. -/
def pathOf (s : PerfectBinary) (i : Nat) : List VertexId :=
  let rec go (v : Nat) (fuel : Nat) : List VertexId :=
    match fuel with
    | 0 => [VertexId.mk v]
    | Nat.succ k =>
      if v = 0 then [VertexId.mk 0]
      else VertexId.mk v :: go ((v - 1) / 2) k
  go (s.numLeaves - 1 + i) (s.depth + 1)

/-- Sibling of vertex `v > 0`. Odd → `v+1`, even → `v-1`. Returns `0` for root. -/
def siblingOf (v : Nat) : Nat :=
  if v = 0 then 0
  else if v % 2 = 1 then v + 1 else v - 1

/-- Copath: siblings of each path vertex except root. Bottom-up, length = depth. -/
def copathOf (s : PerfectBinary) (i : Nat) : List VertexId :=
  let rec go (v : Nat) (fuel : Nat) : List VertexId :=
    match fuel with
    | 0 => []
    | Nat.succ k =>
      if v = 0 then []
      else VertexId.mk (siblingOf v) :: go ((v - 1) / 2) k
  go (s.numLeaves - 1 + i) s.depth

/-- All internal vertices, bottom layer first (deepest internal first). -/
def internalVerticesBottomUpOf (s : PerfectBinary) : List VertexId :=
  -- Internal vertices are [0, n-1); reverse to get bottom-up.
  (List.range (s.numLeaves - 1)).reverse.map VertexId.mk

/-- Vertices at layer `ℓ`: layer 0 is root, layer `depth` is leaves. -/
def verticesAtLayerOf (_s : PerfectBinary) (ℓ : Nat) : List VertexId :=
  -- Layer ℓ contains 2^ℓ vertices starting at index 2^ℓ - 1.
  let start := 2 ^ ℓ - 1
  let count := 2 ^ ℓ
  (List.range count).map (fun k => VertexId.mk (start + k))

end PerfectBinary

instance : MerkleShape PerfectBinary where
  numLeaves s := s.numLeaves
  depth s := s.depth
  numVertices s := s.numVertices
  root _ := VertexId.mk 0
  leaf s i := s.leafVertex i
  children s v := s.childrenOf v
  isLeaf s v := s.isLeafOf v
  path s i := s.pathOf i
  copath s i := s.copathOf i
  internalVerticesBottomUp s := s.internalVerticesBottomUpOf
  verticesAtLayer s ℓ := PerfectBinary.verticesAtLayerOf s ℓ

structure PerfectKAry (k : Nat) where
  numLeaves : Nat
  deriving Repr, Inhabited

namespace PerfectKAry

variable {k : Nat}

/-- Depth helper: count divisions by `k` until `m ≤ 1`. Guards on `k ≤ 1` so
    termination is unconditional regardless of the `Fact (1 < k)` instance. -/
def depthAux (k : Nat) (m : Nat) (acc : Nat) : Nat :=
  if hm : m ≤ 1 then acc
  else
    if hk : k ≤ 1 then acc
    else depthAux k (m / k) (acc + 1)
termination_by m
decreasing_by
  have : 1 < m := by omega
  have : 1 < k := by omega
  exact Nat.div_lt_self (by omega) (by omega)

/-- Depth: smallest `d` with `k^d ≥ numLeaves`. -/
def depthOf (s : PerfectKAry k) : Nat := depthAux k s.numLeaves 0

/-- Total vertices: geometric series `(numLeaves * k - 1) / (k - 1)`.
    Returns `0` when `k ≤ 1` (degenerate guard). -/
def numVerticesOf (s : PerfectKAry k) : Nat :=
  if k ≤ 1 then 0
  else (s.numLeaves * k - 1) / (k - 1)

/-- Index of the first leaf in heap order: `(numLeaves - 1) / (k - 1)`. -/
def firstLeafId (s : PerfectKAry k) : Nat :=
  if k ≤ 1 then 0 else (s.numLeaves - 1) / (k - 1)

/-- Heap layout: leaf for message index `i` is vertex `firstLeafId + i`. -/
def leafVertex (s : PerfectKAry k) (i : Nat) : VertexId :=
  VertexId.mk (s.firstLeafId + i)

/-- Children of vertex `v`: `[k*v+1, k*v+2, ..., k*v+k]` if internal, else `[]`. -/
def childrenOf (s : PerfectKAry k) (v : VertexId) : List VertexId :=
  let first := k * v.val + 1
  let total := s.numVerticesOf
  if first ≥ total then []
  else (List.range k).map (fun j => VertexId.mk (first + j))

/-- `true` iff `v` is a leaf vertex. -/
def isLeafOf (s : PerfectKAry k) (v : VertexId) : Bool :=
  decide (s.firstLeafId ≤ v.val)

/-- Path from leaf `i` up to root (inclusive of both endpoints). Bottom-up. -/
def pathOf (s : PerfectKAry k) (i : Nat) : List VertexId :=
  let rec go (v : Nat) (fuel : Nat) : List VertexId :=
    match fuel with
    | 0 => [VertexId.mk v]
    | Nat.succ f =>
      if v = 0 then [VertexId.mk 0]
      else
        if k ≤ 1 then [VertexId.mk v]  -- guard
        else VertexId.mk v :: go ((v - 1) / k) f
  go (s.firstLeafId + i) (s.depthOf + 1)

/-- Copath of leaf `i`: at each non-root level, the `k - 1` siblings of the
    path vertex (children of its parent that aren't on the path). Bottom-up. -/
def copathOf (s : PerfectKAry k) (i : Nat) : List VertexId :=
  let rec go (v : Nat) (fuel : Nat) : List VertexId :=
    match fuel with
    | 0 => []
    | Nat.succ f =>
      if v = 0 then []
      else
        if k ≤ 1 then []  -- guard
        else
          let parent := (v - 1) / k
          let firstChild := k * parent + 1
          let sibs : List VertexId :=
            (List.range k).filterMap fun j =>
              let s := firstChild + j
              if s = v then none else some (VertexId.mk s)
          sibs ++ go parent f
  go (s.firstLeafId + i) s.depthOf

/-- Internal vertices in reverse heap-index order (deepest internal first). -/
def internalVerticesBottomUpOf (s : PerfectKAry k) : List VertexId :=
  (List.range s.firstLeafId).reverse.map VertexId.mk

/-- Vertices at depth `ℓ`: heap range `[(k^ℓ - 1)/(k-1), (k^(ℓ+1) - 1)/(k-1))`. -/
def verticesAtLayerOf (s : PerfectKAry k) (ℓ : Nat) : List VertexId :=
  if k ≤ 1 then []
  else
    let kPow := k ^ ℓ
    let kPowNext := k ^ (ℓ + 1)
    let start := (kPow - 1) / (k - 1)
    let endExclusive := min ((kPowNext - 1) / (k - 1)) s.numVerticesOf
    if start ≥ endExclusive then []
    else (List.range (endExclusive - start)).map (fun j => VertexId.mk (start + j))

end PerfectKAry

instance {k : Nat} : MerkleShape (PerfectKAry k) where
  numLeaves s := s.numLeaves
  depth s := s.depthOf
  numVertices s := s.numVerticesOf
  root _ := VertexId.mk 0
  leaf s i := s.leafVertex i
  children s v := s.childrenOf v
  isLeaf s v := s.isLeafOf v
  path s i := s.pathOf i
  copath s i := s.copathOf i
  internalVerticesBottomUp s := s.internalVerticesBottomUpOf
  verticesAtLayer s ℓ := s.verticesAtLayerOf ℓ

/-- Binary tree on any `numLeaves ≥ 1`, built by recursive ceil/floor splitting
    (book §20 Definition 20.x.1). Pre-computes parent/children vectors at
    construction so trait methods are cheap lookups.

    Termination workaround: the recursive build splits `count` leaves into
    `(count+1)/2` and `count/2`, and each recursive call has a strictly
    smaller `count`. We use `count` itself as the well-founded measure. -/
structure ArbitraryLength where
  /-- Internal constructor; prefer `ArbitraryLength.mk` (smart constructor). -/
  ofRaw ::
  /-- Number of leaves. -/
  numLeavesField : Nat
  /-- Total vertex count. -/
  numVerticesField : Nat
  /-- Tree depth. -/
  depthField : Nat
  /-- `parentOf[v] = some p` if `v` has parent `p`; `none` for root.
      Length = `numVerticesField`. -/
  parentOf : Array (Option Nat)
  /-- `childrenOf[v]` = list of children of `v` (empty for leaves).
      Length = `numVerticesField`. -/
  childrenOfField : Array (List Nat)
  /-- `leafToVid[i]` = vertex id of the `i`-th leaf. Length = `numLeavesField`. -/
  leafToVid : Array Nat
  /-- Internal vertices in bottom-up topological order. -/
  bottomUpInternal : List Nat
  deriving Repr, Inhabited

namespace ArbitraryLength

/-- One step of the recursive build. Returns:
    - `myId`: id of the constructed subtree's root
    - updated `(parentOf, childrenOf, leafToVid)` arrays -/
def buildStep (parent : Option Nat) (firstLeaf count : Nat)
    (parentOf : Array (Option Nat)) (childrenOf : Array (List Nat))
    (leafToVid : Array Nat) :
    Nat × Array (Option Nat) × Array (List Nat) × Array Nat :=
  let myId := parentOf.size
  let parentOf := parentOf.push parent
  let childrenOf := childrenOf.push []
  if count ≤ 1 then
    -- Leaf: record vid for `firstLeaf`. (count = 0 reaches here only for the
    -- degenerate empty tree; we only call build with count ≥ 1.)
    let leafToVid := leafToVid.set! firstLeaf myId
    (myId, parentOf, childrenOf, leafToVid)
  else
    let leftCount := (count + 1) / 2
    let rightCount := count - leftCount
    -- Recurse left.
    let (leftId, parentOf, childrenOf, leafToVid) :=
      buildStep (some myId) firstLeaf leftCount parentOf childrenOf leafToVid
    -- Recurse right.
    let (rightId, parentOf, childrenOf, leafToVid) :=
      buildStep (some myId) (firstLeaf + leftCount) rightCount
        parentOf childrenOf leafToVid
    let childrenOf := childrenOf.set! myId [leftId, rightId]
    (myId, parentOf, childrenOf, leafToVid)
termination_by count
decreasing_by
  -- leftCount = (count + 1) / 2 < count when count ≥ 2
  · simp_wf; omega
  -- rightCount = count - leftCount < count when leftCount ≥ 1, i.e. count ≥ 2
  · simp_wf
    have : (count + 1) / 2 ≥ 1 := by omega
    omega

/-- Post-order DFS to collect internal vertices bottom-up. Uses fuel = total
    vertex count as termination measure (each call descends to a child, and
    the tree has at most `fuel` vertices). -/
def postOrderInternal (childrenOf : Array (List Nat)) (v : Nat) (fuel : Nat)
    (out : List Nat) : List Nat :=
  match fuel with
  | 0 => out
  | Nat.succ f =>
    let kids := childrenOf.getD v []
    let out :=
      kids.foldl (fun acc c => postOrderInternal childrenOf c f acc) out
    if kids.isEmpty then out else out ++ [v]

/-- Compute depth: longest root-to-leaf path. Uses fuel = vertex count. -/
def depthFromLeaf (parentOf : Array (Option Nat)) (v : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | Nat.succ f =>
    match parentOf.getD v none with
    | none => 0
    | some p => 1 + depthFromLeaf parentOf p f

/-- Smart constructor: build a tree with `n` leaves (`n ≥ 1`). Pre-computes
    parent / children / leafToVid / bottom-up-internal vectors. -/
def mk (n : Nat) : ArbitraryLength :=
  let n := max 1 n  -- guard against degenerate `n = 0`
  let leafToVid : Array Nat := Array.replicate n 0
  let (_, parentOf, childrenOf, leafToVid) :=
    buildStep none 0 n #[] #[] leafToVid
  let numVertices := parentOf.size
  let bottomUpInternal := postOrderInternal childrenOf 0 numVertices []
  -- Depth = max over leaves of (distance to root).
  let depth :=
    leafToVid.foldl
      (fun acc lid => max acc (depthFromLeaf parentOf lid numVertices)) 0
  ArbitraryLength.ofRaw n numVertices depth parentOf childrenOf
    leafToVid bottomUpInternal

/-- Path from leaf `i` up to root using fuel = numVertices. -/
def pathFrom (s : ArbitraryLength) (v : Nat) (fuel : Nat) : List VertexId :=
  match fuel with
  | 0 => [VertexId.mk v]
  | Nat.succ f =>
    match s.parentOf.getD v none with
    | none => [VertexId.mk v]
    | some p => VertexId.mk v :: pathFrom s p f

/-- Copath from leaf vertex `v` upward, collecting non-`v` siblings at each level. -/
def copathFrom (s : ArbitraryLength) (v : Nat) (fuel : Nat) : List VertexId :=
  match fuel with
  | 0 => []
  | Nat.succ f =>
    match s.parentOf.getD v none with
    | none => []
    | some p =>
      let sibs : List VertexId :=
        (s.childrenOfField.getD p []).filterMap fun c =>
          if c = v then none else some (VertexId.mk c)
      sibs ++ copathFrom s p f

end ArbitraryLength

instance : MerkleShape ArbitraryLength where
  numLeaves s := s.numLeavesField
  depth s := s.depthField
  numVertices s := s.numVerticesField
  root _ := VertexId.mk 0
  leaf s i := VertexId.mk (s.leafToVid.getD i 0)
  children s v := (s.childrenOfField.getD v.val []).map VertexId.mk
  isLeaf s v := (s.childrenOfField.getD v.val []).isEmpty
  path s i := s.pathFrom (s.leafToVid.getD i 0) s.numVerticesField
  copath s i := s.copathFrom (s.leafToVid.getD i 0) s.numVerticesField
  internalVerticesBottomUp s := s.bottomUpInternal.map VertexId.mk
  verticesAtLayer s ℓ :=
    -- Default BFS using children. Fuel = depth + 1 covers every reachable layer.
    let rec go (frontier : List VertexId) (steps : Nat) : List VertexId :=
      match steps with
      | 0 => frontier
      | Nat.succ k =>
        let next := frontier.flatMap fun v =>
          (s.childrenOfField.getD v.val []).map VertexId.mk
        if next.isEmpty then [] else go next k
    go [VertexId.mk 0] ℓ
