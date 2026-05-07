import Mathlib.Data.ZMod.Basic
import VC.Src.Merkle.Scheme

-- Mirrors ark-mt/src/capped.rs. A scheme-level modifier (DESIGN.md §3.2).
-- A cap commitment at height `c` replaces the single root with the ordered
-- vector of digests at layer `c`. Each opening proof is shortened by `c`
-- copath levels.

structure CappedMerkleCommitment (H : Type) (S : Type)
    [MerkleHasher H] [MerkleShape S] where
  inner : MerkleCommitment H S
  capHeight : Nat

namespace CappedMerkleCommitment

variable {H S : Type} [MerkleHasher H] [MerkleShape S]

open MerkleCommitment

/-- Commit. Build the inner labels, then read off the digests at every vertex
    in `verticesAtLayer capHeight` to form the cap. The trapdoor is the
    inner trapdoor (full label vector + salts + message). At `capHeight = 0`
    the cap is the singleton `[root]`, recovering `MerkleCommitment.commit`. -/
def commit (c : CappedMerkleCommitment H S) (msg : List (MerkleHasher.Symbol H))
    (_seed : ULift UInt64) : List (MerkleHasher.Digest H) × Trapdoor H S :=
  let mc := c.inner
  let n := MerkleShape.numLeaves mc.shape
  let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
  let salts : List (MerkleHasher.Salt H) := List.replicate n defaultS
  let labels := mc.buildLabels msg salts
  let placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher []
  let capVertices := MerkleShape.verticesAtLayer mc.shape c.capHeight
  let cap : List (MerkleHasher.Digest H) :=
    capVertices.map (fun v => listGetD labels v.val placeholder)
  (cap, { message := msg, salts := salts, labels := labels })

/-- Open. For each requested leaf index, return the leaf salt plus the
    bottom-up copath digests TRUNCATED to the first `depth - capHeight`
    levels. The remaining `capHeight` siblings live in the cap and are not
    transmitted. At `capHeight = 0` this matches `MerkleCommitment.open`. -/
def «open» (c : CappedMerkleCommitment H S) (td : Trapdoor H S)
    (op : Opening H) : OpeningProof H :=
  let mc := c.inner
  let depth := MerkleShape.depth mc.shape
  let keep := depth - c.capHeight
  let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
  let placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher []
  let mkEntry (i : Nat) : MerkleHasher.Salt H × List (MerkleHasher.Digest H) :=
    let copath := (MerkleShape.copath mc.shape i).take keep
    let salt := listGetD td.salts i defaultS
    let digests := copath.map (fun v => listGetD td.labels v.val placeholder)
    (salt, digests)
  { entries := op.indices.map mkEntry }

/-- For a perfect-binary heap-indexed tree, the layer-`capHeight` ancestor
    of leaf `i` is reached by `depth - capHeight` parent steps `(v-1)/2`
    starting from heap vertex `numLeaves - 1 + i`. -/
private def capAncestor (mc : MerkleCommitment H S) (capHeight i : Nat) : Nat :=
  let n := MerkleShape.numLeaves mc.shape
  let depth := MerkleShape.depth mc.shape
  let leafPos := n - 1 + i
  Nat.iterate (fun v => (v - 1) / 2) (depth - capHeight) leafPos

/-- Locate `v` in `vs`. Returns the (0-based) position or `vs.length` if
    not found. -/
private def vertexIndex (vs : List VertexId) (v : Nat) : Nat :=
  let rec go (xs : List VertexId) (k : Nat) : Nat :=
    match xs with
    | [] => k
    | x :: rest => if x.val = v then k else go rest (k + 1)
  go vs 0

/-- Check. For each `(i, value, (salt, copath))` triple, walk the truncated
    copath up to layer `capHeight`, locate the resulting cap-ancestor in
    `verticesAtLayer capHeight`, and compare to the supplied cap entry.
    At `capHeight = 0` and a singleton cap `[root]`, this reduces to
    `MerkleCommitment.check`. -/
def check (c : CappedMerkleCommitment H S) (cap : List (MerkleHasher.Digest H))
    (op : Opening H) (pf : OpeningProof H) : Bool :=
  let _ : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  let mc := c.inner
  let capVertices := MerkleShape.verticesAtLayer mc.shape c.capHeight
  let placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher []
  Id.run do
    if op.indices.length ≠ op.values.length then return false
    if op.indices.length ≠ pf.entries.length then return false
    if cap.length ≠ capVertices.length then return false
    let triples := (op.indices.zip op.values).zip pf.entries
    for triple in triples do
      let ((i, value), (salt, copath)) := triple
      let n := MerkleShape.numLeaves mc.shape
      let leafPos := n - 1 + i
      let leafDigest := MerkleHasher.hashLeaf mc.hasher value salt
      let computed := walkCopath mc leafPos leafDigest copath
      let ancestor := capAncestor mc c.capHeight i
      let pos := vertexIndex capVertices ancestor
      let expected := listGetD cap pos placeholder
      if computed ≠ expected then return false
    return true

end CappedMerkleCommitment

namespace VC.Tests.Capped

open CappedMerkleCommitment

-- Round-trip tests using a local demo hasher over `ZMod 65521`. Mirrors
-- the demo hasher used by `VC/Tests/SchemeTests.lean`.

private def CapDemoHasher : Type := Unit

private instance : Inhabited CapDemoHasher := ⟨()⟩

private instance : MerkleHasher CapDemoHasher where
  Symbol := ZMod 65521
  Digest := ZMod 65521
  Salt := Unit
  decEqDigest := inferInstance
  defaultSalt := ⟨()⟩
  sampleSalt _ _ := ()
  hashLeaf _ x _ := x * 31 + 17
  hashNodes _ cs := cs.foldl (fun acc d => acc * 31 + d) 1

private def msg4 : List (ZMod 65521) := [1, 2, 3, 4]
private def shape4 : PerfectBinary := PerfectBinary.mk 4
private def inner4 : MerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨(), shape4⟩

-- capHeight = 1 → cap has 2 entries, copath shortens by 1 level.
private def capped4_h1 : CappedMerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨inner4, 1⟩

private def commitOut4_h1 := capped4_h1.commit msg4 (ULift.up.{0} 0)
private def cap4_h1 := commitOut4_h1.fst
private def td4_h1 := commitOut4_h1.snd

private def opening4 : Opening CapDemoHasher :=
  { indices := [0, 2], values := [msg4[0]!, msg4[2]!] }
private def proof4_h1 := capped4_h1.open td4_h1 opening4

lemma roundtrip4_h1 :
    capped4_h1.check cap4_h1 opening4 proof4_h1 = true := by
  native_decide

-- capHeight = 0 → equivalent to uncapped (cap = [root]).
private def capped4_h0 : CappedMerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨inner4, 0⟩

private def commitOut4_h0 := capped4_h0.commit msg4 (ULift.up.{0} 0)
private def proof4_h0 := capped4_h0.open commitOut4_h0.snd opening4

lemma roundtrip4_h0 :
    capped4_h0.check commitOut4_h0.fst opening4 proof4_h0 = true := by
  native_decide

-- capHeight = depth = 2 → cap is the full leaf-digest layer; copath empty.
private def capped4_h2 : CappedMerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨inner4, 2⟩

private def commitOut4_h2 := capped4_h2.commit msg4 (ULift.up.{0} 0)
private def proof4_h2 := capped4_h2.open commitOut4_h2.snd opening4

lemma roundtrip4_h2 :
    capped4_h2.check commitOut4_h2.fst opening4 proof4_h2 = true := by
  native_decide

-- 8-leaf tree, capHeight = 2.
private def msg8 : List (ZMod 65521) := [1, 2, 3, 4, 5, 6, 7, 8]
private def shape8 : PerfectBinary := PerfectBinary.mk 8
private def inner8 : MerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨(), shape8⟩
private def capped8_h2 : CappedMerkleCommitment CapDemoHasher PerfectBinary :=
  ⟨inner8, 2⟩

private def commitOut8_h2 := capped8_h2.commit msg8 (ULift.up.{0} 0)
private def opening8 : Opening CapDemoHasher :=
  { indices := [1, 3, 5], values := [msg8[1]!, msg8[3]!, msg8[5]!] }
private def proof8_h2 := capped8_h2.open commitOut8_h2.snd opening8

lemma roundtrip8_h2 :
    capped8_h2.check commitOut8_h2.fst opening8 proof8_h2 = true := by
  native_decide

end VC.Tests.Capped
