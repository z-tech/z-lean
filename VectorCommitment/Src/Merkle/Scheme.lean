import VectorCommitment.Src.Error
import VectorCommitment.Src.Merkle.Hasher
import VectorCommitment.Src.Merkle.Shape

-- The concrete Merkle commitment scheme. Mirrors ark-mt/src/scheme.rs.

structure MerkleCommitment (H : Type) (S : Type) [MerkleHasher H] [MerkleShape S] where
  hasher : H
  shape : S

/-- Trapdoor: stores the message, per-leaf salts, and the full label vector
    indexed by `VertexId.val`. The book's §12 Remark "recomputing the tree"
    permits this layout — we keep the message so `open` can recompute on
    demand. -/
structure Trapdoor (H : Type) (S : Type) [MerkleHasher H] [MerkleShape S] where
  message : List (MerkleHasher.Symbol H)
  salts   : List (MerkleHasher.Salt H)
  labels  : List (MerkleHasher.Digest H)

/-- Committed: the root digest. (Future milestones may add cap data here.) -/
structure Committed (H : Type) (S : Type) [MerkleHasher H] [MerkleShape S] where
  root : MerkleHasher.Digest H

structure Opening (H : Type) [MerkleHasher H] where
  indices : List Nat := []
  values  : List (MerkleHasher.Symbol H) := []

/-- Opening proof: parallel to the opened indices, each entry carries the
    leaf salt plus the bottom-up copath digests. No path-pruning at L1. -/
structure OpeningProof (H : Type) [MerkleHasher H] where
  -- One (salt, copathDigests) entry per opened index; copathDigests is
  -- bottom-up (length = tree depth).
  entries : List (MerkleHasher.Salt H × List (MerkleHasher.Digest H))

namespace MerkleCommitment

variable {H S : Type} [MerkleHasher H] [MerkleShape S]

/-- Read a value out of a `List`, defaulting to `dflt` on out-of-range. -/
def listGetD {α : Type} (xs : List α) (i : Nat) (dflt : α) : α :=
  (xs[i]?).getD dflt

/-- Functional label at vertex `v` for a perfect-binary heap-indexed tree.
    Internal vertices are those with `v + 1 < numLeaves`; their label is
    `hashNodes [labelAt (2v+1), labelAt (2v+2)]`. Leaf vertices use the
    corresponding `msg` entry and `salts` entry.

    Termination: the measure `2n - 1 - v` strictly decreases on the children
    `2v+1`, `2v+2`. -/
def labelAt (mc : MerkleCommitment H S)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H)) (v : Nat) : MerkleHasher.Digest H :=
  let n := MerkleShape.numLeaves mc.shape
  if v + 1 ≥ n then
    -- leaf
    let i := v - (n - 1)
    let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
    match msg[i]? with
    | none     => MerkleHasher.hashNodes mc.hasher []
    | some sym => MerkleHasher.hashLeaf mc.hasher sym (listGetD salts i defaultS)
  else
    let l := labelAt mc msg salts (2 * v + 1)
    let r := labelAt mc msg salts (2 * v + 2)
    MerkleHasher.hashNodes mc.hasher [l, r]
termination_by 2 * (MerkleShape.numLeaves mc.shape) - 1 - v
decreasing_by
  all_goals
    simp_wf
    omega

/-- Compute the full label vector of length `2 * numLeaves - 1`, indexed by
    heap-BFS `VertexId.val`. Pure functional version: `labels[v] = labelAt v`. -/
def buildLabels (mc : MerkleCommitment H S)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H)) :
    List (MerkleHasher.Digest H) :=
  let n := MerkleShape.numLeaves mc.shape
  let total := if n = 0 then 0 else 2 * n - 1
  (List.range total).map (labelAt mc msg salts)

/-- Commit. Returns a `Committed` (just the root) and a `Trapdoor` (message,
    salts, full label vector). Salts default to `defaultSalt` (non-hiding). -/
def commit (mc : MerkleCommitment H S) (msg : List (MerkleHasher.Symbol H)) :
    Committed H S × Trapdoor H S :=
  let n := MerkleShape.numLeaves mc.shape
  let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
  let salts : List (MerkleHasher.Salt H) := List.replicate n defaultS
  let labels := mc.buildLabels msg salts
  let placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher []
  let rootDigest : MerkleHasher.Digest H :=
    if n = 0 then placeholder else listGetD labels 0 placeholder
  ({ root := rootDigest }, { message := msg, salts := salts, labels := labels })

/-- Open. For each requested index, return the leaf salt plus the bottom-up
    copath digests read off the trapdoor's label vector. -/
def «open» (mc : MerkleCommitment H S) (_msg : List (MerkleHasher.Symbol H))
    (td : Trapdoor H S) (indices : List Nat) : OpeningProof H :=
  let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
  let placeholder : MerkleHasher.Digest H :=
    MerkleHasher.hashNodes mc.hasher []
  let mkEntry (i : Nat) : MerkleHasher.Salt H × List (MerkleHasher.Digest H) :=
    let copath := MerkleShape.copath mc.shape i
    let salt := listGetD td.salts i defaultS
    let digests := copath.map (fun v => listGetD td.labels v.val placeholder)
    (salt, digests)
  { entries := indices.map mkEntry }

/-- Walk one level up the tree: combine `acc` with `sib` based on the parity
    of `pos` (odd → `acc` is the left child, even → `acc` is the right child)
    and return the parent digest. -/
def combineUp (mc : MerkleCommitment H S) (pos : Nat)
    (acc sib : MerkleHasher.Digest H) : MerkleHasher.Digest H :=
  let (left, right) := if pos % 2 = 1 then (acc, sib) else (sib, acc)
  MerkleHasher.hashNodes mc.hasher [left, right]

/-- Walk the bottom-up copath, accumulating the digest. Structurally
    recursive on the copath list so it terminates. -/
def walkCopath (mc : MerkleCommitment H S) :
    Nat → MerkleHasher.Digest H → List (MerkleHasher.Digest H) →
      MerkleHasher.Digest H
  | _,   acc, []          => acc
  | pos, acc, sib :: rest => walkCopath mc ((pos - 1) / 2)
                              (combineUp mc pos acc sib) rest

/-- Reconstruct the root digest from a single (index, value, salt, copath).
    Total: terminates on the structure of `copathDigests`. -/
def reconstructRoot (mc : MerkleCommitment H S) (i : Nat)
    (value : MerkleHasher.Symbol H) (salt : MerkleHasher.Salt H)
    (copathDigests : List (MerkleHasher.Digest H)) :
    MerkleHasher.Digest H :=
  let n := MerkleShape.numLeaves mc.shape
  let leafPos := n - 1 + i
  let leafDigest := MerkleHasher.hashLeaf mc.hasher value salt
  walkCopath mc leafPos leafDigest copathDigests

/-- Check. Verify that, for every (index, value, opening-entry) triple, the
    reconstructed root matches the supplied root. -/
def check (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (op : Opening H) (pf : OpeningProof H) : Bool :=
  let _ : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  Id.run do
    if op.indices.length ≠ op.values.length then return false
    if op.indices.length ≠ pf.entries.length then return false
    let triples := (op.indices.zip op.values).zip pf.entries
    for triple in triples do
      let ((i, value), (salt, copath)) := triple
      let r := mc.reconstructRoot i value salt copath
      if r ≠ root then return false
    return true

/-- Path pruning per book §20: the minimal set of vertex labels needed to
    authenticate every index in `indices`. Functional spec
    (Lemma `path-pruning-is-copaths-minus-paths`):
    `deriveVertexSet I = copath(I) \ path(I)` where copath/path are unions
    over the leaves in `I`. -/
def deriveVertexSet (mc : MerkleCommitment H S) (indices : List Nat) :
    List VertexId :=
  let copathSet := indices.flatMap (fun i => MerkleShape.copath mc.shape i)
  let pathSet := indices.flatMap (fun i => MerkleShape.path mc.shape i)
  copathSet.filter (fun v => decide (v ∉ pathSet))

end MerkleCommitment

namespace Opening

variable {H : Type} [MerkleHasher H]

/-- Strict-ascending sortedness check on the index list. -/
private def sortedCheck : List Nat → Nat → Sum OpeningError Unit
  | [], _ => Sum.inr ()
  | [_], _ => Sum.inr ()
  | a :: b :: rest, k =>
    if a = b then Sum.inl (OpeningError.DuplicateIndex a)
    else if a > b then Sum.inl (OpeningError.NotSorted k)
    else sortedCheck (b :: rest) (k + 1)

/-- Validating constructor. Indices must be sorted strictly ascending and the
    two lists must agree in length. -/
def new (indices : List Nat) (values : List (MerkleHasher.Symbol H)) :
    Sum OpeningError (Opening H) :=
  if indices.length ≠ values.length then
    Sum.inl (OpeningError.LengthMismatch indices.length values.length)
  else
    match sortedCheck indices 0 with
    | Sum.inl e => Sum.inl e
    | Sum.inr _ => Sum.inr { indices := indices, values := values }

/-- Build an opening from a list of `(index, value)` pairs. -/
def fromPairs (pairs : List (Nat × (MerkleHasher.Symbol H))) :
    Sum OpeningError (Opening H) :=
  Opening.new (pairs.map Prod.fst) (pairs.map Prod.snd)

/-- Project the values at the given indices out of `msg`, then validate. -/
def fromMessageIndices (msg : List (MerkleHasher.Symbol H)) (indices : List Nat) :
    Sum OpeningError (Opening H) :=
  -- Use indexOf on the indices to fetch from msg with `getD`. We require
  -- the caller to pass a non-empty `msg`; otherwise we default to no values.
  match msg with
  | [] => Opening.new indices []
  | h :: _ =>
    let values := indices.map (fun i => listGetDLocal msg i h)
    Opening.new indices values
where
  listGetDLocal : List (MerkleHasher.Symbol H) → Nat → MerkleHasher.Symbol H →
      MerkleHasher.Symbol H
    | xs, i, d => (xs[i]?).getD d

end Opening
