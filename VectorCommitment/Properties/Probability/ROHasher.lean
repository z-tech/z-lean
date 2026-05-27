import VectorCommitment.Src.Merkle.Hasher
import VectorCommitment.Properties.Probability.RandomOracle

/-!
# RO-derived MerkleHasher (with domain separation)

This file is the bridge between the abstract `MerkleHasher` typeclass
(`VectorCommitment/Src/Merkle/Hasher.lean`) and the random-oracle model
(`VectorCommitment/Properties/Probability/RandomOracle.lean`).

Given a deterministic oracle function `ρ : List ByteArray → List.Vector
Bool κ` (the "function view" of an RO), this file constructs a concrete
`MerkleHasher` instance whose leaf-hash and node-hash are domain-separated
queries to `ρ`. The probabilistic-security theorems in
`VectorCommitment/Properties/Probability/Instances/…` quantify over the
random choice of `ρ` and lift this deterministic construction into the
real RO model.

## Domain separation

The encoding distinguishes leaf queries from internal-node queries via
distinct single-byte tags: `Tag.leaf = ⟨#[0]⟩`, `Tag.node = ⟨#[1]⟩`. This
prevents the "tree-shape attack" where an internal-node digest is
reinterpreted as a leaf value (or vice versa) — a structural attack that
no `q²/2^κ` collision bound can cover.

The injectivity of the tagged encoding plus distinctness of the tag
prefixes give the splitting lemma `encodeLeaf_ne_encodeNodes` below:
LEAF-tagged queries and NODE-tagged queries occupy disjoint input
ranges. Combined with the uniform-RO model this yields the formal
"`ρ_LEAF` and `ρ_NODE` are independent oracles" property the binding /
extractability / hiding / equivocation reductions consume.
-/

namespace ROHasher

/-- Single-byte domain-separation tag for leaf hashes. -/
def Tag.leaf : ByteArray := ⟨#[0]⟩

/-- Single-byte domain-separation tag for internal-node hashes. -/
def Tag.node : ByteArray := ⟨#[1]⟩

/-- Encode a leaf query: `LEAF :: symbol bytes ++ salt bytes`. -/
def encodeLeaf (sym salt : List ByteArray) : List ByteArray :=
  Tag.leaf :: sym ++ salt

/-- Encode an internal-node query: `NODE :: serialized children`.
    A child digest `d : List.Vector Bool κ` is serialized to a `ByteArray`
    by mapping each bit to a 0/1 byte. This is wasteful in bytes but
    simple, injective, and unambiguous about boundaries (every child
    contributes exactly `κ` bytes). -/
def encodeNodes {κ : Nat} (children : List (List.Vector Bool κ)) :
    List ByteArray :=
  Tag.node ::
    children.map fun d =>
      ⟨(d.toList.map (fun b => if b then (1 : UInt8) else (0 : UInt8))).toArray⟩

/-- Domain separation: a leaf encoding never coincides with a node
    encoding. The two start with distinct tag bytes. -/
theorem encodeLeaf_ne_encodeNodes
    {κ : Nat} (sym salt : List ByteArray)
    (children : List (List.Vector Bool κ)) :
    encodeLeaf sym salt ≠ encodeNodes children := by
  intro h
  -- Both lists are nonempty with their tag byte as the head.
  have h_head :
      (encodeLeaf sym salt).head? = (encodeNodes children).head? :=
    congrArg List.head? h
  -- Reduce the heads to the literal tag ByteArrays.
  simp [encodeLeaf, encodeNodes, Tag.leaf, Tag.node, List.head?] at h_head

/-- The hasher value: a thin wrapper around a sampled RO function. -/
structure ROHasherValue (κ : Nat) where
  oracle : List ByteArray → List.Vector Bool κ

/-- `MerkleHasher` instance for the RO-derived hasher.

    The symbol and salt types are `List ByteArray` — concrete enough that
    the RO can take them as queries, abstract enough that callers can
    encode whatever symbol/salt they need into bytes.

    The salt sampler is a placeholder (returns `[]`); the hiding and
    equivocation instances will provide real per-leaf salts. -/
noncomputable instance instMerkleHasherROHasher (κ : Nat) :
    MerkleHasher (ROHasherValue κ) where
  Symbol := List ByteArray
  Digest := List.Vector Bool κ
  Salt := List ByteArray
  decEqDigest := inferInstance
  defaultSalt := ⟨[]⟩
  sampleSalt := fun _ _ => []
  hashLeaf := fun h sym salt => h.oracle (encodeLeaf sym salt)
  hashNodes := fun h children => h.oracle (encodeNodes children)

/-- The `OracleSpec` corresponding to a Merkle RO with `κ`-bit digests.
    Used by the Layer-3 ROM instance files to run experiments in
    `OracleComp` and reason about query traces. -/
def MerkleROSpec (κ : Nat) : OracleSpec where
  Domain := List ByteArray
  Range  := List.Vector Bool κ
  decEqDomain := inferInstance
  fintypeRange := inferInstance
  inhabitedRange := ⟨List.Vector.replicate κ false⟩

end ROHasher
