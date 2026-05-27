# `VectorCommitment` — Vector commitments + Merkle tree, in Lean

**Status:** Draft — evolving alongside L0–L10 milestones (see [ROADMAP.md](ROADMAP.md)).
**Spec reference:** *Building Cryptographic Proofs from Hash Functions* (Chiesa & Yogev), chapters "Basic commitment scheme" (§11), "Merkle commitment scheme" (§12), and "Merkle commitment scheme optimizations" (§20). [snargsbook.org](https://snargsbook.org/) · [book source](https://github.com/hash-based-snargs-book/hash-based-snargs-book).
**Rust counterpart:** [`arkworks-rs/ark-vc`](https://github.com/arkworks-rs/ark-vc) — the trait crate `ark-vc` and the Merkle backend `ark-mt`. This Lean module mirrors that split inside one Lake library so cross-references stay easy.
**Mandate:**
1. Mirror the Rust trait surface so both implementations are anchored to the same book lemmas.
2. Be runnable (`lemma … := by native_decide` over a concrete hasher instance) so `VectorCommitment` can serve as a correctness oracle for the Rust crate's outputs on small examples.
3. Stake out every book theorem in §12 + §20 with `theorem … := sorry` skeletons, locking the surface area even when individual proofs are deferred.

This document is the architectural source of truth. See [HIDING.md](HIDING.md) for the salt-type / `HidingVectorCommitment` two-class rationale, [ROADMAP.md](ROADMAP.md) for milestone-by-milestone deliverables, and [USAGE.md](USAGE.md) for a worked end-to-end example.

---

## 0. Design principles

These are inherited verbatim from the Rust crate's [`ark-mt/DESIGN.md` §0](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/DESIGN.md), with one Lean-specific addition:

1. **The book's three-method core is the API.** `Commit`, `Open`, `Check` — nothing more at the top level. Every other feature (path pruning, k-ary, arbitrary length, updates, equivocation) attaches to that core as optional typeclasses or as internal behavior of those three methods.
2. **Every associated type we add is a known concession.** The Rust trait keeps three associated types; Lean inherits the same discipline.
3. **The hash trait is one trait, not two.** The book's random oracle `ρ` has variable-arity input and fixed-size output; splitting leaf-hash from inner-hash is arkworks history, not a book requirement.
4. **Parameters travel with the hasher.** The hasher is a *value* (`H : Type*` plus `[MerkleHasher H]` and `(h : H)`) the scheme owns, not a set of static methods.
5. **Footguns become types.** Multi-opening index ordering, power-of-two restrictions, `Ok(false)` for bad proofs — fixed at the type level via subtype invariants, decidable equality, and the `Opening.new`-style validating constructor.
6. **Hiding is a distinct capability, not a parameter of a single scheme.** `VectorCommitment` and `HidingVectorCommitment` are separate typeclasses; downstream code that requires hiding bounds on the second. See [HIDING.md](HIDING.md).
7. **Every book feature must have a Lean home, even if unimplemented.** Skeleton files with `sorry` count.
8. **Computability is non-negotiable for `Src/`.** Everything under `VectorCommitment/Src/` is `def` (not `noncomputable`) so `lake build` of `VectorCommitment.Tests` exercises real round-trips. Probability and information-theoretic statements live under `VectorCommitment/Properties/` and may be `noncomputable`.

---

## 1. What the book says the API has to cover

From the Merkle chapter (§12 of `snargs-book.tex`, lines 12395–14587) plus optimizations (§20, lines 19923–20536) and equivocation (§12.7):

| # | Feature | Book reference | Notes |
|---|---|---|---|
| 1 | `Commit : Σ^ℓ → (C, td)` | §12 Def. (L12413) | Probabilistic iff hiding desired |
| 2 | `Open : (td, I) → π` on subset `I ⊆ [ℓ]` | §12 Def. | Subset opening is primary, not an extension |
| 3 | `Check : (C, I, m[I], π) → {0,1}` | §12 Def., Eq. 12.5 | Single-index check is *derived*, not a separate method |
| 4 | Message alphabet `Σ` | §12 Def. | Leaves are *not* bytes — they're field elements / codeword symbols |
| 5 | Hiding via per-leaf salts of size `s` | §12.6 | `s = 0` reduces cleanly to non-hiding; must not be a separate scheme |
| 6 | Path pruning across multi-opens | §20 "Path pruning" | Internal to `Open`/`Check`, *not* a second set of methods |
| 7 | Arbitrary message length `ℓ` (not just 2^k) | §20 "Any message length" | Tree shape is a parameter of the scheme |
| 8 | k-ary trees | §12 Remark "other arities" | Same scheme definition, different tree |
| 9 | Local updates (O(depth)) | §12 Remark "local updates" | Optional capability; not all trapdoor layouts support it |
| 10 | Trapdoor time-memory tradeoff | §12 Remark "recomputing the tree" | Trapdoor must be opaque so implementations can pick layout |
| 11 | Equivocation (`RootSim`, `OpeningSim`) | §12.7 (L14438) | Used only in ZK analysis; inefficient by design |
| 12 | No-privacy degenerate case | §12 Remark "no privacy" | Falls out of `Salt = Unit` |

Coverage of every row is enforced by the [Roadmap](ROADMAP.md) — every row has a Lean home (file path) by L0, even when the body is `sorry`.

---

## 2. Module layout

```
LeanStuff/
├── VectorCommitment.lean                                    -- umbrella, parallel to Sumcheck.lean / InteractiveProtocol.lean
├── VectorCommitment/
│   ├── DESIGN.md                              -- this file
│   ├── HIDING.md
│   ├── ROADMAP.md
│   ├── USAGE.md
│   ├── Src.lean                               -- imports all Src/*.lean
│   ├── Src/
│   │   ├── DataStructures.lean                -- Alphabet, UniversalParams, CommitterKey, VerifierKey, Commitment, CommitmentState, LabeledCommitment   (mirrors ark-vc/src/data_structures.rs)
│   │   ├── Trait.lean                         -- class VectorCommitment, class HidingVectorCommitment   (mirrors ark-vc/src/vc.rs)
│   │   ├── Multi.lean                         -- class MultiVectorCommitment, class HidingMultiVectorCommitment   (mirrors ark-vc/src/mvc.rs)
│   │   ├── Error.lean                         -- OpeningError, CheckError   (mirrors ark-mt/src/error.rs)
│   │   └── Merkle/
│   │       ├── Hasher.lean                    -- class MerkleHasher   (mirrors ark-mt/src/hasher.rs)
│   │       ├── Shape.lean                     -- class MerkleShape + PerfectBinary, PerfectKAry, ArbitraryLength   (mirrors ark-mt/src/shape.rs)
│   │       ├── Scheme.lean                    -- MerkleCommitment, Trapdoor, Committed, Opening, OpeningProof, deriveVertexSet, commit/open/check   (mirrors ark-mt/src/scheme.rs)
│   │       ├── Capped.lean                    -- CappedMerkleCommitment   (mirrors ark-mt/src/capped.rs)
│   │       ├── Capability.lean                -- class LocallyUpdatable, LeavesAccessible, Equivocable   (mirrors ark-mt/src/capability.rs)
│   │       ├── MultiVector.lean               -- batch impl of MultiVectorCommitment for MerkleCommitment   (mirrors ark-mt/src/multi_vector.rs)
│   │       └── Instance.lean                  -- the `instance : VectorCommitment MerkleCommitment` glue   (mirrors ark-mt/src/vc.rs)
│   ├── Properties.lean
│   ├── Properties/
│   │   ├── Probability/
│   │   │   └── RandomOracle.lean              -- ROFunction, RODistribution, ROQueryTrace   (no Rust analogue — pure spec)
│   │   ├── Lemmas/
│   │   │   ├── PathCopath.lean                -- combinatorial lemmas about path / copath / deriveVertexSet
│   │   │   ├── CollisionLemma.lean            -- §12.3 lemma:simple-mt-colliding-paths, lemma:mt-colliding-paths
│   │   │   └── PathPruning.lean               -- §20 lemma:path-pruning-is-copaths-minus-paths + size bounds
│   │   └── Theorems/
│   │       ├── Completeness.lean              -- §12.2 lemma:mt-completeness
│   │       ├── Binding.lean                   -- §12.4 lemma:mt-binding, lemma:mt-other-binding
│   │       ├── Extractability.lean            -- §12.5 lemma:mt-extractability + multi-extractability variants
│   │       ├── Hiding.lean                    -- §12.6 lemma:mt-root-hiding, lemma:mt-privacy
│   │       └── Equivocation.lean              -- §12.7 lemma:mt-equivocation
│   └── Tests.lean
│       └── Tests/
│           ├── HasherTests.lean               -- demo ZMod p hasher: deterministic, computable, native_decide-friendly
│           ├── ShapeTests.lean                -- PerfectBinary / PerfectKAry / ArbitraryLength: path, copath, deriveVertexSet golden values
│           ├── SchemeTests.lean               -- commit / open / check round-trip
│           └── TraitTests.lean                -- verify MerkleCommitment is a VectorCommitment instance
```

`lakefile.lean` gains one entry: `lean_lib «VectorCommitment» where`. No new external dependencies — Mathlib `v4.28.0` already supplies `PMF`, `Finset`, `ZMod`, `ByteArray`.

---

## 3. Key design choices (with Rust-side anchors)

### 3.1 `MerkleHasher` is one typeclass with an associated `Salt` type

Mirrors [`ark-mt/src/hasher.rs:33-58`](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/src/hasher.rs):

```lean
class MerkleHasher (H : Type*) where
  Symbol : Type*
  Digest : Type*
  Salt   : Type*
  decEqDigest : DecidableEq Digest
  defaultSalt : Inhabited Salt
  /-- Sample a fresh salt from a finite seed. Tests fix the seed for
      reproducibility; a real implementation would consume entropy. -/
  sampleSalt : H → ULift.{0} UInt64 → Salt
  /-- ρ(symbol, salt) at a leaf. -/
  hashLeaf   : H → Symbol → Salt → Digest
  /-- ρ(child₁, …, childₖ) at an internal vertex. `children.length` is the
      arity at this vertex (fixed for balanced trees, may vary for the
      arbitrary-length tree per §20). -/
  hashNodes  : H → List Digest → Digest
```

*Why two methods instead of one `hash : H → ByteArray → Digest`*: because the book distinguishes them — different arity, different domain, different security analysis. Forcing a single method either pins us to a byte encoding (slow for field-friendly hashers like Poseidon2) or re-introduces a `DigestConverter` mess.

*Why the hasher is a value `(h : H)` rather than only a typeclass `[MerkleHasher H]`*: parameters (Poseidon round constants, domain-separation tags, Blake3 init context) live inside the hasher value. One object, owned by the tree.

*Why `Salt` as an associated type instead of a `(saltSize : ℕ)` parameter*: the salt type is a property of the hasher, not of the scheme. Non-hiding hashers set `Salt := Unit` — zero-size, computed away by the kernel; the `sampleSalt` no-op compiles to a unit return. Hiding hashers set `Salt := Vector (Fin 256) 16` (or whatever their analysis demands). The scheme signature `MerkleCommitment H S` carries no extra generic — the salt story rides along on the hasher.

*How this interacts with the two-class hiding split.* The `Salt` associated type determines *which* of the `VectorCommitment.Trait` typeclasses `MerkleCommitment H S` implements. `H.Salt = Unit` ⇒ non-hiding only; `H.Salt ≠ Unit` ⇒ both. Full analysis in [HIDING.md](HIDING.md).

*Domain separation.* Lives inside the hasher value, exactly as in the Rust crate. A user-supplied `Poseidon2Hasher` carries its DS tag in a struct field; `hashLeaf` and `hashNodes` use it implicitly. No extra typeclass parameter pollutes the scheme signature.

### 3.2 `MerkleShape` is a typeclass; three concrete instances

Mirrors [`ark-mt/src/shape.rs`](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/src/shape.rs):

```lean
structure VertexId where
  val : ℕ
  deriving DecidableEq, Repr, Hashable

class MerkleShape (S : Type*) where
  numLeaves : S → ℕ
  depth : S → ℕ
  numVertices : S → ℕ
  root : S → VertexId
  leaf : S → ℕ → VertexId
  children : S → VertexId → List VertexId
  isLeaf : S → VertexId → Bool
  path : S → ℕ → List VertexId
  copath : S → ℕ → List VertexId
  internalVerticesBottomUp : S → List VertexId
  verticesAtLayer : S → ℕ → List VertexId
```

Provided instances:

- `PerfectBinary` — book §12 base case. Heap-indexed BFS layout (root = 0, children of `v` are `2v+1, 2v+2`).
- `PerfectKAry (k : ℕ) [hk : Fact (1 < k)]` — book §12 Remark "other arities". `k` is a natural-number parameter (Lean has no ergonomic const-generic story, so we bundle a `Fact` constraint instead). Binary-only fast paths can specialize via `if h : k = 2 then …`.
- `ArbitraryLength` — book §20 Definition 20.x.1 family. Pre-computes parent/children vectors at construction time so every `MerkleShape` method becomes a cheap `Vector` lookup.

Capping is a *scheme-level modifier* (`CappedMerkleCommitment`), not a `MerkleShape` instance — same reasoning as the Rust crate's M6 revision (a cap is a `List H.Digest`, not a single `root` vertex, so it can't satisfy the trait's contract).

### 3.3 The abstract `VectorCommitment` typeclass mirrors `ark-vc/src/vc.rs`

```lean
class VectorCommitment (V : Type*) where
  Alphabet         : Type*
  Index            : Type*
  UniversalParams  : Type*
  CommitterKey     : Type*
  VerifierKey      : Type*
  Commitment       : Type*
  CommitmentState  : Type*
  Proof            : Type*
  /-- Trusted setup. Returns universal parameters; tests fix the RNG seed. -/
  setup  : (maxLen maxQueries : ℕ) → ULift.{0} UInt64 → UniversalParams
  /-- Trim universal parameters to a specific length / query budget. -/
  trim   : UniversalParams → (len queries : ℕ) → CommitterKey × VerifierKey
  /-- Commit to a message vector. Returns the commitment and an opaque state
      (containing the trapdoor). -/
  commit : CommitterKey → List Alphabet → Commitment × CommitmentState
  /-- Construct an opening proof for a subset of locations. -/
  «open» : CommitterKey → List Alphabet → Commitment → List Index → List Alphabet → CommitmentState → Proof
  /-- Verify an opening proof. Returns `true` for an honest proof; returns
      `false` for a forged proof; an `OpeningError` is raised at construction
      time for malformed inputs (sortedness/uniqueness/length-mismatch),
      not via this `Bool` (mirrors `ark-mt`'s footgun fix §2.4). -/
  check  : VerifierKey → Commitment → List Index → List Alphabet → Proof → Bool
```

`ProverChannel` / `VerifierChannel` are deliberately omitted from L0. The Rust trait threads transcripts through the channel for Fiat-Shamir composition. We defer that — when integrating with [`InteractiveProtocol/Src/Protocol.lean`](../InteractiveProtocol/Src/Protocol.lean), VectorCommitment's `commit` output becomes a `ProverMessage`. The channel-threaded variant arrives in L2 (see [ROADMAP.md](ROADMAP.md)).

### 3.4 Computability — `Src/` is `def`, `Properties/` is `noncomputable`

Tests use `lemma … := by native_decide` (matching [`Sumcheck/Tests/TranscriptTests.lean`](../Sumcheck/Tests/TranscriptTests.lean)) so `commit` / `open` / `check` round-trips are verified at build time. `OpeningProof` carries `DecidableEq` so equality assertions work under `native_decide`. The demo hasher in `VectorCommitment/Tests/HasherTests.lean` is a plain `def` over `ZMod 65521` — a prime small enough to fit in `UInt32`, large enough to make collisions unlikely on tiny inputs, and trivial to mirror in Rust.

### 3.5 Random-oracle infrastructure in `Properties/Probability/RandomOracle.lean`

The book's binding / extractability / hiding / equivocation lemmas are stated relative to `ρ ← 𝓤(RO_κ)`. The repo currently uses ad-hoc `Fintype`-counting `ℚ` for probability ([`InteractiveProtocol/Properties/Probability.lean:12-23`](../InteractiveProtocol/Properties/Probability.lean#L12-L23)); for `mt-binding` and friends we need a proper RO model:

```lean
/-- Idealized random oracle: a function from queries to fixed-size digests. -/
def ROFunction (κ : ℕ) : Type := List ByteArray → Vector Bool κ

/-- The uniform distribution over random oracles. Noncomputable. -/
noncomputable def RODistribution (κ : ℕ) : PMF (ROFunction κ) := sorry

/-- A query-answer trace: the queries an algorithm has made to ρ and the
    answers it received. Used for the collision lemma (§12.3). -/
structure ROQueryTrace (κ : ℕ) where
  queries : List (List ByteArray × Vector Bool κ)
```

L0 only requires that the *statements* of `mt-binding` etc. typecheck against this infrastructure — the `RODistribution` body is `sorry`, the lemmas are `sorry`. L4 builds it out properly.

---

## 4. Coverage of every book feature

| # | Book feature | Lean home |
|---|---|---|
| 1 | `Commit : Σ^ℓ → (C, td)` | `VectorCommitment/Src/Merkle/Scheme.lean :: MerkleCommitment.commit` |
| 2 | `Open : (td, I) → π` | `VectorCommitment/Src/Merkle/Scheme.lean :: MerkleCommitment.open` |
| 3 | `Check : (C, I, m[I], π) → {0,1}` | `VectorCommitment/Src/Merkle/Scheme.lean :: MerkleCommitment.check` |
| 4 | Message alphabet `Σ` | `MerkleHasher.Symbol` (associated type) |
| 5 | Hiding via per-leaf salts of size `s` | `MerkleHasher.Salt` + `HidingVectorCommitment` typeclass |
| 6 | Path pruning | `Scheme.lean :: deriveVertexSet`, used inside `open` / `check` |
| 7 | Arbitrary message length `ℓ` | `Shape.lean :: ArbitraryLength` |
| 8 | k-ary trees | `Shape.lean :: PerfectKAry` |
| 9 | Local updates (O(depth)) | `Capability.lean :: class LocallyUpdatable` |
| 10 | Trapdoor time-memory tradeoff | `Trapdoor` opaque (private constructor + accessor pattern) |
| 11 | Equivocation | `Capability.lean :: class Equivocable`; statement in `Theorems/Equivocation.lean` |
| 12 | No-privacy degenerate case | Falls out of `Salt = Unit`; verified by `TraitTests.lean` |

---

## 5. Reused existing utilities

- [`InteractiveProtocol/Src/Protocol.lean :: PublicCoinProtocol`](../InteractiveProtocol/Src/Protocol.lean) — anchors the future channel-threaded VectorCommitment variant in L2; not used at L0.
- [`InteractiveProtocol/Src/FiatShamir.lean :: RandomOracle`](../InteractiveProtocol/Src/FiatShamir.lean) — the existing `List ℕ → C` hash-to-field abstraction. Aligned with `MerkleHasher` once they need to interoperate.
- [`InteractiveProtocol/Properties/Probability.lean :: probEvent`](../InteractiveProtocol/Properties/Probability.lean) — `Fintype`-counting probability, used as the seed for `Properties/Probability/RandomOracle.lean`.
- Test style from [`Sumcheck/Tests/TranscriptTests.lean`](../Sumcheck/Tests/TranscriptTests.lean): `def` concrete witnesses + `lemma … := by native_decide`.

---

## 6. Open questions

1. **`Symbol` vs `ByteArray`.** Do we parametrize on `H.Symbol` through the whole module, or do we require `Symbol : Encodable ByteArray` and work on bytes internally? First is cleaner; second might be required to share paths across hash families.
2. **`MerkleHasher` as value vs zero-sized marker.** Lean has no Rust-style ZST. We make `H : Type*` carry the configuration; for zero-data hashers (e.g., `Blake3Hasher`) the user sets `H := Unit` and supplies the methods statically.
3. **`Decidable` boundaries.** `check` returns `Bool`; `Opening.new` returns `Sum OpeningError Opening`. Both are needed — `native_decide`-friendly equality checking and human-readable errors at construction time.
4. **Cap height as a static parameter.** Passed at scheme construction (`CappedMerkleCommitment.mk hasher shape capHeight`); not a scheme-level type parameter, so downstream signatures stay clean.
5. **Concurrency.** Lean has no rayon. Ignored — the book's lemmas don't depend on parallelism, and `commit` is rarely the bottleneck for cross-checking small examples.
6. **Wire format.** Rust uses `ark-serialize`. Lean has no analogue; if byte-level cross-check with Rust matters, define a `WireEncode` typeclass at L1.

---

## 7. Non-goals

- **Bit-for-bit compatibility with `ark-crypto-primitives::merkle_tree`.** That's the Rust crate's problem.
- **R1CS / `gadget.rs`.** Lean has no R1CS DSL. Out of scope for the whole roadmap.
- **Production hashers.** We provide one demo hasher (`ZMod 65521`) for tests. Real hashers (Poseidon2, Blake3) are user-supplied — the typeclass surface guarantees they slot in.
- **Verified compilation to Rust.** `VectorCommitment` is an oracle, not a code generator.

---

## 8. Call for review

Reviewers: is the four-typeclass surface (`MerkleHasher`, `MerkleShape`, `VectorCommitment`, `HidingVectorCommitment`) the right shape for Lean? Specific questions:

- Any book feature in §1 that doesn't have a Lean home above?
- Any Rust pain point in [`ark-mt/DESIGN.md` §2](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/DESIGN.md) that we haven't addressed?
- Anything in §6 open questions you have a strong opinion on (`Symbol` vs `ByteArray`, RO infrastructure shape, wire encoding)?
