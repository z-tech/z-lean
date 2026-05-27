# `VectorCommitment` — Usage

This doc shows the minimal end-to-end flow for using `VectorCommitment` to commit, open, and check. After L1, the example below works for real; at L0, only the typecheck and the size-0 smoke test pass.

---

## 1. The demo hasher

A toy, deterministic hasher over `ZMod 65521`. Non-cryptographic by design — the point is that Rust can mirror the arithmetic bit-for-bit.

```lean
import VectorCommitment

open VectorCommitment

def MyHasher : Type := Unit

instance : MerkleHasher MyHasher where
  Symbol      := ZMod 65521
  Digest      := ZMod 65521
  Salt        := Unit
  decEqDigest := inferInstance
  defaultSalt := ⟨()⟩
  sampleSalt  := fun _ _ => ()
  hashLeaf    := fun _ x _ => x * 31 + 17
  hashNodes   := fun _ cs => (cs.map id).foldl (fun acc d => acc * 31 + d) 1
```

`Salt := Unit` makes this a non-hiding hasher (see [HIDING.md](HIDING.md)).

---

## 2. The shape

A perfect binary tree with 4 leaves (depth 2):

```lean
def shape : PerfectBinary := PerfectBinary.mk 4
```

---

## 3. The scheme

Bundle the hasher value and the shape into a `MerkleCommitment`:

```lean
def scheme : MerkleCommitment MyHasher PerfectBinary :=
  MerkleCommitment.mk () shape
```

---

## 4. Round-trip

Commit to `[1, 2, 3, 4]`, open at indices `{1, 3}`, check the proof:

```lean
def msg : List (ZMod 65521) := [1, 2, 3, 4]

def committed := scheme.commit msg

def opening := Opening.fromMessageIndices msg [1, 3] |>.toOption.get!

def proof := scheme.open msg committed.snd [1, 3]

lemma roundtrip : scheme.check committed.fst.root opening proof = true := by
  native_decide
```

The `native_decide` discharges the goal by actually running `commit` / `open` / `check` at elaboration time.

---

## 5. Cross-checking against `ark-mt`

To use `VectorCommitment` as a correctness oracle for the Rust crate:

1. On the Rust side, instantiate `MerkleHasher` with the same `x * 31 + 17` (leaf) and `acc * 31 + d` (inner) arithmetic, over a matching modular ring (`ZMod 65521` ↔ a `Fp<65521>` newtype).
2. Run `commit` on `[1, 2, 3, 4]` and `open` at indices `{1, 3}`.
3. Compare:
   - the root digest (`committed.fst.root` in Lean ↔ `commitment.root()` in Rust);
   - the digest list inside the opening proof (`proof` in Lean ↔ `OpeningProof::digests()` in Rust).

If both match exactly, the Rust implementation agrees with the Lean spec on this input.

---

## 6. What doesn't work yet at L0

- `commit` / `open` / `check` bodies are `sorry`; the round-trip lemma above only typechecks.
- The real demo arrives at L1. See [ROADMAP.md](ROADMAP.md).
- `HidingVectorCommitment` is a separate typeclass — see [HIDING.md](HIDING.md) to understand why this hasher (`Salt = Unit`) doesn't satisfy it.

---

## 7. For Rust users coming from `ark-mt`

| Rust (`ark-mt`)                    | Lean (`VectorCommitment`)                |
|------------------------------------|----------------------------|
| `MerkleHasher` trait               | `MerkleHasher` typeclass   |
| `MerkleShape` trait                | `MerkleShape` typeclass    |
| `MerkleCommitment<H, S>`           | `MerkleCommitment H S`     |
| `MerkleCommitment::commit(message)`| `scheme.commit msg`        |
| `Opening::from_pairs`              | `Opening.fromPairs`        |
| `OpeningProof<H>`                  | `OpeningProof H`           |
| `CappedMerkleCommitment`           | `CappedMerkleCommitment`   |

Naming convention: Rust `snake_case` becomes Lean `camelCase`; Rust generics `<H, S>` become Lean explicit args `H S`. Otherwise the surface area is intentionally identical so a reader can move between the two crates without re-learning the API.
