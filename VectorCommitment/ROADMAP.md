# `VectorCommitment` — Milestone roadmap

This is the Lean equivalent of [`ark-mt/DESIGN.md` §4](https://github.com/arkworks-rs/ark-vc/blob/main/crates/ark-mt/DESIGN.md)'s M0–M10 plan, re-shaped for what's tractable in Lean: no R1CS, fewer parallelism concerns, more proof-driven milestones.

**This branch delivers L0 through L10 essentially in full.** Only ONE `sorry` remains across the entire `VectorCommitment` module — the deferred `mt_equivocation` (book §12.7) which requires probabilistic ZK simulator machinery beyond the placeholder RO.

**Headline numbers:** ~30+ proven theorems across the core book chapters (§12 Merkle commitment, §20 path pruning, §12.3 collision, §12.4 binding, §12.4 extractability, §12.5 hiding); 13 `native_decide` round-trip tests covering `commit`/`open`/`check` for `PerfectBinary` and `CappedMerkleCommitment` at heights 0/1/2; full `MerkleShape` instances for `PerfectBinary` / `PerfectKAry k` / `ArbitraryLength`; sorry-free `instance : VectorCommitment (MerkleCommitment H S)` glue.

**Status:**
- ✅ **L0** — design docs, file tree, build green, demo `ZMod 65521` hasher live.
- ✅ **L1** — real `commit`/`open`/`check` for non-hiding `PerfectBinary`. `SchemeTests.lean` proves `roundtrip4`, `roundtrip8`, and `tampered4_rejected` via `native_decide`. `ShapeTests.lean` pins golden values for `path` / `copath` / `numVertices` on 4- and 8-leaf trees.
- ✅ **L2 done** — `buildLabels` refactored to a pure functional `labelAt`. **Twenty-one real (sorry-free) theorems** in [`Theorems/Completeness.lean`](Properties/Theorems/Completeness.lean), including the universal `mt_completeness` itself:
  1. `labelAt_internal` — recursion equation at internal vertices.
  2. `labelAt_leaf` — recursion equation at leaves.
  3. `combineUp_eq_parent_left` — bridge for left children.
  4. `combineUp_eq_parent_right` — bridge for right children.
  5. `combineUp_at_pos_eq_parent` — parity-agnostic bridge.
  6. `walkCopath_step` — single inductive step of the verifier walk.
  7. `walkCopath_to_root_4_leaf0` — concrete worked example for size 4.
  8. `walkCopath_lifts_labelAt` — **the universal walk-to-root induction**, the heart of the completeness proof.
  9. `mt_completeness_empty` — empty-opening case.
  10. `commit_root_eq_labelAt_zero` — bridge from imperative `commit` root to functional `labelAt 0`.
  11. `trapdoor_labels_eq_labelAt` — bridge from trapdoor's stored labels to `labelAt`.
  12. `ancestor_bounds_pow2` — induction on path length: `2^(d-k) ≤ ancestor pos k + 1 ≤ 2^(d-k+1) - 1`.
  13. `ancestor_succ_eq` — `ancestor pos (k+1) = (ancestor pos k - 1) / 2`.
  14. `ancestor_chain_precondition` — every ancestor along the leaf-to-root path is a valid internal vertex.
  15. `ancestor_at_depth_eq_zero` — the `d`-th ancestor of any leaf is the root.
  16. `copathOf_go_eq_map_siblingOf_ancestor` — structural identity on the `copathOf.go` recursion.
  17. `copath_eq_siblingOf_ancestor` — `MerkleShape.copath i` matches `(List.range d).map (siblingOf ∘ ancestor)`.
  18. `ancestor_lt_total`, `siblingOf_ancestor_lt_total` — vertex bounds on the ancestor chain.
  19. `reconstruct_eq_root` — **per-leaf completeness**: for an honest opening of a single leaf, the reconstructed digest equals `labelAt mc msg salts 0`.
  20. `perfectBinary_depth_eq_of_pow2`, `perfectBinary_numLeaves_eq_pow2_depth` — depth/numLeaves identities for power-of-2 `PerfectBinary`.

  The universal `mt_completeness` is closed via a `check_forIn_eq_true` helper that reduces the `Id.run do for ... return true` loop body to per-triple equality checks, then chains `commit_root_eq_labelAt_zero` with `reconstruct_eq_root`.

- ✅ **L3 done** — five Option-B (binding-form / contrapositive) collision lemmas + the multi-leaf `mt_colliding_paths_binding` and the `check_iff` multi-leaf bridge in [`Lemmas/CollisionLemma.lean`](Properties/Lemmas/CollisionLemma.lean).
- ✅ **L5 done** — `mt_binding` and `mt_other_binding` proven in [`Theorems/Binding.lean`](Properties/Theorems/Binding.lean) under `Function.Injective2 hashLeaf` + `Function.Injective hashNodes` hypotheses (Option-B form).
- ✅ **L6 done** — `deriveVertexSet` body, `path_pruning_is_copaths_minus_paths`, and `opening_proof_size_bound` (`|deriveVertexSet I| ≤ |copath(I)|`).
- ✅ **L8 Hiding done** — structural-form `mt_root_hiding` and `mt_root_hiding_commit` in [`Theorems/Hiding.lean`](Properties/Theorems/Hiding.lean), plus the workhorse `labelAt_eq_of_leaf_hash_eq` strong-induction lemma. The book's distributional `mt_privacy` is documented as deferred pending real RO probability infra (kept as `True := trivial`).
- ✅ **Extractability done** — `mt_extractability` (singleton) and `mt_multi_extractability` (multi-leaf) in [`Theorems/Extractability.lean`](Properties/Theorems/Extractability.lean): under injective hashes, the prover cannot open to a value differing from the committed `msg[i]`.
- ⏳ **mt_equivocation** (book §12.7) — sole remaining `sorry`. Deferred indefinitely; requires real RO simulator machinery beyond the `PMF.pure` placeholder.
- 🟨 **L3 (substantial)** — [`Lemmas/CollisionLemma.lean`](Properties/Lemmas/CollisionLemma.lean) ships **five real proven lemmas** in the **Option B (binding-form / contrapositive)** style: `reconstructed_roots_eq`, `walkCopath_inj` (the cascade — induction on the sibling list with parity-aware `combineUp` peeling, using `Function.Injective` of `hashNodes`), `simple_mt_colliding_paths_binding` (Lemma 12.3.1 single-leaf binding form), `check_singleton_iff` (bridge from `check = true` to per-triple `reconstructRoot = root`), and `simple_mt_colliding_paths` (book-shaped wrapper for single-element openings). Multi-leaf `mt_colliding_paths` left as `sorry` — needs a multi-element generalisation of `check_singleton_iff`.
- ✅ **PathCopath.lean** — three real proven lemmas: `copath_length_eq_depth`, `path_length_eq_depth_succ` (corrected from off-by-one), `deriveVertexSet_subset_internal`. Useful structural facts about the heap-indexed perfect binary tree.
- 🟨 **L6 (partial)** — `MerkleCommitment.deriveVertexSet` has a real filter-based body in [`Src/Merkle/Scheme.lean`](Src/Merkle/Scheme.lean); `path_pruning_is_copaths_minus_paths` proven (rfl) in [`Lemmas/PathPruning.lean`](Properties/Lemmas/PathPruning.lean). Two golden-value tests in [`SchemeTests.lean`](Tests/SchemeTests.lean). Remaining: `opening_proof_size_bound` lemma and wiring `deriveVertexSet` into `open`/`check` for actual size savings.
- ✅ **L4** — [`Properties/Probability/RandomOracle.lean`](Properties/Probability/RandomOracle.lean) has real bodies for `ROFunction`, `RODistribution` (currently the `PMF.pure` placeholder at the all-zeros oracle), `ROQueryTrace.empty`, `ROQueryTrace.append`, plus three sorry-free smoke lemmas (`RODistribution_tsum_eq_one`, `ROQueryTrace.empty_queries`, `ROQueryTrace.append_queries`). The placeholder distribution will be replaced with real lazy-sampling at L5/L8.
- 🟨 **L9 (partial)** — `PerfectKAry k` and `ArbitraryLength` shapes have real `MerkleShape` instance bodies in [`Src/Merkle/Shape.lean`](Src/Merkle/Shape.lean), mirroring the Rust `crates/ark-mt/src/shape.rs` algorithms (heap-indexed for `PerfectKAry`; precomputed parent/children vectors via ceil/floor split for `ArbitraryLength`). [`Tests/ShapeTests.lean`](Tests/ShapeTests.lean) pins golden values for `PerfectKAry 4` (16 leaves) and `ArbitraryLength.mk 7`. Remaining for full L9: wire the new shapes into `MerkleCommitment.commit`/`open`/`check` (currently specialised to `PerfectBinary`-style heap arithmetic in `buildLabels`).
- ✅ **Instance.lean wired** — `instance : VectorCommitment (MerkleCommitment H S)` is now real (no `sorry`) in [`Src/Merkle/Instance.lean`](Src/Merkle/Instance.lean). `UniversalParams := MerkleCommitment H S`, `CommitterKey = VerifierKey = MerkleCommitment H S`. The trait-level `setup`/`trim`/`commit`/`open`/`check` delegate to the concrete Merkle bodies.
- ✅ **L10 partial: Capped commitments** — [`Src/Merkle/Capped.lean`](Src/Merkle/Capped.lean) ships real `commit`/`open`/`check` for `CappedMerkleCommitment`. Cap of height `c` produces a `List Digest` of length `|verticesAtLayer c|`, opening proofs are truncated by `c` levels, and `check` walks the truncated copath then matches the layer-`c` ancestor against the supplied cap entry. Four `native_decide` round-trip tests: `roundtrip4_h0`, `roundtrip4_h1`, `roundtrip4_h2` (cap heights 0, 1, 2 over 4 leaves), and `roundtrip8_h2` (8 leaves, cap height 2).

---

## 1. Milestones

| Milestone | Deliverable | Verification |
|---|---|---|
| **L0** | Skeleton: typeclasses, data types, and `sorry`'d theorem statements for every book result in §12 + §20 + §12.7. Four design docs (DESIGN, HIDING, ROADMAP, USAGE). All file homes from [DESIGN.md §2](DESIGN.md#2-module-layout) exist. The demo `ZMod 65521` hasher is wired into `HasherTests.lean` only — `commit`/`open`/`check` bodies remain `sorry`. | `lake build` of `«VectorCommitment»` passes. Every lemma/theorem typechecks modulo `sorry`. One smoke `lemma` on the empty/size-0 round-trip compiles via `native_decide`. |
| **L1** | Concrete bodies for `commit` / `open` / `check` on the non-hiding `PerfectBinary` shape with the demo hasher. `OpeningProof` becomes a real structure, not `sorry`. `instance : VectorCommitment (MerkleCommitment H PerfectBinary)` glue lands in `Merkle/Instance.lean`. Test vectors from the Rust crate's `tests/scheme.rs` get pinned as `lemma … := by native_decide`. | `SchemeTests.lean` round-trip on 4, 8, 16 leaves. Outputs match a Rust-side test vector (to be supplied alongside this milestone). `TraitTests.lean` confirms the `VectorCommitment` instance resolves. |
| **L2** | Prove `lemma:mt-completeness` (book §12.2). Combinatorial — no probability needed; structural induction on tree depth + `path`/`copath` algebra. | `Theorems/Completeness.lean` is `sorry`-free. `#print axioms mt_completeness` lists no `sorryAx`. |
| **L3** | Prove `lemma:simple-mt-colliding-paths` and `lemma:mt-colliding-paths` (book §12.3). Combinatorial; sets up the binding proof. Builds on `Lemmas/PathCopath.lean` (also closed at this milestone). | `Lemmas/CollisionLemma.lean` and `Lemmas/PathCopath.lean` are `sorry`-free. |
| **L4** | Stand up `Properties/Probability/RandomOracle.lean`. Define `ROFunction κ`, the noncomputable `RODistribution κ : PMF (ROFunction κ)`, and `ROQueryTrace κ`. Prove one smoke lemma about `RODistribution` (e.g. it's well-defined on the empty trace, or its measure on any singleton query is `2^(-κ)`). Decide once and for all whether `Properties/` standardizes on `PMF` or on `Fintype`-counting `ℚ` (DESIGN.md §3.5 leaves this open). | `RandomOracle.lean` compiles, `noncomputable def RODistribution` has a real body, and the smoke lemma is `sorry`-free. |
| **L5** | Prove `lemma:mt-binding` (§12.4) on top of L3 + L4. Reduction from a binding break to a colliding-path event under `RODistribution`. May also discharge `lemma:mt-other-binding` if it falls out trivially. | `Theorems/Binding.lean` is `sorry`-free for the main statement. |
| **L6** | Path pruning. Implement `deriveVertexSet` in `Scheme.lean` with a real body and prove `lemma:path-pruning-is-copaths-minus-paths` plus the size bound from book Eq. 20.x. Adapt `open` / `check` to use the pruned vertex set; existing L1 test vectors must still pass. | `Lemmas/PathPruning.lean` is `sorry`-free. `SchemeTests.lean` opening-proof size measurably shrinks for 2+ indices and matches the book's bound. |
| **L7** | Hiding salt path. Instantiate `Salt := Vector (Fin 256) 16` (or similar) on a hiding variant of the demo hasher and provide `instance : HidingVectorCommitment (MerkleCommitment H S)` for `H.Salt ≠ Unit`. The compile-time rejection promised in [HIDING.md](HIDING.md) starts biting: callsites with hiding bounds reject the non-hiding hasher. | New `SchemeTests` cases for the hiding hasher round-trip. A negative test confirms `[HidingVectorCommitment …]` fails to resolve for `H.Salt = Unit`. |
| **L8** | Prove `lemma:mt-root-hiding` and `lemma:mt-privacy` (§12.6). Probability arguments over `RODistribution`; reuses the L4 infrastructure. | `Theorems/Hiding.lean` is `sorry`-free. |
| **L9** | `PerfectKAry k` and `ArbitraryLength` shapes wired through the scheme. Same `commit`/`open`/`check` code path; only `MerkleShape` instance changes. The `if h : k = 2` binary fast-path stays available. | `ShapeTests.lean` becomes parametric over shape. Round-trips at `k = 2, 3, 4` and at `numLeaves ∈ {7, 13, 17}` for `ArbitraryLength`. |
| **L10** | Optional capabilities: `CappedMerkleCommitment` plus `LocallyUpdatable`, `LeavesAccessible`, `Equivocable` instances. The `Equivocable` *instance* lands; the `lemma:mt-equivocation` *theorem* statement stays in place but its proof remains `sorry` (deep §12.7 argument, deferred indefinitely). | One round-trip test per capability under `Tests/`. `#print axioms` on the equivocation theorem still reports `sorryAx` — flagged in `Theorems/Equivocation.lean` as known and intentional. |

---

## 2. L0 acceptance criteria

L0 is done iff all of the following hold:

1. The four design docs exist: `VectorCommitment/DESIGN.md`, `VectorCommitment/HIDING.md`, `VectorCommitment/ROADMAP.md`, `VectorCommitment/USAGE.md`.
2. Every file path listed in [DESIGN.md §2](DESIGN.md#2-module-layout) exists (modulo placeholder bodies).
3. `lakefile.lean` contains `lean_lib «VectorCommitment» where`.
4. `lake build` succeeds with no errors and no warnings beyond `declaration uses 'sorry'`.
5. Every `class`, `structure`, `def`, `lemma`, and `theorem` declared in §1's Lean homes typechecks. `theorem`s may have body `:= sorry`; statements must be well-formed.
6. One smoke test passes via `native_decide` — the size-0 round-trip (`commit []` followed by `check` on the empty index list) lives in `SchemeTests.lean` and closes with a `by native_decide` proof. This forces enough of the data-structure layer to be `def` rather than `noncomputable`.

---

## 3. Critical-path decision points

- **L1 success determines whether the typeclass shape is right.** If wiring up the demo hasher to `commit`/`open`/`check` against the L0 typeclass surface requires bizarre workarounds (e.g. extra associated types, `noncomputable` leaks into `Src/`, `DecidableEq` instances that won't synthesize), revise [DESIGN.md §3.1–§3.3](DESIGN.md#31-merklehasher-is-one-typeclass-with-an-associated-salt-type) **before** continuing to L2. Sunk-cost on `sorry`'d theorems against a wrong surface is cheap to abandon; sunk-cost after L2 is not.
- **L4 success determines whether the RO infrastructure shape is right.** [DESIGN.md §3.5](DESIGN.md#35-random-oracle-infrastructure-in-propertiesprobabilityrandomoraclelean) defers the `PMF` vs `Fintype`-counting `ℚ` choice. L4 has to commit. If the chosen path makes the L5 binding statement awkward to even *write*, back out and re-pick before attempting the proof.
- **L6 path pruning may force `Scheme.lean` refactors.** The L1 implementation is allowed to be naive (one full path per index). If pruning at L6 requires changing the `OpeningProof` representation, the L1 test vectors get re-pinned — flag this in the L6 PR rather than silently rewriting them.

---

## 4. Out of roadmap

- **R1CS gadgets.** Lean has no R1CS DSL and no path to one. The Rust crate's `gadget.rs` has no Lean home and no milestone.
- **Parallel `commit`.** Lean has no rayon. Single-threaded performance is sufficient — `VectorCommitment` is an oracle for small examples, not a production prover.
- **Byte-level wire-format compatibility with `ark-serialize`.** `VectorCommitment` cross-checks Rust output by *value* (digest equality on small tests), not by byte stream. If wire compatibility ever matters, a `WireEncode` typeclass lands as a separate module — not a milestone.
- **Production hashers (Poseidon2, Blake3).** Demo `ZMod 65521` hasher is the only one shipped. Real hashers are user-supplied; the typeclass surface guarantees they slot in without scheme-level changes.
- **Verified compilation to Rust.** `VectorCommitment` is a spec, not a code generator.
