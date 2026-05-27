# Changelog

## 2026-05-17 — LinearCodes review fallout

The cumulative result of a council-style review of `LinearCodes/`
(PR #11): 17 commits consolidating P0/P1/P2 punch-list items across
`LinearCodes/` and `Upstream/`. **0 `sorry`, 0 user-declared `axiom`**,
enforced by CI.

### Added

- **RS instance soundness theorem.**
  `ReedSolomonCode.mcaProximityGapError_proven_sound` in new file
  `LinearCodes/ReedSolomonSoundness.lean` proves that the
  `LinearCode` typeclass output upper-bounds the actual MCA bad-event
  seed-probability, via `rs_MCA_list_decoding_bound`. Profilers
  chaining `mcaProximityGapError` through per-protocol soundness
  formulas are now backed by a Lean term, not a docstring promise.
- **Typeclass range obligation** `mcaProximityGapError_in_unit_interval`
  in `LinearCode`. Every instance must prove the returned value lives
  in `[0, 1]`. RS discharges via `rsMCAProximityGapError_in_unit_interval`.
- **Global `ReedSolomon.MCA.*` namespace** (`caseA`, `listDecodingBound`,
  `someAlphaEvadesBadEvent`) as `alias`-backed discoverability layer.
  Four naming surfaces now coexist for the headline capstones:
  paper-flat `rs_MCA_*`, long-flat `reedSolomon_correlatedAgreement_*`,
  namespaced `ReedSolomon.MCA.*`. All resolve to the same theorems.
- **`JohnsonListSize n := n²`** (tight) and
  **`JohnsonListSizeWithSlack ℓ n := (ℓ+1)·n²`** (caller-supplied
  slack). Previously the slack form was the only one and was
  misleadingly called `JohnsonListSize`.
- **Per-subtree READMEs**: `SumcheckProtocol/README.md`, `LinearCodes/README.md`;
  top-level `README.md` slimmed to a summary that links to both.
- **Getting-started doc** at `LinearCodes/doc/getting-started.md` with
  three runnable snippets (encode, security bounds, STIR profiler).
- **Stability tiers** documented (stable / recently-landed / research).
- **CI**: rejects user-declared `axiom` (in addition to the existing
  `sorry` rejection); builds `LinearCodes`, `Upstream`,
  `LinearCodes.Research`, `LinearCodes.Examples` as default lake
  targets (previously CI only built `SumcheckProtocol` — LinearCodes was
  silently unchecked).

### Changed

- **`Type → Type*`** for `LinearCode` typeclass, `ReedSolomonConfig`,
  `ReedSolomonCode`, and the `F` variables across `LinearCodes/` and
  `Upstream/`. No more `Type 0` lockup.
- **`MCA_list_decoding_bound` carries `h_radius : n·γ ≤ τ`** (BCGM25
  §6.2 semantic pin). Without it the theorem allowed `τ=0, L=1` to
  trivially recover the unique-decoding bound dressed as list-decoding.
  Threaded through all callers (`rs_MCA_list_decoding_bound`,
  `rs_MCA_caseA`, `STIR_MCA_list_decoding_bound`).
- **RS instance `mcaProximityGapError .proven`** now returns the
  integer-tight bound from `rs_MCA_list_decoding_bound`
  (`n²·(max(δ,1)+1)·(l-1)/q`, clipped to `[0, 1]`). Previously a
  placeholder `(l-1)·d/q` that didn't match any proven theorem.
- **File reorganisation**:
  - `MCA/ListDecoding{,Counting,Domains,MCA,Witness}.lean` →
    `MCA/ListDecoding/{Core,Counting,Domains,MCA,Witness}.lean`.
  - `MCA/Case2Subtargets.lean` (1479L) split into
    `MCA/Case2/{Counting,MDSBridge,Lemma53}.lean`.
  - `MCA/RSListDecoding.lean` (1419L) split into
    `MCA/RS/{Submodule,ArrayBridge,MCABound}.lean`.
  - `MCA/Examples.lean` → `MCA/Generators.lean` (defines real
    generators, not examples).
  - `LinearCodes/Tests.lean` → `LinearCodes/Examples/RSSmokeTest.lean`
    (separate lake target, no longer in public umbrella).
- **`_implies_` → `_of_`** rename pass (8 names, Mathlib convention).
- **MCA capstone docstrings** include case-numbering crosswalks
  distinguishing Lean's "Case 1 / Case 2" (small-γ / large-γ branches
  of Theorem 6.1) from BCGM25's "case (a) / case (b)" (structural vs
  quantitative form, Theorem 9.2).
- **`Generator.IsMDS` vs `IsMDS`** overload documented in both
  declarations' docstrings to avoid silent confusion.
- **`MutualCorrelatedAgreement γ ≤ 1`** restriction documented:
  outside `[0, 1]` the predicate is either trivial or vacuous.

### Removed

- **Dead theorems**: `zeroEvading_implies_list_decodable_johnson`
  (was `:= True`, no callers) and `bad_witness_list_cw_eq_combine_cstars`
  (no callers, 9 unused hypotheses).
- **Dead docs**: `LinearCodes/doc/rs-bridge-followups.md` (items
  marked DONE) and `LinearCodes/doc/stale-todos-audit.md`
  (one-shot audit, served its purpose).
- **Shim modules**: `LinearCodes/MCA/Case2Subtargets.lean` and
  `LinearCodes/MCA/RSListDecoding.lean` re-export shims (added
  transiently during the splits) have been deleted; all internal
  importers point at sub-files directly.
- **`ListDecodingCstars.lean`** merged into `ListDecoding/Counting.lean`
  (only consumer); the dead `exists_cstars_list_of_MDS` lift was
  dropped.

### Fixed

- **CI now actually builds `LinearCodes/`.** Before, only `SumcheckProtocol`
  was a default lake target; `lake build` (which CI runs) never
  type-checked the LinearCodes tree.
- **`private instance Fact (Nat.Prime 7)`** in `MCA/RS/MCABound.lean`
  changed to `local instance` — `private` doesn't actually hide
  instances from typeclass unification.
- **Stale "this theorem is likely FALSE" banner** at the top of
  `MCA/CAImplications.lean` rewritten — the theorem now carries the
  `0 < ℓ` hypothesis the banner asked for and has been proved.
- **Build-time `#eval` info-spam** from `Lemma53Examples.lean`
  silenced by converting the three `#eval` lines to silent
  `example := by native_decide` regression tests.
- **Unused `h_minDist` on small-γ branch of `MCA_unique_decoding_bound`**
  documented (the hypothesis is only consumed on γ ≥ 1/n).

## 2026-04-21 — TQBF cleanup

- Removed TQBF scaffolding from the main tree (`SumcheckProtocol/IP/TQBF/`,
  `SumcheckProtocol/IP/TQBF.lean`, `SumcheckProtocol/Tests/TQBFTests.lean`). The work — in
  particular the fully-proved multilinear-extension library in `Linearize.lean`
  (specialize0, linearize0, linearize_i, linearizeAll, degree bounds,
  specialize0_commute, eval_arithmetizeLeavingFirst) — remains in git
  history at commit `f24f73a` for resurrection when starting GKR or when
  closing the TQBF `sorry`.

## 2026-04-21 — Inner-product sumcheck

- Added `SumcheckProtocol/IP/InnerProduct.lean`: `InnerProductStatement` +
  `toSumcheckProtocol` reduction to a `SumcheckProtocolStatement` on `f * g`;
  `innerProduct_completeness`, `innerProduct_soundness` as corollaries of
  `sumcheck_hasPerfectCompleteness` / `sumcheck_hasSoundnessError`.
- `innerProduct_soundnessError_le_multilinear`: when both factors are
  multilinear, soundness error `≤ n · 2 / |𝔽|` (via
  `maxIndDegree (f * g) ≤ 2`, itself from `degreeOf_mul_le_c`).
- Thin-wrapper form — `f * g` is materialized. A native two-oracle
  protocol (separate prover state for `f` and `g`) is deferred; the
  current form is enough for downstream protocols that build on
  inner-product claims.

## 2026-04-20 — IP Class + #SAT ∈ IP (unconditional) + TQBF scaffold

- Added `InIP` predicate and `IPCertificate` structure
  (`InteractiveProtocol/Properties/IPClass.lean`) with `InIP.mk` and
  `InIP.of_hasProperties` smart constructors; universe-pinned to
  `PublicCoinProtocol.{0,0,0,0}`.
- Added size-indexed analogues: `IPFamilyCertificate`, `InIPFamily`,
  `InIPFamily.mk`, `InIPFamily.of_hasProperties`. Needed because a fixed
  field can't meet `ε ≤ 1/3` for unbounded-size languages — classical IP
  lets the protocol grow with input size.
- **#SAT ∈ IP proved unconditionally** (`SumcheckProtocol/IP/SharpSAT/`):
  - 3-CNF type, `arithmetize`, `sharpSAT_completeness`,
    `sharpSAT_soundness`, `sharpSAT_soundnessError_le` (concrete
    Schwartz–Zippel bound via individual-degree analysis).
  - `sharpSAT_inIPFamily` — conditional on a field scheme with
    `9k² ≤ |F k|` and `ℕ → F k` injective on `[0, 2^k]`.
  - `sharpSAT_inIPFamily_concrete` — discharges both hypotheses with
    `sharpSATField k := ZMod p_k` where `p_k` is a prime
    `≥ max(2^k + 1, 9k² + 1)` selected via `Nat.exists_infinite_primes`.
- TQBF / Shamir scaffolding (`SumcheckProtocol/IP/TQBF/`):
  - `QBF` datatype, `arithmetizeQBF` + correctness vs `boolToField Q.value`.
  - Full multilinear-extension library (`Linearize.lean`): `specialize0`,
    `linearize0`, `linearize_i`, `linearizeAll`, with evaluation and
    individual-degree bounds (`degreeOf_linearizeAll_le_one`).
  - `specialize0_commute` — 0↔1 rename commutes with nested `specialize0`
    (via new `finSuccEquiv_eval_C_eq_aeval` bridge and `aeval`/`rename`
    composition laws).
  - `eval_arithmetizeLeavingFirst` — scalar evaluation collapses to the
    standard quantifier-fold arithmetization.
  - Shamir protocol defined with raw-degree round polynomials; field-size
    hypothesis `3·2^n ≤ |𝔽|`. `tqbf_inIP` still sorry pending honest-round/
    final-check identities (blocked on a `tqbfHonestMessage` cast refactor).
- Test modules: `SumcheckProtocol/Tests/SharpSATTests.lean`,
  `SumcheckProtocol/Tests/TQBFTests.lean`.

## 2026-04-17 — Canonical Cleanup & eval Migration

- Removed `Adversary` def; `sumcheckProtocol` now uses `Prover` directly
- Removed `AdversaryTranscript` def; replaced by `proverTranscript`
- Slimmed `Transcript` struct: removed `claims` field (now computed on the fly)
- Unified probability definitions: `probEvent` + `allChallenges` live in `InteractiveProtocol`
- Migrated `eval₂ (RingHom.id 𝔽)` to `eval` across ~185 call sites
- Removed `@HAdd.hAdd _ _ _ instHAdd` / `@HMul.hMul` workarounds; now plain `+` and `*` (enabled by CompPoly fork: Verified-zkEVM/CompPoly#192)
- Canonicalized casing across the repo to match Lean/Mathlib conventions
- Bumped mathlib `v4.26.0` → `v4.28.0`

## 2026-04-09 — Interactive Protocol Interface & Refactor

- Generic `PublicCoinProtocol` interface with Fiat-Shamir transformation

## 2026-02-06 — Soundness & Completeness Proved

- `perfect_completeness`: honest prover accepted with probability 1
- `soundness_dishonest`: dishonest claim accepted with probability at most n * d / |F|

## 2025-12-21 — Switch to CMvPolynomial

- Adopted zkEVM `CompPoly` library for computable multivariate polynomials

## 2026-01-02 — End-to-End SumcheckProtocol

- Complete sumcheck implementation over `CMvPolynomial` with computable transcripts
- Prover, verifier, and test suite over concrete fields (ZMod 19)

