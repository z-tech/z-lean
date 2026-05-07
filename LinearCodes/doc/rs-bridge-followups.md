# RS Bridge Follow-ups

Audit of places in `LinearCodes/` where the new sharp Reed-Solomon list-decoding infrastructure in `LinearCodes/MCA/RSListDecoding.lean` (notably `reedSolomonSubmodule_isListDecodable_johnson`, `reedSolomonSubmodule_johnson_ncard`, `rs_MCA_list_decoding_bound`, `caseA_implies_bad_event_universal{,_linComb}`, `mcaGoodScalar_iff_submodule_close`, and the `reedSolomonSubmodule` MDS witness) can tighten existing theorems or unblock new ones.

Date: 2026-05-07. Branch: `z-tech/linear-codes`.

---

## High priority

### 1. Replace `2^n` field-size bound with `(l+1)·n²` in `mca_correlated_agreement_caseA` — DONE

- **Status**: **COMPLETED** (2026-05-07). The legacy `mca_correlated_agreement_caseA` (with the `|𝔽| > (l + 1) · 2^n` pigeonhole hypothesis) and its public wrapper `mca_correlated_agreement`, plus the helper `mca_commonSupport_manyScalars_implies_domainWitness`, were removed from `LinearCodes/ReedSolomonProperties.lean`. The sharper `rs_MCA_caseA` in `LinearCodes/MCA/RSListDecoding.lean` is now the canonical case-(a) statement. Build green, 0 sorries, 0 axioms.

### 2. Update `paper-to-lean-map.md` "Future / parked" table — RS bridge entry is stale — DONE

- **Status**: **COMPLETED** (2026-05-07). The full RS submodule bridge API (Phases 1–4 of `MCA/RSListDecoding.lean`, 0 sorries) is documented in the "§9.x — GS-sharpened RS bridge (Guruswami-Sudan track)" section of `paper-to-lean-map.md`, with subsections for the submodule reformulation, the `rsGenerator` alias, the `mcaGoodScalar` reformulation, the RS-specialized list-decoding MCA bound, and the sharper case-(a) variant `rs_MCA_caseA`. The misplaced "Landed" row inside the "Future / parked" table has been removed; a brief pointer to §9.x now sits below the parked table. The `2^n → n²` upgrade (Item 1) landed in tandem; the legacy `mca_correlated_agreement_caseA` / `mca_correlated_agreement` are retired.

---

## Medium priority

### 3. Wire RS list-decoding capstone into `LinearCode.mcaProximityGapError` (close STIR A8 SKIPPED)

- **Location**: `LinearCodes/MCA/Applications/STIR.lean:196-218` (the `A8: LinearCode-typeclass wiring — SKIPPED` block) and `LinearCodes/LinearCode.lean:49-77` (the typeclass).
- **Current state**: A8 is documented as SKIPPED — it requires "a concrete `Code` value wrapping `Submodule F (Fin n → F)`", a `LinearCode` instance whose `mcaProximityGapError` is *defined* by `(max(n·γ,1)+1)·d/q`, and a proof that the runtime field equals the bound. Now that `rs_MCA_list_decoding_bound` exists, the wiring becomes substantially more direct: the `Code` wrapper can just bundle a `ReedSolomonConfig F` (already used everywhere), and `mcaProximityGapError` for the `proven` regime can be defined as `n²·(max(n·γ,1)+1)·l / q` (the bound from RSListDecoding line 626). The `conjectured` regime still needs the capacity-bound formula.
- **Proposed improvement**: Add a new file `LinearCodes/MCA/Applications/RSCodeInstance.lean` (or extend `Applications/Profile.lean`) defining a `ReedSolomonCode` wrapper and a `LinearCode ReedSolomonCode F` instance whose `mcaProximityGapError _ proven l δ q` returns the bound from `rs_MCA_list_decoding_bound`. Add a `proven_bound_correct` theorem certifying the runtime value matches the proved seedProb upper bound.
- **Effort**: ~80-150 lines (typeclass instance + the equality-to-bound theorem + 2-3 sanity examples). 2-4 hours.
- **Priority**: **MEDIUM** — useful for downstream "security profiler" consumers; the STIR file already calls out the wiring as wanted. Not blocking any active proof.

### 4. Fill in `Applications/Profile.lean` with a list-decoding profile

- **Location**: `LinearCodes/MCA/Applications/Profile.lean` (the whole file, 39 lines).
- **Current state**: Holds only `IsSTIRGenerator` (a one-liner predicate) and a sanity check. The docstring promises "Future profiles (WHIR-univariate, WARP) will be added here as their applications are formalized."
- **Proposed improvement**: Add a list-decoding-flavored profile predicate, e.g.:
  - `IsRSListDecodingInstance cfg τ` — bundles `(reedSolomonSubmodule cfg, τ, n²)`-list-decodability via `reedSolomonSubmodule_isListDecodable_johnson` plus the Johnson hypothesis. Sanity: instantiates the predicate from `RSListDecoding`.
  - `IsRSMCAListInstance cfg l τ γ` — bundles the `rs_MCA_list_decoding_bound` hypotheses (Johnson hypothesis on τ + small-γ regime + `l + 1 ≤ |F|`) into a single profile, with the bound exposed as a structure field. Sanity: derive from `rs_MCA_list_decoding_bound`.
  - Optional: `IsWHIRGenerator` (placeholder, blocked on tensor MDS replacement noted in `Tensor.lean:299`).
- **Effort**: ~40-80 lines of definitions + sanity examples. 1-2 hours.
- **Priority**: **MEDIUM** — directly fulfills the file's stated purpose; the new bridge makes RS profiles cleanly statable.

### 5. RS-specialized list-decoding MCA capstone in STIR.lean

- **Location**: `LinearCodes/MCA/Applications/STIR.lean` — currently focused exclusively on the unique-decoding regime (A1: `STIR_MCA_unique_decoding_bound`, A6: `STIR_uniqueDecoding_via_MCA`).
- **Current state**: There is no STIR-flavored list-decoding capstone. The unique-decoding bound (A1) is the `MCA_unique_decoding_bound` specialization, but the analogous list-decoding bound (`MCA_list_decoding_bound` specialized to univariate-powers + RS code) is missing. The new `rs_MCA_list_decoding_bound` already specializes to `Generator.univariatePowers F l`, which **is** the STIR generator — so the STIR list-decoding capstone is now a one-line wrapper.
- **Proposed improvement**: Add `STIR_MCA_list_decoding_bound` (parallel to A1) and `STIR_listDecoding_via_MCA` (parallel to A6) as wrappers around `rs_MCA_list_decoding_bound`, threading the same `ReedSolomonConfig F` parameters STIR uses. Optionally add a sanity `example` mirroring the existing ZMod-7 one (line 94-101).
- **Effort**: ~30-60 lines including the sanity example. 1 hour.
- **Priority**: **MEDIUM** — natural rounding-out of the STIR application file; no novel mathematical content needed.

---

## Low priority

### 6. Tighten the docstring trade-off note in `ReedSolomonProperties.lean` — DONE

- **Status**: **COMPLETED** (2026-05-07). File header in `LinearCodes/ReedSolomonProperties.lean` now points readers at `rs_MCA_caseA` in `MCA/RSListDecoding.lean`; the legacy `2^n`-pigeonhole trade-off discussion was removed along with the legacy theorem itself.

### 7. Sharper `johnson_list_decoding_radius` quantitative bound

- **Location**: `LinearCodes/ReedSolomonProperties.lean:539-603` (`johnson_list_decoding_radius`).
- **Current state**: Proves only `Set.Finite` of the close-codeword set (qualitative). Uses the bespoke injectivity argument via `johnsonAgreementPositions`.
- **Proposed improvement**: Strengthen the conclusion to a quantitative `Set.ncard ≤ cfg.codeLength ^ 2` bound by routing through `reedSolomonSubmodule_johnson_ncard` (RSListDecoding.lean:431, which gives exactly this `n²`-ncard form for the submodule), then transferring back to the `Array F` flavour via the bridges (`arrayEncoded_mem_reedSolomonSubmodule` + `hammingDist_eq_hammingDistance_arrayToFun`). The Array-vs-submodule equivalence on close codewords is a `Set.ncard`-of-an-image argument.
- **Effort**: ~80-120 lines (the Array↔submodule transfer for the close-codeword set requires care because of the `Array.size = messageLength` filter; one option is to phrase the bound on the submodule view and add a corollary). 2-3 hours.
- **Priority**: **LOW** — `johnson_list_decoding_radius` is currently only consumed via its `Set.Finite` content; the quantitative form is mostly nice-to-have unless a downstream consumer needs the count. (Re-check after Item 1 lands; the bridge in Item 1 may already supply the quantitative form for free.)

### 8. STIR A4 (WARP-univariate) — list-decoding companion for `affineSpace F 1`

- **Location**: `LinearCodes/MCA/Applications/STIR.lean:103-143` (the WARP-univariate boundary case).
- **Current state**: Only the unique-decoding bound (A4) is available. The general WARP `affineSpace F s` for `s ≥ 2` is **blocked** by `affineSpace_IsMDS` (line 106), but the boundary `s = 1` is unblocked.
- **Proposed improvement**: Add a `WARP_univariate_list_decoding_bound_s_one` companion that specializes `MCA_list_decoding_bound` (or, with appropriate IsListDecodable hypothesis on the abstract code, `rs_MCA_list_decoding_bound`'s analogue on `affineSpace F 1`). Note: this does **not** directly use `rs_MCA_list_decoding_bound` (which is specialized to RS submodule + `univariatePowers`), but it follows the same pattern and is naturally placed adjacent.
- **Effort**: ~50-100 lines. 1-2 hours.
- **Priority**: **LOW** — independent of the RS sharpening; included here for completeness because it's the obvious symmetric extension once Item 5 lands.

### 9. Add an RS list-decoding sanity example in `Tests.lean` or `Examples_Capstones.lean`

- **Location**: `LinearCodes/Tests.lean` and/or `LinearCodes/MCA/Examples_Capstones.lean`.
- **Current state**: Sanity examples exist for the abstract `MCA_list_decoding_bound` and inline (in `MCA/RSListDecoding.lean`) for `rs_MCA_caseA`, but not yet for the RS-specialized `rs_MCA_list_decoding_bound` or `reedSolomonSubmodule_isListDecodable_johnson` end-to-end.
- **Proposed improvement**: Add a small concrete example over `ZMod 7` or `ZMod 11` exhibiting `reedSolomonSubmodule_isListDecodable_johnson` and `rs_MCA_list_decoding_bound` for tiny parameters (`n = 4, k = 2, τ = 1`). This grounds the abstraction and gives readers a fast smoke test.
- **Effort**: ~30-60 lines (mostly setting up a concrete `ReedSolomonConfig (ZMod p)`). 1 hour.
- **Priority**: **LOW** — purely demonstrative.

---

## Summary table

| # | Location | Improvement | Effort | Priority |
|---|---|---|---|---|
| 1 | `ReedSolomonProperties.lean` | Replace `2^n` field-size bound with `(l+1)·n²` via the new RS submodule bridge — **DONE** (legacy form removed; tight variant in `MCA/RSListDecoding.lean`) | — | DONE |
| 2 | `doc/paper-to-lean-map.md` | Move RS bridge out of "Future / parked"; document its current API — **DONE** (full API documented in §9.x; misplaced "Landed" row removed from parked table) | — | DONE |
| 3 | `Applications/STIR.lean:196` (A8) | `LinearCode` instance for RS using `rs_MCA_list_decoding_bound` | 2-4 h | MEDIUM |
| 4 | `Applications/Profile.lean` | Add `IsRSListDecodingInstance`, `IsRSMCAListInstance` profiles | 1-2 h | MEDIUM |
| 5 | `Applications/STIR.lean` | `STIR_MCA_list_decoding_bound`, `STIR_listDecoding_via_MCA` wrappers | 1 h | MEDIUM |
| 6 | `ReedSolomonProperties.lean` | Update docstring after Item 1 lands — **DONE** | — | DONE |
| 7 | `ReedSolomonProperties.lean:539` | Strengthen `johnson_list_decoding_radius` to `ncard ≤ n²` | 2-3 h | LOW |
| 8 | `Applications/STIR.lean:103` | List-decoding companion for WARP-univariate boundary case | 1-2 h | LOW |
| 9 | `Tests.lean` / `Examples_Capstones.lean` | Concrete RS list-decoding sanity example | 1 h | LOW |

## Recommended sequencing

1. Items 1, 2, 6 — DONE (the doc clean-ups and the highest-leverage proof improvement that removed the only loose bound flagged in the codebase).
2. Items 4 and 5 — quick application-layer expansions, naturally pair with Item 1.
3. Item 3 — wires the bound into the `LinearCode` typeclass for security-profiler consumers.
4. Items 7, 8, 9 — completeness / nice-to-haves.
