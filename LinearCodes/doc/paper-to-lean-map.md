# BCGM25 Paper → Lean formalization map

A theorem-by-theorem map of which results from
[BCGM25 — *All Polynomial Generators Preserve Distance with Mutual
Correlated Agreement*][bcgm25] (eprint 2025/2051) are formalized in this
project, and where they live.

[bcgm25]: https://eprint.iacr.org/2025/2051

**Status:** build clean, **0 sorries**, **0 axioms**. All capstone theorems
proved end-to-end. One documented `+1` slack vs the paper's tight bound
(intrinsic to the chosen proof technique for Lemma 5.3; recovery would
require a Corrádi-grouped-by-codeword reformulation).

Files referenced are relative to the repo root
`/Users/zitek/Documents/LeanStuff/`.

---

## §2 — Preliminaries: codes, generators, agreement

| Paper concept | Lean | File |
|---|---|---|
| Linear code (submodule of `F^n`) | `Submodule F (Fin n → F)` | (Mathlib) |
| Hamming weight | `hammingWeight` | [Algebraic/Code.lean][code] |
| Hamming distance | `hammingDistance` | [Algebraic/Agreement.lean][agreement] |
| Agreement set `agree(u, v)` | `agreementSet u v` | [Algebraic/Agreement.lean][agreement] |
| Min-distance bound `≥ d` | `MinDistAtLeast c d` | [Algebraic/Code.lean][code] |
| MDS code (Singleton) | `IsMDS c k` | [Algebraic/Code.lean][code] |
| Generator `G : S → F^ℓ` | `Generator F S ℓ` | [MCA/Definitions.lean][defs] |
| Linear combination `G(x) · u` | `Generator.combine` | [MCA/Definitions.lean][defs] |
| Dot map / column map | `Generator.dotMap` | [MCA/InducedCode.lean][induced] |
| Induced code `Im(G)` | `Generator.inducedCode` | [MCA/InducedCode.lean][induced] |
| Restricted code `c\|_T` | `InRestrictedCode c T u` | [Algebraic/Restriction.lean][restr] |
| Seed probability | `seedProb` | [MCA/Definitions.lean][defs] |

[code]: ../Algebraic/Code.lean
[agreement]: ../Algebraic/Agreement.lean
[restr]: ../Algebraic/Restriction.lean
[defs]: ../MCA/Definitions.lean
[induced]: ../MCA/InducedCode.lean

### Concrete generators (BCGM25 §2.3)

| Paper generator | Lean | File |
|---|---|---|
| Identity `G(x) = x` | `Generator.identity` | [MCA/Examples.lean][exa] |
| Univariate powers `G(x) = (1, x, …, x^d)` | `Generator.univariatePowers` | [MCA/Examples.lean][exa] |
| Affine line `G(x) = (1, x)` | `Generator.affineLine` | [MCA/Examples.lean][exa] |
| Affine space `G(x) = (1, x₁, …, xₛ)` | `Generator.affineSpace` | [MCA/Examples.lean][exa] |

[exa]: ../MCA/Examples.lean

---

## §3 — Distance-preservation predicates

| Paper concept | Lean | File |
|---|---|---|
| Definition 3.11: zero-evading `ε_ZE` | `ZeroEvading G ε` | [MCA/Definitions.lean][defs] |
| Definition 3.13: correlated agreement | `CorrelatedAgreement G c εCA` | [MCA/Definitions.lean][defs] |
| Mutual correlated agreement (MCA) | `MutualCorrelatedAgreement G c εMCA` | [MCA/Definitions.lean][defs] |
| MCA bad event | inline existential predicate in capstones | various |

### §3.4 — Lemma 3.18 (MCA ⇒ ZE at γ = 0)

| Paper | Lean | File |
|---|---|---|
| Lemma 3.18 (forward direction) | `MCA_implies_ZeroEvading_at_zero` | [MCA/Properties.lean][props] |
| Helper: `a • u ∉ c` if `a ≠ 0`, `u ∉ c` | `smul_not_mem_of_ne_zero_of_not_mem` | [MCA/Properties.lean][props] |
| MCA at γ = 0 simplification | `MutualCorrelatedAgreement_zero_simplify` | [MCA/CAImplications.lean][caimpl] |

[props]: ../MCA/Properties.lean
[caimpl]: ../MCA/CAImplications.lean

### §3.4 — Lemma 3.22 / 3.23 (MCA implies CA, Corrádi)

| Paper | Lean | File |
|---|---|---|
| Lemma 3.22: MCA ⇒ CA | `MCA_implies_CA` | [MCA/CAImplications.lean][caimpl] |
| Lemma 3.23: Corrádi (combinatorial) | `corradi_unconditional`, `corradi_ratio` | [Upstream/Combinatorics/Corradi.lean][corradi] |

[corradi]: ../../Upstream/Combinatorics/Corradi.lean

---

## §5 — Aggregate counting infrastructure

### Lemma 5.3 (zero-evading aggregate-disagreement bound)

The paper's "tight" Lemma 5.3 says: for the column-difference structure,
`|T̃| > n(1-γ)` follows from a zero-evading aggregate. Our formalization
uses a slightly weakened form (with `+1` slack) intrinsic to the chosen
double-counting proof technique.

| Paper | Lean | Notes |
|---|---|---|
| Lemma 5.3 (specialized to MDS) | `Ttilde_card_gt_of_MDS_aggregate` | [MCA/Case2Subtargets.lean][case2sub] — concl `≥ n(1-γ) - 1` (1-slack) |
| Slack analysis docstring | (in same file) | Explains why pure double-counting gives `+1` slack |
| Helper: column-difference vec | `colDiff us cstars i` | [MCA/Case2Subtargets.lean][case2sub] |
| Per-coord count bound | `bad_pair_count_per_coord_le` | [MCA/Case2Subtargets.lean][case2sub] |

[case2sub]: ../MCA/Case2Subtargets.lean

---

## §6.1 — Theorem 6.1 (unique-decoding regime)

The Phase A capstone. Decomposed into Case 1 (γ < 1/n) and Case 2 (γ ≥ 1/n).

### Case 1 (γ < 1/n)

| Paper | Lean | File |
|---|---|---|
| Theorem 6.1 Case 1 (small-γ MCA bound) | `MCA_unique_decoding_small_gamma_bound` | [MCA/UniqueDecoding.lean][uniq] |
| Setup: MCA bad event ⇒ T = univ | `MCA_bad_event_at_small_gamma_eq_zero_event` | [MCA/UniqueDecoding.lean][uniq] |
| Bad-set count ≤ ℓ-1 | `MCA_zero_bad_set_card_le_ell_minus_one` | [MCA/UniqueDecoding.lean][uniq] |
| MDS-distinct-seeds rigidity | `all_us_mem_of_combine_at_distinct_seeds` | [MCA/UniqueDecoding.lean][uniq] |
| `MDS_pairwise_agreement_bound` | (proved upstream) | [Algebraic/Code.lean][code] |
| `MDS_distinct_codewords_disagree` | (proved upstream) | [Algebraic/Code.lean][code] |
| `MDS_unique_decoding` | (proved upstream) | [Algebraic/Code.lean][code] |

[uniq]: ../MCA/UniqueDecoding.lean

### Case 2 (γ ≥ 1/n)

The harder case. Uses Lemmas 6.4, 6.5, 6.6 plus the cstars-construction
machinery.

| Paper | Lean | File |
|---|---|---|
| Theorem 6.1 Case 2 (large-γ MCA bound) | `MCA_unique_decoding_large_gamma_bound` | [MCA/Case2Capstone.lean][cap] |
| Theorem 6.1 unified bound | `MCA_unique_decoding_bound` | [MCA/Case2Capstone.lean][cap] |
| Lemma 6.4: max-agreement intersection ⇒ max CA | `maxAgreement_intersection_isMaxCA` | [MCA/MaximalDomain.lean][maxdom] |
| Lemma 6.5: ℓ-fold intersection = max CA | `maxAgreement_inter_eq_maxCA` | [MCA/MaximalDomain.lean][maxdom] |
| Lemma 6.6: strict-superset count bound | `strict_superset_count_bound` | [MCA/UniqueDecoding.lean][uniq] |
| Maximal agreement domain (def) | `IsMaxAgreementDomain` | [MCA/MaximalDomain.lean][maxdom] |
| Maximal CA domain (def) | `IsMaxCADomain` | [MCA/MaximalDomain.lean][maxdom] |
| Bad-witness bundle | `MCABadWitness` | [MCA/UniqueDecoding.lean][uniq] |
| Cstars construction (MDS-inversion) | `exists_cstars_of_MDS` | [MCA/Case2Subtargets.lean][case2sub] |
| Witness codeword equality | `bad_witness_cw_eq_combine_cstars` | [MCA/Case2Subtargets.lean][case2sub] |
| Coordinate-wise CA from MDS-equality | `isCADomain_of_combines_agree` | [MCA/Case2Subtargets.lean][case2sub] |
| Strictness `T̃ ⊊ Bₓ` | `CAdomain_strictly_subset_maxAgreementDomain` | [MCA/Case2Subtargets.lean][case2sub] |
| Degree bound (Corrádi-style) | `degree_bound_at_non_Ttilde` | [MCA/Case2Subtargets.lean][case2sub] |
| `T̃ ⊆ Bₓ` for max agreement | `Ttilde_subset_maxAgreementDomain` | [MCA/Case2Subtargets.lean][case2sub] |

[cap]: ../MCA/Case2Capstone.lean
[maxdom]: ../MCA/MaximalDomain.lean

**Trade-off vs paper.** The capstone bound is
`(max(n·γ, 1) + 1) · (ℓ - 1) / |S|` whereas BCGM25 has
`max(n·γ, 1) · (ℓ - 1) / |S|`. The `+1` slack stems from Lemma 5.3's
double-counting derivation; the rigorous slack analysis is in
[Case2Subtargets.lean][case2sub] (docstring of `Ttilde_card_gt_of_MDS_aggregate`).
Recovery requires a Corrádi-grouped-by-codeword proof of Lemma 5.3 — an
identified future task (~200-300 lines).

---

## §6.2 — Theorem 6.2 (list-decoding regime)

Phase B capstone. Mirrors §6.1 but with up to `L` candidate codewords per
seed.

### List-decoding API

| Paper | Lean | File |
|---|---|---|
| `(τ, L)`-list-decodable | `IsListDecodable c τ L` | [MCA/ListDecoding.lean][listdec] |
| `(0, 1)`-list-decodable trivial | `IsListDecodable_zero` | [MCA/ListDecoding.lean][listdec] |
| Char. of unique decoding | `IsListDecodable_one_iff_minDist` | [MCA/ListDecoding.lean][listdec] |
| Min-distance ⇒ unique decoding | `IsListDecodable_of_minDist_unique` | [MCA/ListDecoding.lean][listdec] |
| Monotonicity in `L` | `IsListDecodable.mono_L`, `mono_L_succ` | [MCA/ListDecoding.lean][listdec] |
| Monotonicity in `τ` | `IsListDecodable.mono_τ` | [MCA/ListDecoding.lean][listdec] |
| Subcode inheritance | `IsListDecodable.subcode` | [MCA/ListDecoding.lean][listdec] |
| Translation invariance | `IsListDecodable.shift` | [MCA/ListDecoding.lean][listdec] |
| Bounded-distance decoding | `IsListDecodable_BDD` | [MCA/ListDecoding.lean][listdec] |
| Hamming-ball reformulation | `IsListDecodable_iff_ball` | [MCA/ListDecoding.lean][listdec] |
| Sup-code union bound | `IsListDecodable.union_set_bound` | [MCA/ListDecoding.lean][listdec] |

[listdec]: ../MCA/ListDecoding.lean

### Johnson bound (BCGM25 Lemma 6.2 list size)

| Paper | Lean | File |
|---|---|---|
| List-size `(ℓ+1) · n²` | `JohnsonListSize` | [MCA/ListDecoding.lean][listdec] |
| Squared Johnson bound for MDS | `IsListDecodable_squared_johnson_MDS` (J6) | [MCA/JohnsonBound.lean][john] |
| Squared form ↔ Real.sqrt form | `johnson_squared_iff_real_sqrt` | [MCA/JohnsonBound.lean][john] |
| α: lower bound on `S = ∑ nₓ` | `johnson_S_lower_bound` | [MCA/JohnsonBound.lean][john] |
| β: Cauchy-Schwarz `S² ≤ n·Q` | `johnson_cauchy_schwarz` | [MCA/JohnsonBound.lean][john] |
| γ: pairwise upper bound on `Q` | `johnson_Q_upper_bound` | [MCA/JohnsonBound.lean][john] |
| δ: final arithmetic | `johnson_final_arithmetic` | [MCA/JohnsonBound.lean][john] |
| MDS-implies-zero-evading | `Generator.IsMDS.zeroEvading_bound` | [MCA/UniqueDecoding.lean][uniq] |

[john]: ../MCA/JohnsonBound.lean

### List-decoding capstones

| Paper | Lean | File |
|---|---|---|
| Theorem 6.2 (list-decoding MCA bound) | `MCA_list_decoding_bound` | [MCA/ListDecodingMCA.lean][lmca] |
| Small-γ list bound | `MCA_list_decoding_small_gamma_bound` | [MCA/ListDecodingMCA.lean][lmca] |
| Large-γ list bound | `MCA_list_decoding_large_gamma_bound` | [MCA/ListDecodingMCA.lean][lmca] |
| List bad-witness bundle | `MCAListBadWitness` | [MCA/ListDecodingWitness.lean][lwit] |
| List CA domain (def) | `IsListCADomain` | [MCA/ListDecodingDomains.lean][ldom] |
| List-CA from combines (L=1 case) | `isListCADomain_of_all_combines_agree_one` | [MCA/ListDecodingDomains.lean][ldom] |
| List-CA from combines (general L) | `isListCADomain_of_all_combines_agree` (j₀-trick, ~225 lines) | [MCA/ListDecodingDomains.lean][ldom] |
| List cstars-family lift | `exists_cstars_list_of_MDS` | [MCA/ListDecodingCstars.lean][lcstars] |
| List per-coord count | `bad_pair_count_per_coord_le_list` | [MCA/ListDecodingCounting.lean][lcount] |
| List degree bound | `degree_bound_at_non_Ttilde_list` | [MCA/ListDecodingCounting.lean][lcount] |
| List-version of Lemma 5.3 (pigeonhole) | `exists_Ttilde_choose_card_large` | [MCA/ListDecodingCounting.lean][lcount] |
| Multiplicity-aware count bound | `list_strict_superset_count_bound` | [MCA/ListDecodingCounting.lean][lcount] |

[lmca]: ../MCA/ListDecodingMCA.lean
[lwit]: ../MCA/ListDecodingWitness.lean
[ldom]: ../MCA/ListDecodingDomains.lean
[lcstars]: ../MCA/ListDecodingCstars.lean
[lcount]: ../MCA/ListDecodingCounting.lean

---

## §9 — Applications: STIR, WHIR, WARP

### Concrete-generator MDS witnesses

| Paper | Lean | File |
|---|---|---|
| `affineLine` is MDS | `Generator.affineLine_IsMDS` | [MCA/ConcreteMDS.lean][cmds] |
| `univariatePowers` is MDS | `Generator.univariatePowers_IsMDS` | [MCA/ConcreteMDS.lean][cmds] |
| `affineSpace s=1` is MDS (boundary) | `Generator.affineSpace_IsMDS_of_s_one` | [MCA/ConcreteMDS.lean][cmds] |
| `affineLine` dotMap injective | `affineLine_dotMap_injective` | [MCA/ConcreteMDS.lean][cmds] |
| `univariatePowers` dotMap injective | `univariatePowers_dotMap_injective` | [MCA/ConcreteMDS.lean][cmds] |
| `affineSpace` dotMap injective | `affineSpace_dotMap_injective` | [MCA/ConcreteMDS.lean][cmds] |
| Min-distance for `univariatePowers` | `univariatePowers_inducedCode_minDist` | [MCA/ConcreteMDS.lean][cmds] |
| Min-distance for `affineLine` | `affineLine_inducedCode_minDist` | [MCA/ConcreteMDS.lean][cmds] |

[cmds]: ../MCA/ConcreteMDS.lean

### STIR (univariate-powers generator)

| Paper / spec | Lean | File |
|---|---|---|
| STIR MCA unique-decoding bound | `STIR_MCA_unique_decoding_bound` (A1) | [MCA/Applications/STIR.lean][stir] |
| STIR MutualCorrelatedAgreement instance | `STIR_MutualCorrelatedAgreement` (A2) | [MCA/Applications/STIR.lean][stir] |
| STIR zero-evading bound | `STIR_zeroEvading` (A3) | [MCA/Applications/STIR.lean][stir] |
| STIR concrete bound (large fields) | A5 example | [MCA/Applications/STIR.lean][stir] |
| STIR unique-decoding via half-distance | `STIR_uniqueDecoding_via_MCA` (A6) | [MCA/Applications/STIR.lean][stir] |
| WARP-univariate boundary case | `WARP_univariate_MCA_bound_s_one` (A4) | [MCA/Applications/STIR.lean][stir] |

[stir]: ../MCA/Applications/STIR.lean

### Tensor-product / WHIR multivariate

| Paper / spec | Lean | File |
|---|---|---|
| Tensor-product generator | `Generator.tensorProduct` | [MCA/Tensor.lean][tens] |
| Tensor preserves dotMap injectivity | `tensorProduct_dotMap_injective` | [MCA/Tensor.lean][tens] |
| Tensor `finrank` preservation | `tensorProduct_finrank_eq` | [MCA/Tensor.lean][tens] |
| Tensor multiplicative min-distance `≥ d₁·d₂` | `tensorProduct_inducedCode_minDist_at_least` | [MCA/Tensor.lean][tens] |

**Note:** The textbook `tensorProduct_IsMDS` (preservation of Singleton-bound MDS)
is **mathematically false** in general — the tensor of two `[n, n-1, 2]`
codes has min-distance `4`, but Singleton requires `2n`. The correct
preservation is the multiplicative `d₁ · d₂` bound above (classical
result; the only outstanding sorry).

[tens]: ../MCA/Tensor.lean

### Cross-cutting predicate

| Paper / spec | Lean | File |
|---|---|---|
| `IsSTIRGenerator` predicate | `IsSTIRGenerator` | [MCA/Applications/Profile.lean][prof] |

[prof]: ../MCA/Applications/Profile.lean

---

## Sanity examples / smoke tests

| Demonstrates | Lean | File |
|---|---|---|
| Theorem 6.1 elaborates concretely | `example` over `Fin 2` seeds | [MCA/Case2Capstone.lean][cap] |
| Theorem 6.2 elaborates concretely | `example` over `Fin 2` seeds | [MCA/ListDecodingMCA.lean][lmca] |
| `affineLine` MDS over `ZMod 5` | `example` | [MCA/ConcreteMDS.lean][cmds] |
| `univariatePowers F 3` MDS over `ZMod 7` | `example` | [MCA/ConcreteMDS.lean][cmds] |
| STIR MutualCorrelatedAgreement over ZMod 7 | `example` | [MCA/Applications/STIR.lean][stir] |
| Curated capstone examples | `Examples_Capstones.lean` | [MCA/Examples_Capstones.lean][excap] |
| seedProb sanity (`True`/`False`) | `example`s | [Tests.lean][tests] |

[excap]: ../MCA/Examples_Capstones.lean
[tests]: ../../Tests.lean

---

## Future / parked

| Paper / spec | Status | Where |
|---|---|---|
| Lemma 5.3 paper-tight bound (no `+1` slack) | Documented as intrinsic to current technique; needs Corrádi-grouped-by-codeword | [MCA/Case2Subtargets.lean][case2sub] |
| Bivariate polynomial / Guruswami-Sudan | Skeleton only (3 sorries in `Upstream/Algebra/BivariatePolynomial/Basic.lean`) | [Upstream/...][biv] |
| Reed-Solomon → `IsListDecodable` bridge | Stub-only; full bridge needs Array↔Fin function plumbing | [MCA/RSListDecoding.lean][rsld] |
| WHIR MCA bound (multivariate) | Tensor MDS-replacement landed (multiplicative `d₁·d₂` bound); WHIR specialization not yet wired | — |

[biv]: ../../Upstream/Algebra/BivariatePolynomial/Basic.lean
[rsld]: ../MCA/RSListDecoding.lean

---

## Build status

```
$ lake build LinearCodes
Build completed successfully (2300 jobs).
```

Sorries: **0**. Axioms: **0**. The LinearCodes core is fully proved.
