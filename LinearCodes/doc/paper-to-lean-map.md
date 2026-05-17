# BCGM25 Paper → Lean formalization map

A theorem-by-theorem map of which results from
[BCGM25 — *All Polynomial Generators Preserve Distance with Mutual
Correlated Agreement*][bcgm25] (eprint 2025/2051) are formalized in this
project, and where they live.

[bcgm25]: https://eprint.iacr.org/2025/2051

**Status:** build clean, **0 sorries**, **0 axioms**. All capstone theorems
proved end-to-end at the **integer-tight** lossless bound of the literature
(BCH+25 eprint 2025/2055 Theorem 4.1, with matching adversarial saturation
in Remark 2.5). What was previously logged as a `+1` slack vs BCGM25's
informal `n·γ·(ℓ-1)` is in fact the integer-honest form of the same bound
for the Lean shape of `B_set := {x : Δ_x ≤ nγ}`; a concrete counterexample
in [`LinearCodes/MCA/Lemma53Examples.lean`](../MCA/Lemma53Examples.lean)
witnesses that the real-number form is genuinely insufficient for that
shape. Full details: [`literature-survey-lemma-5-3.md`](literature-survey-lemma-5-3.md)
and [`lemma-5-3-numerical-analysis.md`](lemma-5-3-numerical-analysis.md).

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

For the column-difference structure, `|T̃| ≥ n(1-γ)` follows from a
zero-evading aggregate. Our formalization is **integer-tight relative to
the published lossless bound**: BCH+25 (eprint 2025/2055) Theorem 4.1
gives `|S| > M·(γn+1)` (with `M = ℓ-1`), matching our hypothesis
`b > (nγ+1)(ℓ-1)` exactly; BCH+25 Remark 2.5 proves this is tight via an
explicit adversarial saturation. BCGM25's stated `b > nγ(ℓ-1)` is the
real-number form, sufficient only for the strict bad-seed shape
`A_strict := {x : Δ_x = 0}` — for our Lean shape `B_set := {x : Δ_x ≤ nγ}`
(produced by the Case 2 reduction) the real-number bound is genuinely
INSUFFICIENT, witnessed by a concrete `n = 5, ℓ = 2, γ = 0.4`
counterexample in [`MCA/Lemma53Examples.lean`](../MCA/Lemma53Examples.lean).

The conclusion `|T̃| ≥ n(1-γ)` is paper-tight (no `−1` slack) via
per-seed integer rounding (`Nat.ceil`).

| Paper | Lean | Notes |
|---|---|---|
| Lemma 5.3 (specialized to MDS) | `Ttilde_card_gt_of_MDS_aggregate` | [MCA/Case2Subtargets.lean][case2sub] — paper-tight at the integer-honest BCH+25 bound |
| Companion (agreement-set form) | `Ttilde_card_gt_of_MDS_aggregate_via_A` | [MCA/Case2Subtargets.lean][case2sub] |
| Counterexample for the real-number form | (`#eval`) | [MCA/Lemma53Examples.lean](../MCA/Lemma53Examples.lean) |
| Literature survey | — | [doc/literature-survey-lemma-5-3.md](literature-survey-lemma-5-3.md) |
| Numerical analysis | — | [doc/lemma-5-3-numerical-analysis.md](lemma-5-3-numerical-analysis.md) |
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
`(max(n·γ, 1) + 1) · (ℓ - 1) / |S|`, the integer-honest form of BCGM25's
real-number `max(n·γ, 1) · (ℓ - 1) / |S|`. They coincide whenever
`n·γ ∈ ℤ`; in general the integer-tight form is the one we prove and
matches BCH+25 (eprint 2025/2055) Theorem 4.1, which is published-tight
via Remark 2.5. The conclusion `|T̃| ≥ n(1-γ)` is paper-tight via
per-seed `Nat.ceil` integer rounding. See
[`literature-survey-lemma-5-3.md`](literature-survey-lemma-5-3.md) and
[`lemma-5-3-numerical-analysis.md`](lemma-5-3-numerical-analysis.md) for
the full audit, and the docstring of `Ttilde_card_gt_of_MDS_aggregate`
in [Case2Subtargets.lean][case2sub] for the in-file analysis.

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
| Specialization to `L = 1` (unique-decoding shape) | `MCA_list_decoding_bound_L_one` | [MCA/ListDecodingMCA.lean][lmca] |
| `L = 1` ↔ `MCA_unique_decoding_bound` equivalence | `MCA_list_decoding_bound_L_one_eq_unique`, `MCA_unique_decoding_bound_of_list_one` | [MCA/ListDecodingMCA.lean][lmca] |
| Asymptotic-friendly `B / |S|` form | `MCA_list_decoding_bound_div` | [MCA/ListDecodingMCA.lean][lmca] |
| Seed-prob ≤ Johnson list-size / |S| | `seedProb_le_JohnsonListSize_ncard_div` | [MCA/ListDecodingMCA.lean][lmca] |
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
preservation is the multiplicative `d₁ · d₂` bound above
(`tensorProduct_inducedCode_minDist_at_least`, fully proved). The
provably-false `tensorProduct_IsMDS` statement has been deleted entirely
rather than sorried.

[tens]: ../MCA/Tensor.lean

### Cross-cutting predicate

| Paper / spec | Lean | File |
|---|---|---|
| `IsSTIRGenerator` predicate | `IsSTIRGenerator` | [MCA/Applications/Profile.lean][prof] |

[prof]: ../MCA/Applications/Profile.lean

---

## §9.x — GS-sharpened RS bridge (Guruswami-Sudan track)

This is the bridge between the Array-flavoured Reed-Solomon
infrastructure (`ReedSolomon.lean`, `ReedSolomonProperties.lean`) and
the abstract `Submodule F (Fin n → F)`-flavoured MCA framework
(`MCA/`). It allows the Johnson list-size bound proved abstractly in
`MCA/JohnsonBound.lean` (the `(ℓ+1)·n²` Cauchy-Schwarz form) to flow
back into RS-specific case-(a) MCA results.

### Submodule reformulation of RS

| Paper concept | Lean | File |
|---|---|---|
| Encoder as `LinearMap` | `reedSolomonLinearMap` | [MCA/RSListDecoding.lean][rsld] |
| RS code as submodule | `reedSolomonSubmodule` | [MCA/RSListDecoding.lean][rsld] |
| RS submodule is MDS | `reedSolomonSubmodule_isMDS` | [MCA/RSListDecoding.lean][rsld] |
| RS submodule Johnson list-decoding | `reedSolomonSubmodule_isListDecodable_johnson` | [MCA/RSListDecoding.lean][rsld] |
| Array → Fin function lift | `arrayToFun` | [MCA/RSListDecoding.lean][rsld] |
| Array RS encoder ≡ submodule encoder | `reedSolomonEncode_eq_linearMap` | [MCA/RSListDecoding.lean][rsld] |
| Array codeword in submodule | `arrayEncoded_mem_reedSolomonSubmodule` | [MCA/RSListDecoding.lean][rsld] |

### RS combination generator (Phase 1)

| Paper concept | Lean | File |
|---|---|---|
| RS combination generator `(1, α, …, αˡ)` | `rsGenerator F l` (alias of `Generator.univariatePowers`) | [MCA/RSListDecoding.lean][rsld] |
| Coordinate evaluation | `rsGenerator_apply` | [MCA/RSListDecoding.lean][rsld] |
| RS generator is MDS | `rsGenerator_IsMDS` | [MCA/RSListDecoding.lean][rsld] |
| `combine` ↔ `linComb` (function form) | `combine_eq_linComb_funForm` | [MCA/RSListDecoding.lean][rsld] |
| `linComb arrayToFun` ↔ `combine` | `linComb_arrayToFun_eq_combine` | [MCA/RSListDecoding.lean][rsld] |

### Submodule reformulation of `mcaGoodScalar` (Phase 2)

| Paper concept | Lean | File |
|---|---|---|
| Array-form ↔ submodule-form `mcaGoodScalar` | `mcaGoodScalar_iff_submodule_close` | [MCA/RSListDecoding.lean][rsld] |
| Universal case-A ⇒ MCA bad event (combine form) | `caseA_implies_bad_event_universal` | [MCA/RSListDecoding.lean][rsld] |
| Universal case-A ⇒ MCA bad event (linComb form) | `caseA_implies_bad_event_universal_linComb` | [MCA/RSListDecoding.lean][rsld] |
| Hamming-distance reflection through `arrayToFun` | `hammingDist_eq_hammingDistance_arrayToFun` | [MCA/RSListDecoding.lean][rsld] |

### RS-specialized list-decoding MCA bound (Phase 3)

| Paper concept | Lean | File |
|---|---|---|
| RS list-decoding MCA bound | `rs_MCA_list_decoding_bound` | [MCA/RSListDecoding.lean][rsld] |
| Existence of a good seed | `rs_some_alpha_evades_bad_event` | [MCA/RSListDecoding.lean][rsld] |
| Field-size ⇒ ∃ α witness (ℚ form) | `field_size_implies_some_alpha_witness` | [MCA/RSListDecoding.lean][rsld] |
| Field-size ⇒ ∃ α witness (ℕ form) | `field_size_implies_some_alpha_witness_nat` | [MCA/RSListDecoding.lean][rsld] |
| `seedProb < 1` ↔ ∃ α evading | `seedProb_lt_one_iff_exists_not` | [MCA/RSListDecoding.lean][rsld] |
| `n*(1−γ) = n−δ` arithmetic | `n_one_minus_gamma_eq_n_sub_delta` | [MCA/RSListDecoding.lean][rsld] |
| Johnson `τ` ⇒ `k ≤ n` | `rs_messageLength_le_codeLength_of_johnson` | [MCA/RSListDecoding.lean][rsld] |
| Johnson `δ ≤ n` arithmetic | `rs_delta_le_codeLength` | [MCA/RSListDecoding.lean][rsld] |
| Johnson γ-threshold derivation | `gamma_johnson_implies_hi`, `rs_gamma_to_agreement_size` | [MCA/RSListDecoding.lean][rsld] |

### Case-(a) RS-MCA (Phase 4 — landed)

| Paper concept | Lean | Status |
|---|---|---|
| Case-(a) RS-MCA at the `(ℓ+1)·n²` Johnson field-size threshold | `rs_MCA_caseA` | **Landed** — proved end-to-end in [`MCA/RSListDecoding.lean`][rsld] via the abstract Cauchy-Schwarz Johnson bound |

`rs_MCA_caseA` matches the field-size threshold of BCGM25 Theorem 9.2 /
BCIKS18 Theorem 1.2. New callers should use `rs_MCA_caseA` directly.

[rsprops]: ../ReedSolomonProperties.lean

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
[tests]: ../Tests.lean

---

## Future / parked

| Paper / spec | Status | Where |
|---|---|---|
| WHIR MCA bound (multivariate) | Tensor MDS-replacement landed (multiplicative `d₁·d₂` bound); WHIR specialization not yet wired | — |

The Reed-Solomon → `IsListDecodable` bridge (formerly parked here) has
fully landed across Phases 1–4 in
[`MCA/RSListDecoding.lean`][rsld]; the complete API is documented in the
"§9.x — GS-sharpened RS bridge (Guruswami-Sudan track)" section above.

[rsld]: ../MCA/RSListDecoding.lean

---

## Build status

```
$ lake build LinearCodes
Build completed successfully (2300 jobs).
```

Sorries: **0**. Axioms: **0**. The LinearCodes core is fully proved.
