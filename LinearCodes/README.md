# LinearCodes

A Lean 4 library for **linear codes** and the **BCGM25 mutual
correlated-agreement (MCA) framework**, including a runnable
Reed-Solomon encoder and machine-checked security bounds for the
IOP-based SNARK family (FRI, STIR, WHIR, WARP).

```lean
import LinearCodes
```

A three-snippet tour (encode a message, read security bounds, plug into
a STIR profiler) lives at [`doc/getting-started.md`](doc/getting-started.md).

## What's in the box

- **`LinearCode` typeclass** ([`LinearCode.lean`](LinearCode.lean)) —
  `encode`, `messageLen`, `codeLen`, `minimumDistance`, `johnsonRadius`,
  `mcaProximityGapError` (gated by a `ProximityRegime`: `.proven` or
  `.conjectured`). Every instance must discharge a typeclass-level
  `mcaProximityGapError_in_unit_interval` obligation — instances
  cannot return garbage.
- **Reed-Solomon code** ([`ReedSolomon.lean`](ReedSolomon.lean)) —
  Horner-loop encoder, fully computable, no `FftField` requirement.
  Seven formal properties proved in
  [`ReedSolomonProperties.lean`](ReedSolomonProperties.lean):
  `encode_size`, `encode_add`, `encode_smul`, `encode_min_distance`,
  `encode_injective`, `johnson_list_decoding_radius`, plus the keystone
  bridge to `Polynomial.eval`.
- **BCGM25 MCA framework** ([`MCA/`](MCA/)) — Theorems 6.1 (unique
  decoding), 6.2 (list decoding), and 9.2 (Reed-Solomon, Johnson
  regime) proved end-to-end at the integer-tight BCH+25 bound.
- **GS-sharpened RS bridge** ([`MCA/RS/`](MCA/RS/)) — `Array F` ↔
  `Submodule F (Fin n → F)` plumbing, squared-Johnson list-decoding
  certificate, and the canonical case-(a) MCA theorem `rs_MCA_caseA`
  matching BCIKS18 Thm 1.2 / BCGM25 Thm 9.2.
- **STIR / WHIR / WARP application bridges** in
  [`MCA/Applications/`](MCA/Applications/).

## BCGM25 Mutual Correlated Agreement

The [`MCA/`](MCA/) tree formalizes the linear-code mutual correlated
agreement (MCA) framework of Bordage, Chiesa, Guan, and Manzur (2025),
*Correlated agreement, revisited*, IACR ePrint
[2025/2051](https://eprint.iacr.org/2025/2051). BCGM25 unifies the
correlated-agreement (CA) and mutual-correlated-agreement (MCA) bounds
used by modern IOP-based SNARKs by reducing them to a single
generator-level seed-probability bound, parameterized by a relaxation
parameter `γ` and the minimum distance `δ_C` of the underlying linear
code.

### Status

- **Core BCGM25 + RS bridge:** build clean, **0 `sorry`**, **0 axioms**
  across `LinearCodes/` and `Upstream/`, enforced by CI. All Phase A
  (Theorem 6.1) and Phase B (Theorem 6.2) capstones are proved
  end-to-end, and the GS-sharpened Reed-Solomon bridge has landed.
- **Theorem map:** see
  [`doc/paper-to-lean-map.md`](doc/paper-to-lean-map.md) for the full
  paper-to-Lean correspondence.

### Capstones

- **Phase A — unique-decoding regime (Theorem 6.1)**:
  [`MCA/Case2Capstone.lean`](MCA/Case2Capstone.lean) →
  `MCA_unique_decoding_bound`. Bounds the seed probability of the MCA
  bad event by `(max{n·γ, 1} + 1)·(ℓ−1) / |S|` for any generator over
  a code with `MinDistAtLeast c δ_C` and `γ·(ℓ+1) < δ_C / n`. This is
  the **integer-tight** lossless bound of BCH+25 (eprint 2025/2055)
  Theorem 4.1, which Remark 2.5 proves matches an explicit adversarial
  saturation; BCGM25's stated `max{n·γ, 1}·(ℓ−1) / |S|` is the
  real-number form (sufficient only for the strict bad-seed shape
  `Δ_x = 0`, not the Lean shape `Δ_x ≤ nγ`). See
  [`doc/literature-survey-lemma-5-3.md`](doc/literature-survey-lemma-5-3.md)
  and the concrete counterexample
  [`MCA/Lemma53Examples.lean`](MCA/Lemma53Examples.lean).
- **Phase B — list-decoding regime (Theorem 6.2)**:
  [`MCA/ListDecoding/MCA.lean`](MCA/ListDecoding/MCA.lean) →
  `MCA_list_decoding_bound`. Strengthens the bound to
  `L · (max{n·γ, 1} + 1)·(ℓ−1) / |S|`, where each bad seed may admit
  up to `L` candidate codewords agreeing on the witness set.
- **Concrete application — STIR**:
  [`MCA/Applications/STIR.lean`](MCA/Applications/STIR.lean) →
  `STIR_MCA_unique_decoding_bound`, `STIR_MutualCorrelatedAgreement`,
  `STIR_zeroEvading`. Specializes the abstract MCA capstones to the
  univariate-powers generator `G(x) = (1, x, x², …, xᵈ)` used by STIR.

### GS-sharpened Reed-Solomon bridge

[`MCA/RS/`](MCA/RS/) is the bridge from the `Array F`-shaped
Reed-Solomon implementation to the abstract `Submodule F (Fin n → F)`
view used throughout the MCA capstones. It packages:

- A function-form RS encoder (`reedSolomonLinearMap`,
  `reedSolomonSubmodule`) with min-distance, injectivity, dimension,
  and `IsMDS` proofs.
- A squared-Johnson list-decodability witness:
  `reedSolomonSubmodule_isListDecodable_johnson` gives `(τ, n²)`-list-
  decodability whenever `(n − τ)² > n · k`.
- The case-(a) combination generator `rsGenerator F l = (1, α, α², …, αˡ)`
  and a `combine ↔ linComb` bridge between the abstract
  `Generator.combine` and the concrete array-form linear combination.

The headline result is the **sharper RS-MCA bound**

```lean
theorem rs_MCA_list_decoding_bound :
  seedProb (fun α => MCA_bad_event α)
    ≤ (n² · (max (n·γ) 1 + 1) · l) / |F|
```

i.e. specializing Theorem 6.2 to RS replaces the abstract list size
`L` with the Johnson list size `n²`. As a consequence, the case-(a)
field-size requirement sharpens from the loose `(ℓ + 1) · 2^n` (used
when bounding `L` by the trivial `2^n`) to `(ℓ + 1) · n²`, which is
the right order for realistic STIR/WHIR/WARP parameter regimes. The
case-(a) RS-MCA theorem under this sharper hypothesis is
`rs_MCA_caseA` in [`MCA/RS/`](MCA/RS/), also discoverable as
`ReedSolomon.MCA.caseA`.

For the full theorem-by-theorem map (including which sub-targets are
landed and which are still in progress for the bridge), see
[`doc/paper-to-lean-map.md`](doc/paper-to-lean-map.md).

## Stability

The LinearCodes tree is in active development. Stability tiers for
downstream consumers:

- **Stable** (safe to depend on; breaking changes will be flagged in
  PRs): the [`LinearCode`](LinearCode.lean) typeclass interface, the
  Reed-Solomon encoder (`reedSolomonEncode`), the seven proved RS
  properties (`encode_size`, `encode_add`, `encode_smul`,
  `encode_min_distance`, `encode_injective`,
  `johnson_list_decoding_radius`, plus the encoder ↔ `Polynomial.eval`
  bridge), and the BCGM25 capstones (`MCA_unique_decoding_bound`,
  `MCA_list_decoding_bound`, `rs_MCA_caseA`,
  `rs_MCA_list_decoding_bound`).
- **Recently landed (may evolve)**: theorem aliases
  (`correlatedAgreement_*`, `reedSolomon_correlatedAgreement_*`,
  `ReedSolomon.MCA.*`); the GS-sharpened RS-MCA bridge
  ([`MCA/RS/`](MCA/RS/)); the `JohnsonListSize` vs
  `JohnsonListSizeWithSlack` split. Public names are unlikely to
  change but exact theorem locations may move as the tree gets
  reorganised.
- **Research / not for downstream use**: [`Research/`](Research/)
  (capstone smoke-test scratch); the `.conjectured` branch of
  `mcaProximityGapError` (a capacity-regime placeholder, **not**
  machine-checked, gated on the open capacity-achieving proximity-gap
  conjecture); `Generator.affineSpace` general `s ≥ 2` MDS proofs
  (the structural special cases for `s ∈ {0, 1}` and `s = 2 ∧ |F| = 2`
  are landed; the general case is mathematically false in the current
  parameterisation — see [`MCA/ConcreteMDS.lean`](MCA/ConcreteMDS.lean)
  for discussion).

## Module structure

- *Foundations*:
  [`MCA/Definitions.lean`](MCA/Definitions.lean) (`Generator`,
  `seedProb`, `MutualCorrelatedAgreement`, `ZeroEvading`),
  [`MCA/Properties.lean`](MCA/Properties.lean) (basic lemmas),
  [`MCA/SeedProbLemmas.lean`](MCA/SeedProbLemmas.lean) (probability
  bounds over uniform seed types).
- *MDS infrastructure*:
  [`MCA/UniqueDecoding.lean`](MCA/UniqueDecoding.lean),
  [`MCA/Generators.lean`](MCA/Generators.lean) (Vandermonde and
  univariate-powers generators),
  [`MCA/ConcreteMDS.lean`](MCA/ConcreteMDS.lean) (concrete MDS
  certificates).
- *Lemma 5.3 sub-targets*: [`MCA/Case2/`](MCA/Case2/) — the
  ℚ-double-counting argument bounding the size of the maximal
  agreement domain `T̃`.
- *Capstones*:
  [`MCA/Case2Capstone.lean`](MCA/Case2Capstone.lean) (Theorem 6.1),
  [`MCA/ListDecoding/MCA.lean`](MCA/ListDecoding/MCA.lean)
  (Theorem 6.2 list-decoding regime), supported by
  [`MCA/ListDecoding/Witness.lean`](MCA/ListDecoding/Witness.lean),
  [`MCA/ListDecoding/Domains.lean`](MCA/ListDecoding/Domains.lean),
  [`MCA/ListDecoding/Counting.lean`](MCA/ListDecoding/Counting.lean),
  and [`MCA/JohnsonBound.lean`](MCA/JohnsonBound.lean).
- *Reed-Solomon bridge*: [`MCA/RS/`](MCA/RS/) — bridge from
  `Array F`-form RS codewords to `Submodule F (Fin n → F)`,
  squared-Johnson list-decodability, and the
  `rs_MCA_list_decoding_bound` specialization of Theorem 6.2.
- *Applications*:
  [`MCA/Applications/STIR.lean`](MCA/Applications/STIR.lean),
  [`MCA/Applications/Profile.lean`](MCA/Applications/Profile.lean)
  (cross-cutting predicates for STIR / WHIR-univariate / WARP).
- *Onboarding / tests*:
  [`Examples/RSSmokeTest.lean`](Examples/RSSmokeTest.lean) — hand-
  computed encoding and security-bound checks (excluded from the
  public umbrella; built as a separate lake target so CI catches
  encoder regressions).

## Docs

- [`doc/getting-started.md`](doc/getting-started.md) — three runnable
  snippets (encode, security bounds, STIR profiler hooks).
- [`doc/paper-to-lean-map.md`](doc/paper-to-lean-map.md) —
  theorem-by-theorem map from BCGM25 (ePrint 2025/2051) to the Lean
  codebase.
- [`doc/literature-survey-lemma-5-3.md`](doc/literature-survey-lemma-5-3.md),
  [`doc/lemma-5-3-numerical-analysis.md`](doc/lemma-5-3-numerical-analysis.md),
  [`doc/lemma-5-3-paper-technique.md`](doc/lemma-5-3-paper-technique.md)
  — Lemma 5.3 deep-dive (integer-tight vs real-number forms).
