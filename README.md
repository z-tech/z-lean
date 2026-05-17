# Sumcheck-Lean4

The **Sumcheck protocol** written in [Lean 4](https://lean-lang.org/) using [`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly).

## What you import

```lean
import Sumcheck     -- the sumcheck protocol
import LinearCodes  -- LinearCode typeclass, Reed-Solomon, BCGM25 MCA framework
```

For the LinearCodes tree specifically, a tour of common usage patterns
(encoding, security primitives, STIR / WHIR profiler hooks) lives at
[`LinearCodes/doc/getting-started.md`](LinearCodes/doc/getting-started.md).

## Key Features

- **Fully Computable**: Transcript generation is provided given a [`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly), a claim, and challenge set.
- **Formalized Theorems**: Notions of `completeness` and `soundness` are machine-checked.
- **Inner-product sumcheck** ([`Sumcheck/IP/InnerProduct.lean`](Sumcheck/IP/InnerProduct.lean)): `InnerProductStatement` claiming `c = Σ f(x)·g(x)` over a boolean hypercube (or other domain), reduced to sumcheck on `f * g`. Completeness, soundness, and a multilinear soundness-error bound of `n · 2 / |𝔽|`.

## Theorems

### Completeness

> If the prover is honest, the verifier always accepts.

```
theorem perfect_completeness
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) :
  prob_over_challenges
    (fun r => AcceptsEvent p (generate_honest_transcript p (honest_claim p) r))
  = 1
```

Given a multivariate polynomial $p : \mathbb{F}[X_1, \dots, X_n]$ and an honest prover who sets:

$$c_0 = \sum_{b \in \\{0,1\\}^n} p(b)$$

the verifier accepts with probability exactly 1 over all challenge tuples $r \in \mathbb{F}^n$.

### Soundness

> If the claim is false, the verifier accepts with low probability.

```
theorem soundness_dishonest
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (claim : 𝔽)
  (claim_p : CPoly.CMvPolynomial n 𝔽)
  (adv : Adversary 𝔽 n)
  (h : claim ≠ honest_claim (p := claim_p)) :
  prob_over_challenges (E := AcceptsOnChallenges claim claim_p adv)
    ≤ n * (max_ind_degree claim_p) / field_size
```

If a prover claims a value $c \neq \sum_{b \in \\{0,1\\}^n} p(b)$, then for any strategy, the probability the verifier accepts is bounded by:

$$\Pr[\text{accept}] \leq \frac{n \cdot d}{|\mathbb{F}|}$$

where $d = \max_i \deg_{X_i}(p)$ is the max individual degree of $p$. The proof sketch is:

1. **Reduction**: a dishonest claim implies at least one "bad" round where the prover's polynomial $\neq$ honest one.
2. **Union bound**: the acceptance probability is bounded by the sum over rounds.
3. **Schwartz–Zippel**: at each bad round, the probability of the verifier's random challenge hitting a root of the difference polynomial is at most $d / |\mathbb{F}|$ (via Mathlib's `MvPolynomial.schwartz_zippel_sum_degreeOf`).

## Honest Prover

The honest prover message at round $i$ is defined as the **univariate polynomial** in $X_i$ computed by summing out the remaining variables over the Boolean hypercube:

$$g_i(X_i) = \sum_{b \in \\{0,1\\}^{n-i-1}} p(r_1, \dots, r_{i-1}, X_i, b_1, \dots, b_{n-i-1})$$

where $r_1, \dots, r_{i-1}$ are the verifier's previous challenges. This is implemented in [`Src/Prover.lean`](Sumcheck/Src/Prover.lean) as `honest_prover_message_at`, which:

1. Builds a **substitution map** `Fin n → CMvPolynomial 1 𝔽` that replaces the first $i$ variables with constants (the challenges), the $(i{+}1)$-th variable with the indeterminate $X_0$, and the remaining variables with hypercube bits.
2. Evaluates $p$ under this substitution via `eval₂Poly`, producing a univariate polynomial.
3. **Sums** these univariates over all $\\{0,1\\}^{n-i-1}$ assignments using `sum_over_hypercube_recursive`.

## Stability (LinearCodes)

The LinearCodes tree is in active development. Stability tiers for
downstream consumers:

- **Stable** (safe to depend on; breaking changes will be flagged in
  PRs): the [`LinearCode`](LinearCodes/LinearCode.lean) typeclass
  interface, the Reed-Solomon encoder (`reedSolomonEncode`), the seven
  proved RS properties (`encode_size`, `encode_add`, `encode_smul`,
  `encode_min_distance`, `encode_injective`,
  `johnson_list_decoding_radius`, plus the encoder ↔ `Polynomial.eval`
  bridge), and the BCGM25 capstones (`MCA_unique_decoding_bound`,
  `MCA_list_decoding_bound`, `rs_MCA_caseA`,
  `rs_MCA_list_decoding_bound`).
- **Recently landed (may evolve)**: theorem aliases
  (`correlatedAgreement_*`, `reedSolomon_correlatedAgreement_*`); the
  GS-sharpened RS-MCA bridge (`MCA/RS/`); the
  `JohnsonListSize` vs `JohnsonListSizeWithSlack` split. Public names
  are unlikely to change but exact theorem locations may move as the
  tree gets reorganised (P2 work).
- **Research / not for downstream use**:
  [`LinearCodes/Research/`](LinearCodes/Research/) (capstone smoke-test
  scratch); the `.conjectured` branch of `mcaProximityGapError` (a
  capacity-regime placeholder, **not** machine-checked, gated on the
  open capacity-achieving proximity-gap conjecture);
  `Generator.affineSpace` general `s ≥ 2` MDS proofs (the structural
  special cases for `s ∈ {0, 1}` and `s = 2 ∧ |F| = 2` are landed; the
  general case is mathematically false in the current
  parameterisation — see `MCA/ConcreteMDS.lean` for discussion).

## BCGM25 Mutual Correlated Agreement

The [`LinearCodes/MCA/`](LinearCodes/MCA/) tree formalizes the linear-code
*mutual correlated agreement* (MCA) framework of Bordage, Chiesa, Guan, and
Manzur (2025), *Correlated agreement, revisited*, IACR ePrint
[2025/2051](https://eprint.iacr.org/2025/2051). BCGM25 unifies the
correlated-agreement (CA) and mutual-correlated-agreement (MCA) bounds used by
modern IOP-based SNARKs (STIR, WHIR, WARP) by reducing them to a single
generator-level seed-probability bound, parameterized by a relaxation
parameter `γ` and the minimum distance `δ_C` of the underlying linear code.

### Status

- **Core BCGM25 + RS bridge:** build clean, **0 `sorry`**, **0 axioms**
  across `LinearCodes/` and `Upstream/`. All Phase A (Theorem 6.1) and
  Phase B (Theorem 6.2) capstones are proved end-to-end, and the
  GS-sharpened Reed-Solomon bridge has landed.
- **GS-sharpened Reed-Solomon bridge** (landed):
  [`LinearCodes/MCA/RS/`](LinearCodes/MCA/RS/)
  threads the Johnson list-size `n²` through the abstract list-decoding
  capstone, yielding a sharper concrete bound for Reed-Solomon (see below).
- **Theorem map:** see
  [`LinearCodes/doc/paper-to-lean-map.md`](LinearCodes/doc/paper-to-lean-map.md)
  for the full paper-to-Lean correspondence.

### Capstones

- **Phase A — unique-decoding regime (Theorem 6.1)**:
  [`LinearCodes/MCA/Case2Capstone.lean`](LinearCodes/MCA/Case2Capstone.lean) →
  `MCA_unique_decoding_bound`. Bounds the seed probability of the MCA bad
  event by `(max{n·γ, 1} + 1)·(ℓ−1) / |S|` for any generator over a code
  with `MinDistAtLeast c δ_C` and `γ·(ℓ+1) < δ_C / n`. This is the
  **integer-tight** lossless bound of BCH+25 (eprint 2025/2055) Theorem 4.1,
  which Remark 2.5 proves matches an explicit adversarial saturation;
  BCGM25's stated `max{n·γ, 1}·(ℓ−1) / |S|` is the real-number form
  (sufficient only for the strict bad-seed shape `Δ_x = 0`, not the Lean
  shape `Δ_x ≤ nγ`). See
  [`doc/literature-survey-lemma-5-3.md`](LinearCodes/doc/literature-survey-lemma-5-3.md)
  and the concrete counterexample
  [`MCA/Lemma53Examples.lean`](LinearCodes/MCA/Lemma53Examples.lean).
- **Phase B — list-decoding regime (Theorem 6.2)**:
  [`LinearCodes/MCA/ListDecoding/MCA.lean`](LinearCodes/MCA/ListDecoding/MCA.lean)
  → `MCA_list_decoding_bound`. Strengthens the bound to
  `L · (max{n·γ, 1} + 1)·(ℓ−1) / |S|`, where each bad seed may admit up
  to `L` candidate codewords agreeing on the witness set.
- **Concrete application — STIR**:
  [`LinearCodes/MCA/Applications/STIR.lean`](LinearCodes/MCA/Applications/STIR.lean)
  → `STIR_MCA_unique_decoding_bound`, `STIR_MutualCorrelatedAgreement`,
  `STIR_zeroEvading`. Specializes the abstract MCA capstones to the
  univariate-powers generator `G(x) = (1, x, x^2, …, x^d)` used by STIR.

### GS-sharpened Reed-Solomon bridge

[`LinearCodes/MCA/RS/`](LinearCodes/MCA/RS/)
is the new bridge from the `Array F`-shaped Reed-Solomon implementation to
the abstract `Submodule F (Fin n → F)` view used throughout the MCA
capstones. It packages:

- A function-form RS encoder (`reedSolomonLinearMap`, `reedSolomonSubmodule`)
  with min-distance, injectivity, dimension, and `IsMDS` proofs.
- A Guruswami-Sudan / squared-Johnson list-decodability witness:
  `reedSolomonSubmodule_isListDecodable_johnson` gives `(τ, n²)`-list-
  decodability whenever `(n - τ)² > n · k`.
- The case-A combination generator `rsGenerator F l = (1, α, α², …, αˡ)`
  and a `combine ↔ linComb` bridge between the abstract `Generator.combine`
  and the concrete array-form linear combination.

The headline result is the **sharper RS-MCA bound**

```
theorem rs_MCA_list_decoding_bound :
  seedProb (fun α => MCA_bad_event α)
    ≤ (n² · (max (n·γ) 1 + 1) · l) / |F|
```

i.e. specializing Theorem 6.2 to RS replaces the abstract list size `L`
with the Johnson list size `n²`. As a consequence, the case-A field-size
requirement sharpens from the loose `(ℓ + 1) · 2^n` (used when bounding
`L` by the trivial `2^n`) to `(ℓ + 1) · n²`, which is the right order for
realistic STIR/WHIR/WARP parameter regimes. The case-(a) RS-MCA theorem
under this sharper hypothesis is `rs_MCA_caseA` in
[`LinearCodes/MCA/RS/`](LinearCodes/MCA/RS/).

For the full theorem-by-theorem map (including which sub-targets are
landed and which are still in progress for the bridge), see
[`LinearCodes/doc/paper-to-lean-map.md`](LinearCodes/doc/paper-to-lean-map.md).

### Module structure

- *Foundations*:
  [`Definitions.lean`](LinearCodes/MCA/Definitions.lean) (`Generator`,
  `seedProb`, `MutualCorrelatedAgreement`, `ZeroEvading`),
  [`Properties.lean`](LinearCodes/MCA/Properties.lean) (basic lemmas),
  [`SeedProbLemmas.lean`](LinearCodes/MCA/SeedProbLemmas.lean) (probability
  bounds over uniform seed types).
- *MDS infrastructure*:
  [`UniqueDecoding.lean`](LinearCodes/MCA/UniqueDecoding.lean),
  [`Generators.lean`](LinearCodes/MCA/Generators.lean) (Vandermonde and
  univariate-powers generators),
  [`ConcreteMDS.lean`](LinearCodes/MCA/ConcreteMDS.lean) (concrete MDS
  certificates).
- *Lemma 5.3 sub-targets*:
  [`Case2/`](LinearCodes/MCA/Case2/) — the
  ℚ-double-counting argument bounding the size of the maximal agreement
  domain `T̃`.
- *Capstones*:
  [`Case2Capstone.lean`](LinearCodes/MCA/Case2Capstone.lean) (Theorem 6.1),
  [`ListDecoding/MCA.lean`](LinearCodes/MCA/ListDecoding/MCA.lean)
  (Theorem 6.2 list-decoding regime), supported by
  [`ListDecoding/Witness.lean`](LinearCodes/MCA/ListDecoding/Witness.lean),
  [`ListDecoding/Domains.lean`](LinearCodes/MCA/ListDecoding/Domains.lean),
  [`ListDecoding/Counting.lean`](LinearCodes/MCA/ListDecoding/Counting.lean),
  and [`JohnsonBound.lean`](LinearCodes/MCA/JohnsonBound.lean).
- *Reed-Solomon bridge*:
  [`RS/`](LinearCodes/MCA/RS/) — bridge
  from `Array F`-form RS codewords to `Submodule F (Fin n → F)`,
  squared-Johnson list-decodability, and the `rs_MCA_list_decoding_bound`
  specialization of Theorem 6.2.
- *Applications*:
  [`Applications/STIR.lean`](LinearCodes/MCA/Applications/STIR.lean),
  [`Applications/Profile.lean`](LinearCodes/MCA/Applications/Profile.lean)
  (cross-cutting predicates for STIR / WHIR-univariate / WARP).

## License

This project is released under the **Apache License 2.0**. See [LICENSE](LICENSE) for details.