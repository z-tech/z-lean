# Sumcheck-Lean4

The **Sumcheck protocol** written in [Lean 4](https://lean-lang.org/) using [`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly).

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

## BCGM25 Mutual Correlated Agreement

The [`LinearCodes/MCA/`](LinearCodes/MCA/) tree formalizes the linear-code
*mutual correlated agreement* (MCA) framework of Bordage, Chiesa, Guan, and
Manzur (2025), *Correlated agreement, revisited*, IACR ePrint
[2025/2051](https://eprint.iacr.org/2025/2051). BCGM25 unifies the
correlated-agreement (CA) and mutual-correlated-agreement (MCA) bounds used by
modern IOP-based SNARKs (STIR, WHIR, WARP) by reducing them to a single
generator-level seed-probability bound, parameterized by a relaxation
parameter `γ` and the minimum distance `δ_C` of the underlying linear code.

### Capstones

- **Phase A — unique-decoding regime (Theorem 6.1)**:
  [`LinearCodes/MCA/Case2Capstone.lean`](LinearCodes/MCA/Case2Capstone.lean) →
  `MCA_unique_decoding_bound`. Bounds the seed probability of the MCA bad
  event by `((n·γ + 1)·(ℓ−1)) / |S|` for any generator over a code with
  `MinDistAtLeast c δ_C` and `γ·ℓ < δ_C / n`.
- **Phase B — list-decoding regime (Theorem 6.2)**:
  [`LinearCodes/MCA/ListDecodingMCA.lean`](LinearCodes/MCA/ListDecodingMCA.lean)
  → `MCA_list_decoding_bound`. Strengthens the bound to the list-decoding
  regime, where each bad seed may admit up to `L` candidate codewords
  agreeing on the witness set.
- **Concrete application — STIR**:
  [`LinearCodes/MCA/Applications/STIR.lean`](LinearCodes/MCA/Applications/STIR.lean)
  → `STIR_MCA_unique_decoding_bound`, `STIR_MutualCorrelatedAgreement`,
  `STIR_zeroEvading`. Specializes the abstract MCA capstones to the
  univariate-powers generator `G(x) = (1, x, x^2, …, x^d)` used by STIR.

### Module structure

- *Foundations*:
  [`Definitions.lean`](LinearCodes/MCA/Definitions.lean) (`Generator`,
  `seedProb`, `MutualCorrelatedAgreement`, `ZeroEvading`),
  [`Properties.lean`](LinearCodes/MCA/Properties.lean) (basic lemmas),
  [`SeedProbLemmas.lean`](LinearCodes/MCA/SeedProbLemmas.lean) (probability
  bounds over uniform seed types).
- *MDS infrastructure*:
  [`UniqueDecoding.lean`](LinearCodes/MCA/UniqueDecoding.lean),
  [`Examples.lean`](LinearCodes/MCA/Examples.lean) (Vandermonde and
  univariate-powers generators),
  [`ConcreteMDS.lean`](LinearCodes/MCA/ConcreteMDS.lean) (concrete MDS
  certificates).
- *Lemma 5.3 sub-targets*:
  [`Case2Subtargets.lean`](LinearCodes/MCA/Case2Subtargets.lean) — the
  ℚ-double-counting argument bounding the size of the maximal agreement
  domain `T̃`.
- *Capstones*:
  [`Case2Capstone.lean`](LinearCodes/MCA/Case2Capstone.lean) (Theorem 6.1),
  [`ListDecodingMCA.lean`](LinearCodes/MCA/ListDecodingMCA.lean)
  (Theorem 6.2 list-decoding regime), supported by
  [`ListDecodingWitness.lean`](LinearCodes/MCA/ListDecodingWitness.lean),
  [`ListDecodingDomains.lean`](LinearCodes/MCA/ListDecodingDomains.lean),
  [`ListDecodingCstars.lean`](LinearCodes/MCA/ListDecodingCstars.lean),
  [`ListDecodingCounting.lean`](LinearCodes/MCA/ListDecodingCounting.lean),
  and [`JohnsonBound.lean`](LinearCodes/MCA/JohnsonBound.lean).
- *Applications*:
  [`Applications/STIR.lean`](LinearCodes/MCA/Applications/STIR.lean),
  [`Applications/Profile.lean`](LinearCodes/MCA/Applications/Profile.lean)
  (cross-cutting predicates for STIR / WHIR-univariate / WARP).

## License

This project is released under the **Apache License 2.0**. See [LICENSE](LICENSE) for details.