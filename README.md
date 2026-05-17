# sumcheck-lean4

A Lean 4 monorepo with two formalised sub-projects: the **sumcheck
protocol** and the **BCGM25 mutual-correlated-agreement (MCA)
framework** for linear codes (with a runnable Reed-Solomon encoder
backing it).

## What you import

```lean
import Sumcheck     -- the sumcheck protocol
import LinearCodes  -- LinearCode typeclass, Reed-Solomon, BCGM25 MCA framework
```

## The two sub-trees

### [`Sumcheck/`](Sumcheck/) — sumcheck protocol

Machine-checked completeness and soundness for the canonical
sumcheck protocol on multivariate polynomials, built on
[`CMvPolynomial`](https://github.com/Verified-zkEVM/CompPoly).
Fully-computable transcript generation; inner-product sumcheck
specialisation with a multilinear soundness-error bound of
`n · 2 / |𝔽|`. **See [`Sumcheck/README.md`](Sumcheck/README.md).**

### [`LinearCodes/`](LinearCodes/) — linear codes + MCA framework

A `LinearCode` typeclass, a runnable Reed-Solomon encoder with seven
proved properties (length, additivity, scalar-multiplicativity,
Singleton-MDS distance, injectivity, Johnson list-decoding radius,
encoder↔`Polynomial.eval` bridge), and the BCGM25 MCA capstones
(Theorems 6.1, 6.2, 9.2) proved end-to-end at the integer-tight
BCH+25 bound. **0 `sorry`**, **0 axioms**, enforced by CI. **See
[`LinearCodes/README.md`](LinearCodes/README.md).** Quick tour for
new users: [`LinearCodes/doc/getting-started.md`](LinearCodes/doc/getting-started.md).

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
