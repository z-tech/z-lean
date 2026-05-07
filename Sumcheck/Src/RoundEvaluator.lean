import Sumcheck.Src.CMvPolynomial

/-!
# Arbitrary-degree round-poly evaluator (Phase 5(b))

A typeclass-shaped (but value-level — `structure`, not `class`) evaluator
that mirrors the `RoundPolyEvaluator` trait used by `effsc`'s
`CoefficientProver`. The Rust trait centers on a per-pair callback that
returns the contribution of one hypercube point (or pair) to the round
polynomial; the library handles iteration. Here, the simplest meaningful
shape is *the polynomial-with-degree-bound itself*: an evaluator IS a
multivariate polynomial together with a per-variable individual-degree
bound. The "callback contribution" of the Rust trait is then just
`virtualPolynomial.eval point` and the library's iteration is exactly the
existing `residualSumWithOpenVars` / `honestProverMessageEvalsAt` plumbing.

Richer shapes (e.g. separate `tablewise`/`pairwise` oracle bundles à la
`InnerProduct.NativeStatement`) are deferred: in eval-form land any
finite collection of oracles can be realised as a single virtual polynomial
(the symbolic product/sum) along with the appropriate degree bound, and
the IP framework's `Prover` is statement-keyed by a single
`SumcheckStatementEvalForm`, which itself carries a single `polynomial`.
This file provides the shared evaluator shape; downstream files (such as
`Sumcheck/IP/InnerProductNative.lean`) provide the bridges that let a
*native* prover hot-path avoid materialising the virtual polynomial while
the verifier's view stays on the symbolic side.
-/

open CPoly

/--
A per-round polynomial evaluator: a multivariate polynomial together
with a uniform per-variable individual-degree bound.

The bound `virtualPolynomial_degree_le` is a quantifier over the index
type rather than a single max-degree number because the eval-form
`SumcheckStatementEvalForm.degree_le` field is itself stated per-`Fin n`,
and the bound flows through directly.

`d = 1` is the multilinear case (Phase 2); `d = 2` covers the
inner-product native case (Phase 5(a)). Higher `d` values are used by
e.g. arithmetised 3-CNF (`d = 3·|φ|`).
-/
structure RoundPolyEvaluator
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n d : ℕ) where
  virtualPolynomial : CMvPolynomial n 𝔽
  virtualPolynomial_degree_le :
    ∀ i : Fin n, indDegreeK virtualPolynomial i ≤ d

namespace RoundPolyEvaluator

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/--
Per-point contribution: the value of the virtual polynomial at `point`.
This is the analogue of the Rust trait's per-pair callback. The library's
iteration over the hypercube is performed by
`Sumcheck/Src/EvalForm.lean::honestProverMessageEvalsAt`, which calls
exactly this function on each summand.
-/
@[simp] def evalAt {n d : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (E : RoundPolyEvaluator 𝔽 n d) (point : Fin n → 𝔽) : 𝔽 :=
  CMvPolynomial.eval point E.virtualPolynomial

end RoundPolyEvaluator
