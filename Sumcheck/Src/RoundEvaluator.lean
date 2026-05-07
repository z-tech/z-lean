import Sumcheck.Src.CMvPolynomial
import Sumcheck.IP.SharpSAT.Degree

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

/-! ## Concrete instances

Two evaluator constructions used elsewhere in the codebase:

* `multilinearEvaluator p hp` — `d = 1` evaluator backed by an explicit
  multilinearity hypothesis. Used by Phase 2's multilinear sumcheck.
* `innerProductEvaluator f g hf hg` — `d = 2` evaluator backed by the
  symbolic product `f * g` of two multilinears. The degree bound is
  closed by `degreeOf_mul_le_c` from `Sumcheck/IP/SharpSAT/Degree.lean`,
  threaded through `Nat.add_le_add hf hg`. Mirrors the Phase 5(a)
  `InnerProduct.NativeStatement.toEvalFormStatement` bridge but
  packaged as a generic `RoundPolyEvaluator`.

Higher-arity instances (e.g. arithmetised 3-CNF, GKR layers) follow the
same pattern: provide a polynomial and a per-variable degree bound.
-/

/--
Multilinear evaluator: `d = 1`. Direct from a polynomial `p` together
with the per-variable degree bound `hp`. -/
def multilinearEvaluator {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (p : CMvPolynomial n 𝔽)
    (hp : ∀ i : Fin n, indDegreeK p i ≤ 1) :
    RoundPolyEvaluator 𝔽 n 1 where
  virtualPolynomial := p
  virtualPolynomial_degree_le := hp

@[simp] lemma multilinearEvaluator_virtualPolynomial
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (p : CMvPolynomial n 𝔽) (hp : ∀ i : Fin n, indDegreeK p i ≤ 1) :
    (multilinearEvaluator p hp).virtualPolynomial = p := rfl

/--
Inner-product evaluator: `d = 2`. Built from two multilinears `f, g`
together with their per-variable degree bounds; the virtual polynomial
is the symbolic product `f * g`. The degree bound chains
`SharpSAT.degreeOf_mul_le_c` (`(f*g).degreeOf i ≤ f.degreeOf i + g.degreeOf i`)
with `Nat.add_le_add hf hg` to land at `≤ 1 + 1 = 2`.

Mirrors the Phase 5(a) `InnerProduct.NativeStatement.toEvalFormStatement`
construction. The `[BEq 𝔽] [LawfulBEq 𝔽]` constraints are inherited from
`SharpSAT.degreeOf_mul_le_c`'s preconditions. -/
def innerProductEvaluator
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}
    (f g : CMvPolynomial n 𝔽)
    (hf : ∀ i : Fin n, indDegreeK f i ≤ 1)
    (hg : ∀ i : Fin n, indDegreeK g i ≤ 1) :
    RoundPolyEvaluator 𝔽 n 2 where
  virtualPolynomial := f * g
  virtualPolynomial_degree_le := by
    intro i
    have hmul : (f * g).degreeOf i ≤ f.degreeOf i + g.degreeOf i :=
      SharpSAT.degreeOf_mul_le_c f g i
    -- `indDegreeK p i = p.degreeOf i` by definition.
    exact le_trans hmul (Nat.add_le_add (hf i) (hg i))

@[simp] lemma innerProductEvaluator_virtualPolynomial
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] {n : ℕ}
    (f g : CMvPolynomial n 𝔽)
    (hf : ∀ i : Fin n, indDegreeK f i ≤ 1)
    (hg : ∀ i : Fin n, indDegreeK g i ≤ 1) :
    (innerProductEvaluator f g hf hg).virtualPolynomial = f * g := rfl

