import SumcheckProtocol.Src.RoundEvaluator
import SumcheckProtocol.IP.EvalForm

/-!
# CoefficientProver bridge: `RoundPolyEvaluator` → `SumcheckProtocolStatementEvalForm`

A thin plumbing layer that lets a caller package a
`RoundPolyEvaluator 𝔽 n d` together with the remaining eval-form
statement data (domain, claim, evaluation nodes) into a fully-formed
`SumcheckProtocolStatementEvalForm 𝔽 n d`. The degree bound transfers from the
evaluator's `virtualPolynomial_degree_le` field directly.

This is the structural equivalent of effsc's `CoefficientProver` ←
`RoundPolyEvaluator` composition: the user supplies the per-pair
contribution (i.e. the virtual polynomial) once, and the library hands
back a statement bundle the IP framework's `Prover` can consume.

The companion correctness theorem (that the eval-form honest prover on
the bridged statement produces the same per-round messages as direct
hypercube evaluation of the evaluator's virtual polynomial) is left for
a follow-up: it is a corollary of the existing
`honestProverMessageEvalsAt` definition modulo the simp lemmas below.
-/

open CPoly

namespace RoundPolyEvaluator

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/--
Plumb a `RoundPolyEvaluator` into a `SumcheckProtocolStatementEvalForm`. The
evaluator's polynomial becomes the statement polynomial and its degree
bound discharges the statement's `degree_le` field. -/
def toEvalFormStatement {n d : ℕ}
    (E : RoundPolyEvaluator 𝔽 n d)
    (domain : List 𝔽) (claim : 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (evalPoints_inj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x) :
    SumcheckProtocolStatementEvalForm 𝔽 n d where
  domain := domain
  claim := claim
  polynomial := E.virtualPolynomial
  evalPoints := evalPoints
  evalPoints_inj := evalPoints_inj
  domain_sub := domain_sub
  degree_le := E.virtualPolynomial_degree_le

@[simp] lemma toEvalFormStatement_polynomial {n d : ℕ}
    (E : RoundPolyEvaluator 𝔽 n d)
    (domain : List 𝔽) (claim : 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (evalPoints_inj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x) :
    (toEvalFormStatement E domain claim evalPoints
        evalPoints_inj domain_sub).polynomial
      = E.virtualPolynomial := rfl

@[simp] lemma toEvalFormStatement_domain {n d : ℕ}
    (E : RoundPolyEvaluator 𝔽 n d)
    (domain : List 𝔽) (claim : 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (evalPoints_inj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x) :
    (toEvalFormStatement E domain claim evalPoints
        evalPoints_inj domain_sub).domain
      = domain := rfl

@[simp] lemma toEvalFormStatement_claim {n d : ℕ}
    (E : RoundPolyEvaluator 𝔽 n d)
    (domain : List 𝔽) (claim : 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (evalPoints_inj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x) :
    (toEvalFormStatement E domain claim evalPoints
        evalPoints_inj domain_sub).claim
      = claim := rfl

@[simp] lemma toEvalFormStatement_evalPoints {n d : ℕ}
    (E : RoundPolyEvaluator 𝔽 n d)
    (domain : List 𝔽) (claim : 𝔽)
    (evalPoints : Fin (d + 1) → 𝔽)
    (evalPoints_inj : Function.Injective evalPoints)
    (domain_sub : ∀ x ∈ domain, ∃ k, evalPoints k = x) :
    (toEvalFormStatement E domain claim evalPoints
        evalPoints_inj domain_sub).evalPoints
      = evalPoints := rfl

end RoundPolyEvaluator
