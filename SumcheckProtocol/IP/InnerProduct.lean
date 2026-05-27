import SumcheckProtocol.IP.Statement
import SumcheckProtocol.IP.InteractiveProtocol
import SumcheckProtocol.IP.SharpSAT.Degree

/-!
# Inner-product sumcheck

A thin wrapper over the existing sumcheck protocol specialised to an inner-
product claim:

`claim = Σ_{x ∈ domain^n} f(x) · g(x)`

for two multivariate polynomials `f, g : CMvPolynomial n 𝔽`. Under the hood
this is just sumcheck on the product polynomial `f * g`, so completeness and
soundness follow immediately from the underlying sumcheck theorems. Individual
degrees combine additively: `(f * g).degreeOf i ≤ f.degreeOf i + g.degreeOf i`,
which tightens the soundness bound when both polynomials are multilinear to
`n · 2 / |𝔽|`.

## Scope note

This file materialises `f * g` as a single `CMvPolynomial`. A native
two-oracle protocol (prover maintains `f, g` separately; verifier queries
both at the end) would save prover memory and preserve the structural view
used in GKR — that's planned separately. The thin-wrapper formulation here
is enough to stand up inner-product claims, validate the interface, and
start using them as building blocks.

## Key declarations

* `InnerProductStatement` — bundles `f`, `g`, a domain, and a claim.
* `InnerProductStatement.toSumcheckProtocol` — reduces to a `SumcheckProtocolStatement` on
  `f * g`.
* `innerProduct_completeness`, `innerProduct_soundness` — corollaries of the
  sumcheck theorems via the reduction.
* `innerProduct_soundnessError_le` — multilinear specialisation of the
  soundness bound: `≤ n · 2 / |𝔽|` when both factors are multilinear.
-/

namespace InnerProduct

open CPoly

/-- An inner-product sumcheck statement: two polynomials, a summation
domain, and the claimed value of the inner-product sum.

`domain_nodup` mirrors the underlying `SumcheckProtocolStatement` invariant —
required so the claim counts each assignment exactly once. -/
structure InnerProductStatement (𝔽 : Type*) [Field 𝔽] [DecidableEq 𝔽]
    (n : ℕ) where
  domain : List 𝔽
  claim : 𝔽
  f : CMvPolynomial n 𝔽
  g : CMvPolynomial n 𝔽
  domain_nodup : domain.Nodup

variable {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

/-- Reduce an inner-product statement to a sumcheck statement on the product
polynomial. -/
def InnerProductStatement.toSumcheckProtocol {n : ℕ} (I : InnerProductStatement 𝔽 n) :
    SumcheckProtocolStatement 𝔽 n :=
  { domain := I.domain
    claim := I.claim
    polynomial := I.f * I.g
    domain_nodup := I.domain_nodup }

/-- The statement is *valid* when the claim equals the honest inner-product
sum — equivalently, when the reduced sumcheck claim is correct. -/
def InnerProductStatement.Valid {n : ℕ} (I : InnerProductStatement 𝔽 n) : Prop :=
  I.claim = honestClaim I.domain (I.f * I.g)

/-- `Valid` is definitionally the correctness of the reduced sumcheck. -/
theorem valid_iff_toSumcheckProtocol_claim_correct {n : ℕ}
    (I : InnerProductStatement 𝔽 n) :
    I.Valid ↔ sumcheckClaimIsCorrect I.toSumcheckProtocol := Iff.rfl

end InnerProduct

/-! ### Transcripts

Thin wrappers around the existing sumcheck transcript generators, specialised
to `InnerProductStatement` via `toSumcheckProtocol`. -/

namespace InnerProduct

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

/-- Honest-prover transcript for an inner-product claim, given the verifier's
random challenges. -/
def honestTranscript {n : ℕ}
    (I : InnerProductStatement 𝔽 n) (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  generateHonestTranscript I.domain (I.f * I.g) I.claim r

/-- Transcript for an arbitrary (possibly adversarial) prover on an
inner-product claim. -/
def proverTranscript {n : ℕ}
    (I : InnerProductStatement 𝔽 n)
    (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  _root_.proverTranscriptFull I.toSumcheckProtocol P r

end InnerProduct

namespace InnerProduct

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

/-- **Inner-product completeness.** For every valid inner-product statement,
the sumcheck honest prover (applied to `f * g`) convinces the verifier with
probability 1. -/
theorem innerProduct_completeness {n : ℕ}
    (I : InnerProductStatement 𝔽 n) (h : I.Valid) :
    probAccept
      (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))
      I.toSumcheckProtocol
      sumcheckHonestProverFull = 1 :=
  sumcheck_hasPerfectCompleteness I.toSumcheckProtocol
    ((valid_iff_toSumcheckProtocol_claim_correct I).mp h)

/-- **Inner-product soundness.** If the claim does not equal the honest
inner-product sum, no prover convinces the verifier with probability more
than the sumcheck soundness error on `f * g`. -/
theorem innerProduct_soundness {n : ℕ}
    (I : InnerProductStatement 𝔽 n)
    (h : I.claim ≠ honestClaim I.domain (I.f * I.g))
    (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))) :
    probAccept
      (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))
      I.toSumcheckProtocol
      P
      ≤ soundnessError (I.f * I.g) := by
  have hFalse : ¬ sumcheckClaimIsCorrect I.toSumcheckProtocol := by
    unfold sumcheckClaimIsCorrect InnerProductStatement.toSumcheckProtocol
    exact h
  exact sumcheck_hasSoundnessError I.toSumcheckProtocol P hFalse

omit [Fintype 𝔽] [DecidableEq 𝔽] in
/-- Product of two multilinears has individual degree ≤ 2 in every variable.
`ℕ`-level bound on `maxIndDegree (f * g)`. -/
private lemma maxIndDegree_mul_multilinear_le {n : ℕ}
    (f g : CPoly.CMvPolynomial n 𝔽)
    (hf : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i f ≤ 1)
    (hg : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i g ≤ 1) :
    maxIndDegree (f * g) ≤ 2 := by
  unfold maxIndDegree
  refine Finset.sup_le ?_
  intro i _
  have hmul : (f * g).degreeOf i ≤ f.degreeOf i + g.degreeOf i :=
    SharpSAT.degreeOf_mul_le_c f g i
  exact le_trans hmul (Nat.add_le_add (hf i) (hg i))

omit [DecidableEq 𝔽] in
/-- **Multilinear inner-product soundness bound.** When both factors are
multilinear (individual degree ≤ 1 in every variable), the product has
individual degree ≤ 2 in every variable, so the soundness error is bounded by
`n · 2 / |𝔽|`. -/
theorem innerProduct_soundnessError_le_multilinear {n : ℕ}
    (f g : CPoly.CMvPolynomial n 𝔽)
    (hf : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i f ≤ 1)
    (hg : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i g ≤ 1) :
    soundnessError (f * g) ≤ (n : ℚ) * 2 / (fieldSize (𝔽 := 𝔽) : ℚ) := by
  unfold soundnessError
  rcases Nat.eq_zero_or_pos (fieldSize (𝔽 := 𝔽)) with hF | hF
  · simp [hF]
  have hpos : (0 : ℚ) < (fieldSize (𝔽 := 𝔽) : ℚ) := by exact_mod_cast hF
  rw [div_le_div_iff_of_pos_right hpos]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast maxIndDegree_mul_multilinear_le f g hf hg

end InnerProduct
