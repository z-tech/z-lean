import SumcheckProtocol.IP.InteractiveProtocol
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 200000

namespace __InteractiveProtocolTests__

/-!
# SumcheckProtocol via the Generic Interactive Protocol Interface

This test exercises the same 2-round sumcheck example from ProtocolTests,
but through the generic `PublicCoinProtocol` interface rather than calling
the prover/verifier functions directly.

**Polynomial**: p = 3x₀x₁ + 5x₀ + 1  over  ZMod 19
**Domain**: boolean hypercube {0, 1}
**Honest sum**: p(0,0) + p(1,0) + p(0,1) + p(1,1) = 1 + 6 + 1 + 9 = 17 mod 19

The generic interface packages this into a `SumcheckProtocolStatement` and uses
`generateTranscript` to automatically run the round-by-round interaction:

  Round 0: prover sends G₀ = 13x + 2        (sum over x₁ ∈ {0,1})
           verifier challenges with r₀ = 2
  Round 1: prover sends G₁ = 6x + 11        (with x₀ fixed to r₀ = 2)
           verifier challenges with r₁ = 3
  Final:   verifier checks G₁(3) = p(2, 3) = 10  ✓

Compare with ProtocolTests.lean, which walks through this same interaction
by hand. Here, `generateTranscript` does the orchestration for us.
-/

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

-- p = 3x₀x₁ + 5x₀ + 1
def poly : CPoly.CMvPolynomial 2 (ZMod 19) :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
      |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
      |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)

def domain : List (ZMod 19) := [0, 1]

-- Verifier's random challenges: r₀ = 2, r₁ = 3
def challenges : Fin 2 → ZMod 19 := ![(2 : ZMod 19), (3 : ZMod 19)]

/-! ## Honest claim: sum = 17

The `SumcheckProtocolStatement` bundles the domain, polynomial, and claimed sum.
The `sumcheckHonestProver` wraps `honestProverMessageAt` as a generic `Prover`.
`generateTranscript` feeds challenges to the prover round by round and
assembles the result — this is the generic analogue of `generateHonestTranscript`.
-/

def honestStatement : SumcheckProtocolStatement (ZMod 19) 2 where
  domain := domain
  claim := (17 : ZMod 19)  -- correct: 1 + 6 + 1 + 9 = 17
  polynomial := poly
  domain_nodup := by decide

-- The generic verifier accepts the honest transcript.
lemma honest_claim_accepted :
    sumcheckProtocolFull.verifierAccepts honestStatement
      (generateTranscript sumcheckProtocolFull honestStatement
        sumcheckHonestProverFull challenges) := by
  -- Rewrite through the bridge lemma to reach the computable verifier,
  -- then unfold the generic prover to its concrete implementation.
  show AcceptsOnChallenges _ _ _ _
  simp only [AcceptsOnChallenges_unfold, AcceptsEvent, isVerifierAccepts,
             Transcript.claims, proverTranscript, proverTranscriptFull,
             sumcheckHonestProver, sumcheckHonestProverFull, residualSum_full_eq_eval]
  native_decide

/-! ## Wrong claim: sum = 18

Same polynomial and domain, but the prover claims the sum is 18 instead of 17.
Even though the prover honestly computes each round polynomial, the initial
claim is wrong, so the verifier's check at round 0 fails:
  G₀(0) + G₀(1) = 2 + 15 = 17 ≠ 18
-/

def dishonestStatement : SumcheckProtocolStatement (ZMod 19) 2 where
  domain := domain
  claim := (18 : ZMod 19)  -- wrong claim
  polynomial := poly
  domain_nodup := by decide

-- The generic verifier rejects the dishonest claim.
lemma wrong_claim_rejected :
    ¬ sumcheckProtocolFull.verifierAccepts dishonestStatement
      (generateTranscript sumcheckProtocolFull dishonestStatement
        sumcheckHonestProverFull challenges) := by
  show ¬ AcceptsOnChallenges _ _ _ _
  simp only [AcceptsOnChallenges_unfold, AcceptsEvent, isVerifierAccepts,
             Transcript.claims, proverTranscript, proverTranscriptFull,
             sumcheckHonestProver, sumcheckHonestProverFull, residualSum_full_eq_eval]
  native_decide

end __InteractiveProtocolTests__
