import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

import Sumcheck.Properties.Probability.CountingPolynomials
import Sumcheck.Src.Prover
import Sumcheck.Src.Verifier

set_option maxHeartbeats 800000

namespace __ProtocolTests__

  instance : Fact (Nat.Prime 19) := ⟨by decide⟩

  -- p = 3 * x_0 * x_1 + 5 * x_0 + 1, true sum = 17 mod 19
  -- round 0 prover sums over all points
  -- point: [0, 0] -> 1
  -- point: [1, 0] -> 6
  -- point: [0, 1] -> 1
  -- point: [1, 1] -> 9
  -- prover interpolates ((0, 2), (1, 15)) and sends univariate G_0 = 13 * x + 2
  -- verifier checks G_0(0) + G_0(1) =? 17 mod 19
  -- verifier samples a challenge: 2
  -- verifier computes next round claim: 9
  -- round 1 prover sums over smaller points after absorbing verifier challenge
  -- point: [2, 0] -> 11
  -- point: [2, 1] -> 17
  -- prover interpolates ((0, 11), (1, 17)) and sends univariate G_1 = 6 * x + 11
  -- verifier checks G_1(0) + G_1(1) =? G_0(2)
  -- verifier samples a challenge: 3
  -- verifier computes next round claim: 10 <-- this is never used
  -- transcript { prover_messages: [(2, 15), (11, 17)], verifier_messages: [2] }

  -- setup
  def claimPoly : CPoly.CMvPolynomial 2 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful <|
      ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
        |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
        |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)
  def claim : (ZMod 19) := (17 : ZMod 19)

  -- Boolean hypercube domain
  def boolDomain : List (ZMod 19) := [0, 1]

  -- round 0
  def round_poly_0 := honestProverMessageAt boolDomain claimPoly ⟨0, by decide⟩ ![] -- message = 13x + 2
  def max_degree_0 : ℕ := indDegreeK claimPoly ⟨0, by decide⟩
  lemma verifier_check_0_is_correct : verifierCheck boolDomain max_degree_0 claim round_poly_0  = true := by
    simp
    native_decide
  def simulated_challenge_0 : (ZMod 19) := 2

  -- round 1
  def claim_1 := nextClaim simulated_challenge_0 round_poly_0
  def max_degree_1 : ℕ := indDegreeK claimPoly ⟨1, by decide⟩
  def round_poly_1 := honestProverMessageAt boolDomain claimPoly ⟨1, by decide⟩ ![simulated_challenge_0] -- message = 6x + 11
  lemma verifier_check_1_is_correct : verifierCheck boolDomain max_degree_1 claim_1 round_poly_1 = true := by
    simp
    native_decide
  def simulated_challenge_1 : (ZMod 19) := 3

  -- final check
  def final_claim := nextClaim simulated_challenge_1 round_poly_1
  def received := CPoly.CMvPolynomial.eval ![simulated_challenge_0, simulated_challenge_1] claimPoly
  lemma final_check_is_correct : final_claim = received := by
    unfold final_claim
    simp
    native_decide

end __ProtocolTests__
