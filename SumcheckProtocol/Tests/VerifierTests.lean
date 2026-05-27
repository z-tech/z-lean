import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.CMvMonomial
import CompPoly.Multivariate.Lawful
import Mathlib.Data.ZMod.Basic

import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Verifier

namespace __VerifierTests__

  def test_round_p : CPoly.CMvPolynomial 1 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful <|
      ((0 : CPoly.Unlawful 1 (ZMod 19)).insert ⟨#[1], by decide⟩ (13 : ZMod 19))
        |>.insert ⟨#[0], by decide⟩ (2 : ZMod 19)

  -- Boolean hypercube domain
  def boolDomain : List (ZMod 19) := [0, 1]

  namespace __verifier_check_tests__

    def received_false := verifierCheck boolDomain 1 (11 : ZMod 19) test_round_p
    lemma it_should_check_false_round_correctly : received_false = false := by native_decide

    def received_true := verifierCheck boolDomain 1 (17 : ZMod 19) test_round_p
    lemma it_should_check_true_round_correctly :received_true = true := by native_decide

  end __verifier_check_tests__

  namespace __next_claim_tests__

    def expected_claim : (ZMod 19) := (9 : ZMod 19)
    def received_claim : (ZMod 19) := nextClaim (2 : ZMod 19) test_round_p
    lemma it_should_generate_claim_correctly : received_claim = expected_claim := by native_decide

  end __next_claim_tests__

end __VerifierTests__
