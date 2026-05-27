import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Src.Prover

namespace __ProverTests__

  def test_p_mon_11 : CPoly.CMvMonomial 2 := ⟨#[1, 1], by decide⟩
  def test_p_mon_10   : CPoly.CMvMonomial 2 := ⟨#[1, 0], by decide⟩
  def test_p_mon_00    : CPoly.CMvMonomial 2 := ⟨#[0, 0], by decide⟩
  def test_p : CPoly.CMvPolynomial 2 (ZMod 19) :=
    CPoly.Lawful.fromUnlawful <|
      ((0 : CPoly.Unlawful 2 (ZMod 19)).insert test_p_mon_11 (3 : ZMod 19))
        |>.insert test_p_mon_10 (5 : ZMod 19)
        |>.insert test_p_mon_00  (1 : ZMod 19)

  -- Boolean hypercube domain
  def boolDomain : List (ZMod 19) := [0, 1]

  namespace __generate_sums_variablewise_tests__

    def expected_sum_0 : (ZMod 19) := (2 : ZMod 19)
    lemma it_should_generate_sum_0_correctly : roundSum boolDomain ![] 0 test_p (by decide) = expected_sum_0 := by
      unfold roundSum test_p expected_sum_0
      simp
      native_decide

    noncomputable def expected_sum_1 : (ZMod 19) := (15 : ZMod 19)
    lemma it_should_generate_sum_1_correctly : roundSum boolDomain ![] 1 test_p (by decide) = expected_sum_1 := by
      unfold roundSum test_p expected_sum_1
      simp
      native_decide

  end __generate_sums_variablewise_tests__

end __ProverTests__
