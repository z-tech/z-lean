import Mathlib.Data.ZMod.Basic
import SumcheckProtocol.IP.SharpSAT

-- End-to-end smoke test for the #SAT ∈ IP pipeline. The point is not to
-- exercise nontrivial behavior but to force the whole stack (CNF → arithmetize
-- → sumcheck → IP bridge → completeness) to elaborate on a concrete instance.
-- If any upstream signature shifts, this fails to type-check.

namespace __SharpSATTests__

open SharpSAT

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev 𝔽 := ZMod 7

-- The empty 3-CNF over 2 variables: every assignment satisfies it, so the
-- count of satisfying assignments is 2² = 4.
def emptyInstance : SharpSATInstance 2 := { formula := [], count := 4 }

theorem emptyInstance_valid : emptyInstance.Valid := by
  show (4 : ℕ) = numSatisfying ([] : CNF3 2)
  decide

-- Smoke check 1: completeness lifts from `sharpSAT_completeness` to a concrete
-- `probAccept = 1` statement over ZMod 7.
theorem smoke_completeness :
    probAccept
      (sumcheckProtocol (𝔽 := 𝔽) (n := 2))
      (emptyInstance.toSumcheckProtocol (𝔽 := 𝔽))
      sumcheckHonestProver = 1 :=
  sharpSAT_completeness emptyInstance emptyInstance_valid

-- Smoke check 2: an invalid instance (claim ≠ true count). In ZMod 7, the
-- counts 3 and 4 remain distinct, so the soundness-path hypothesis holds.
def badInstance : SharpSATInstance 2 := { formula := [], count := 3 }

theorem smoke_soundness (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := 2))) :
    probAccept
      (sumcheckProtocol (𝔽 := 𝔽) (n := 2))
      (badInstance.toSumcheckProtocol (𝔽 := 𝔽))
      P
      ≤ soundnessError (arithmetize (𝔽 := 𝔽) badInstance.formula) := by
  apply sharpSAT_soundness
  show ((3 : ℕ) : 𝔽) ≠ ((numSatisfying ([] : CNF3 2) : ℕ) : 𝔽)
  decide

end __SharpSATTests__
