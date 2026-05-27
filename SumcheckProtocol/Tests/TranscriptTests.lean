import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Algebra.Field.ZMod

import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.Verifier

set_option maxHeartbeats 800000

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

-- 3x0x1 + 5x0 + 1
def claimPoly : CPoly.CMvPolynomial 2 (ZMod 19) :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 (ZMod 19)).insert ⟨#[1, 1], by decide⟩ (3 : ZMod 19))
      |>.insert ⟨#[1, 0], by decide⟩ (5 : ZMod 19)
      |>.insert ⟨#[0, 0], by decide⟩  (1 : ZMod 19)
def claim : (ZMod 19) := (17 : ZMod 19)
def simulatedChallenges := ![(2 : ZMod 19), (3 : ZMod 19)]

-- Boolean hypercube domain
def boolDomain : List (ZMod 19) := [0, 1]

def validTranscript := generateHonestTranscript boolDomain claimPoly claim simulatedChallenges
lemma valid_transcript_accepts :
    isVerifierAccepts ⟨2, by decide⟩ boolDomain claimPoly claim validTranscript = true := by
  unfold isVerifierAccepts
  simp
  native_decide

def invalidTranscript := generateHonestTranscript boolDomain claimPoly (claim + 1) simulatedChallenges
lemma invalid_transcript_rejects :
    isVerifierAccepts ⟨2, by decide⟩ boolDomain claimPoly (claim + 1)
      invalidTranscript = false := by
  unfold isVerifierAccepts
  simp
  native_decide
