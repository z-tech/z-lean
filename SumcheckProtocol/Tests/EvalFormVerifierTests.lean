import Mathlib.Algebra.Field.ZMod

import SumcheckProtocol.IP.Statement
import SumcheckProtocol.Src.EvalFormVerifier

/-!
# Evaluation-form verifier: regression tests

Executable checks of `isEvalVerifierAccepts` over `ZMod 17`
(`native_decide`, as in the other `Tests/` files). Natural nodes `0..d`
are distinct in `ZMod 17` because `d < 17`.

* Example 1 (`EvalFormTests`): `p(x) = 1 + 2x`, claim 4.
* Example 3 (`EvalFormTests`): `p(x,y,z) = x²y + z`, claim 6, round degree
  bounds `(2, 1, 1)`, first tuple `G₀(0), G₀(1), G₀(2) = 2, 4, 10`.
  Partial runs `k = 0..3`, challenges on and off the nodes, per-round
  shifted nodes, wrong claims, malformed and adversarial tuples.
* Degree 0: `p(x,y) = x + 3` has degree 0 in `y`; the last round sends a
  single value.
* Over-degree message: a symbolic degree-2 message for a degree-1 round is
  rejected symbolically but its two node values are accepted, so the
  degree hypothesis of `isVerifierAccepts_eq_encode` is necessary. With
  the challenge at a node, only the symbolic degree check rejects it.
-/

namespace __EvalFormVerifierTests__

open CompPoly.CPolynomial.CLagrange (BarycentricDomain)

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev 𝔽 := ZMod 17

/-- Natural nodes `0, …, d` in `ZMod 17`. -/
def natNodes (d : ℕ) (h : d < 17) : BarycentricDomain 𝔽 (d + 1) :=
  BarycentricDomain.mk' (fun i => (i.val : 𝔽)) (by
    intro a b hab
    apply Fin.ext
    have ha : a.val % 17 = a.val := Nat.mod_eq_of_lt (by omega)
    have hb : b.val % 17 = b.val := Nat.mod_eq_of_lt (by omega)
    have := (ZMod.natCast_eq_natCast_iff' a.val b.val 17).mp hab
    omega)

/-- The nodes `3, 5, 7`. -/
def shifted : BarycentricDomain 𝔽 3 :=
  BarycentricDomain.mk' ![3, 5, 7] (by decide)

def domain : List 𝔽 := [0, 1]

/-! ## Barycentric evaluation -/

-- Weights for nodes 0,1,2: (1/2, -1, 1/2) = (9, 16, 9).
example : (natNodes 2 (by decide)).weights 0 = 9 := by native_decide
example : (natNodes 2 (by decide)).weights 1 = 16 := by native_decide
-- G₀(c) = 2c² + 2 from its values 2, 4, 10: at a node and away from it.
example : (natNodes 2 (by decide)).eval ![2, 4, 10] 1 = 4 := by native_decide
example : (natNodes 2 (by decide)).eval ![2, 4, 10] 5 = 1 := by native_decide
-- The same polynomial from its values at 3, 5, 7.
example : shifted.eval ![3, 1, 15] 0 = 2 := by native_decide
-- Boundary parser.
example : (tupleOf? 2 ([2, 4, 10] : List 𝔽)).isSome = true := by native_decide
example : (tupleOf? 2 ([2, 4] : List 𝔽)).isSome = false := by native_decide
example : (tupleOf? 2 ([2, 4, 10, 0] : List 𝔽)).isSome = false := by native_decide

/-! ## Example 1: `p(x) = 1 + 2x` -/

namespace Example1

def p : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 1 𝔽).insert ⟨#[0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1], by decide⟩ (2 : 𝔽)

def k : Fin 2 := ⟨1, by decide⟩

def i0 : Fin k.val := ⟨0, by decide⟩

theorem degree_lt : ∀ i, roundDegree p k i < 17 := by native_decide

def nodes : RoundNodes 𝔽 (roundDegree p k) := fun i => natNodes _ (degree_lt i)

def run (claim : 𝔽) (ys : List 𝔽) (r : 𝔽) : Bool :=
  isEvalVerifierAccepts k domain p nodes claim ⟨![ys], ![r]⟩

example : roundDegree p k i0 = 1 := by native_decide
example : run 4 [1, 3] 2 = true := by native_decide          -- p(2) = 5
example : run 4 [1, 3] 1 = true := by native_decide          -- challenge at a node
example : run 4 [18, 20] 2 = true := by native_decide        -- literals 18 ≡ 1, 20 ≡ 3
example : run 5 [1, 3] 2 = false := by native_decide         -- wrong claim
example : run 4 [0, 4] 2 = false := by native_decide         -- sums to 4, wrong final value
example : run 4 [1] 2 = false := by native_decide            -- too short
example : run 4 [1, 3, 5] 2 = false := by native_decide      -- too long

/-- An over-degree symbolic message `1 + x + x²`: it agrees with `1 + 2x`
at the nodes `0, 1`, but not at the challenge `2`. -/
def q : CPoly.CMvPolynomial 1 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 1 𝔽).insert ⟨#[0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[1], by decide⟩ (1 : 𝔽)
      |>.insert ⟨#[2], by decide⟩ (1 : 𝔽)

def overDegree : Transcript 𝔽 1 := ⟨![q], ![2]⟩

-- The symbolic verifier rejects (degree 2 > 1, and q(2) = 7 ≠ p(2)) ...
example : isVerifierAccepts k domain p 4 overDegree = false := by native_decide
-- ... but the node values [1, 3] are the honest ones and are accepted.
example : encodeMessage (nodes i0) q = [1, 3] := by native_decide
example : isEvalVerifierAccepts k domain p nodes 4
    (overDegree.encode (roundDegree p k) nodes) = true := by native_decide

/-- The same message with the challenge at the node `1`. Here the domain
sum `q(0) + q(1) = 4` and the final value `q(1) = 3 = p(1)` are both
correct, so the symbolic verifier rejects only by its degree check. -/
def overDegreeAtNode : Transcript 𝔽 1 := ⟨![q], ![1]⟩

example : CPoly.CMvPolynomial.eval (fun _ => 0) q + CPoly.CMvPolynomial.eval (fun _ => 1) q = 4 := by
  native_decide
example : nextClaim 1 q = CPoly.CMvPolynomial.eval ![1] p := by native_decide
example : CPoly.CMvPolynomial.degreeOf 0 q = 2 := by native_decide
example : isVerifierAccepts k domain p 4 overDegreeAtNode = false := by native_decide
example : isEvalVerifierAccepts k domain p nodes 4
    (overDegreeAtNode.encode (roundDegree p k) nodes) = true := by native_decide

end Example1

/-! ## Example 3: `p(x,y,z) = x²y + z` -/

namespace Example3

def p : CPoly.CMvPolynomial 3 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 3 𝔽).insert ⟨#[2, 1, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[0, 0, 1], by decide⟩ (1 : 𝔽)

def st : SumcheckProtocolStatement 𝔽 3 where
  domain := domain
  claim := 6
  polynomial := p
  domain_nodup := by decide

theorem degree_le : ∀ j : Fin 3, indDegreeK p j ≤ 2 := by native_decide

/-- Natural nodes, sized by each round's degree bound. -/
def nodes (k : Fin 4) : RoundNodes 𝔽 (roundDegree p k) := fun i =>
  natNodes _ (Nat.lt_of_le_of_lt (degree_le _) (by decide))

/-- Honest messages in evaluation form. -/
def honest (k : Fin 4) (r : Fin k.val → 𝔽) (ns : RoundNodes 𝔽 (roundDegree p k)) :
    EvalTranscript 𝔽 k.val :=
  (proverTranscript k st (sumcheckHonestProver k) r).encode (roundDegree p k) ns

def k0 : Fin 4 := ⟨0, by decide⟩
def k1 : Fin 4 := ⟨1, by decide⟩
def k2 : Fin 4 := ⟨2, by decide⟩
def k3 : Fin 4 := ⟨3, by decide⟩

def r3 : Fin 3 → 𝔽 := ![3, 5, 6]

def i0 : Fin k3.val := ⟨0, by decide⟩
def i1 : Fin k3.val := ⟨1, by decide⟩
def i2 : Fin k3.val := ⟨2, by decide⟩

-- Mixed degree bounds (2, 1, 1), hence tuple lengths (3, 2, 2).
example : roundDegree p k3 i0 = 2 := by native_decide
example : roundDegree p k3 i1 = 1 := by native_decide
example : roundDegree p k3 i2 = 1 := by native_decide
example : (honest k3 r3 (nodes k3)).roundEvals i0 = [2, 4, 10] := by native_decide
example : ((honest k3 r3 (nodes k3)).roundEvals i1).length = 2 := by native_decide

-- Honest runs, partial and full.
example : isEvalVerifierAccepts k0 domain p (nodes k0) 6 ⟨Fin.elim0, Fin.elim0⟩ = true := by
  native_decide
example : isEvalVerifierAccepts k1 domain p (nodes k1) 6 (honest k1 ![3] (nodes k1)) = true := by
  native_decide
example : isEvalVerifierAccepts k2 domain p (nodes k2) 6
    (honest k2 ![3, 5] (nodes k2)) = true := by native_decide
example : isEvalVerifierAccepts k3 domain p (nodes k3) 6 (honest k3 r3 (nodes k3)) = true := by
  native_decide
-- Challenges at the nodes.
example : isEvalVerifierAccepts k3 domain p (nodes k3) 6
    (honest k3 ![1, 0, 1] (nodes k3)) = true := by native_decide

-- Per-round nodes: round 0 uses 3, 5, 7; first values G₀(3), G₀(5), G₀(7).
theorem degree0 : roundDegree p k3 i0 = 2 := by native_decide

def mixedNodes : RoundNodes 𝔽 (roundDegree p k3) := fun i =>
  if h : i = i0 then cast (by rw [h, degree0]) shifted else nodes k3 i

example : (honest k3 r3 mixedNodes).roundEvals i0 = [3, 1, 15] := by native_decide
example : isEvalVerifierAccepts k3 domain p mixedNodes 6 (honest k3 r3 mixedNodes) = true := by
  native_decide

-- Wrong claims.
example : isEvalVerifierAccepts k3 domain p (nodes k3) 7 (honest k3 r3 (nodes k3)) = false := by
  native_decide
example : isEvalVerifierAccepts k0 domain p (nodes k0) 7 ⟨Fin.elim0, Fin.elim0⟩ = false := by
  native_decide

/-- Replace round 0's list. -/
def withRound0 (ys : List 𝔽) : EvalTranscript 𝔽 3 :=
  let t := honest k3 r3 (nodes k3)
  ⟨fun i => if i.val = 0 then ys else t.roundEvals i, t.challenges⟩

-- Adversarial values with the right sum fail later; malformed lengths fail at once.
example : isEvalVerifierAccepts k3 domain p (nodes k3) 6 (withRound0 [2, 4, 11]) = false := by
  native_decide
example : isEvalVerifierAccepts k3 domain p (nodes k3) 6 (withRound0 [2, 4]) = false := by
  native_decide
example : isEvalVerifierAccepts k3 domain p (nodes k3) 6 (withRound0 [2, 4, 10, 0]) = false := by
  native_decide

-- The symbolic verifier gives the same verdicts on the honest transcripts.
example : isVerifierAccepts k3 domain p 6 (proverTranscript k3 st (sumcheckHonestProver k3) r3)
    = true := by native_decide

end Example3

/-! ## Degree 0 and a larger domain -/

namespace DegreeZero

/-- `p(x, y) = x + 3`: degree 1 in `x`, degree 0 in `y`. -/
def p : CPoly.CMvPolynomial 2 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 2 𝔽).insert ⟨#[1, 0], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[0, 0], by decide⟩ (3 : 𝔽)

def k : Fin 3 := ⟨2, by decide⟩

theorem degree_lt : ∀ i, roundDegree p k i < 17 := by native_decide

def nodes : RoundNodes 𝔽 (roundDegree p k) := fun i => natNodes _ (degree_lt i)

def dom3 : List 𝔽 := [0, 1, 2]

-- Σ_{x,y ∈ {0,1,2}} (x + 3) = 3·(0+1+2) + 9·3 = 36 ≡ 2.
-- Round 0: G₀(x) = 3(x + 3), values 9, 12. Round 1 (after r₀ = 4): G₁ = 7, one value.
example : roundDegree p k ⟨1, by decide⟩ = 0 := by native_decide
example : isEvalVerifierAccepts k dom3 p nodes 2 ⟨![[9, 12], [7]], ![4, 10]⟩ = true := by
  native_decide
example : isEvalVerifierAccepts k dom3 p nodes 2 ⟨![[9, 12], [7, 7]], ![4, 10]⟩ = false := by
  native_decide
-- Repeated domain entries are kept: over [0, 1, 1] the claim changes.
example : isEvalVerifierAccepts k [0, 1, 1] p nodes 2 ⟨![[9, 12], [7]], ![4, 10]⟩ = false := by
  native_decide

end DegreeZero

end __EvalFormVerifierTests__
