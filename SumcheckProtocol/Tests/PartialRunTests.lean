import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

import SumcheckProtocol.IP.Statement
import SumcheckProtocol.Src.Prover
import SumcheckProtocol.Src.Verifier

/-!
# Partial-run sumcheck smoke test

Exercises `sumcheckProtocol` with `k < n` on a concrete polynomial to
confirm:
- the protocol elaborates with a non-trivial `k`,
- the honest prover produces a transcript that the verifier accepts,
- the residual-claim check (`claims (Fin.last k.val) = residualSum domain
  challenges p _`) matches the actual residual sum.

Polynomial: `p(x₀, x₁, x₂) = x₀·x₁·x₂ + 1` over `ZMod 7`.
Domain: `{0, 1}` (boolean hypercube).

- `honestClaim` = `∑_{b ∈ {0,1}³} p(b) = 7·1 + 1·2 = 9 ≡ 2 mod 7`.
- Partial run with `k = 1`: prover sends `G₀(x) = ∑_{x₁,x₂ ∈ {0,1}} p(x, x₁, x₂)`,
  verifier picks `r₀ = 3`, residual claim is `G₀(3) = residualSum domain
  [3] p _ = ∑_{x₁,x₂} (3·x₁·x₂ + 1) = 4 + 3 = 7 ≡ 0 mod 7`.
- Partial run with `k = 2`: continue past round 0 with a second challenge
  `r₁ = 5`. Residual claim = `residualSum domain [3, 5] p _`.
- Partial run with `k = 3` (= n, full run): the final residual collapses
  to `p.eval [3, 5, 6] = 3·5·6 + 1 = 91 ≡ 0 mod 7`.
-/

namespace __PartialRunTests__

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev 𝔽 := ZMod 7

-- p(x₀, x₁, x₂) = x₀·x₁·x₂ + 1
def poly : CPoly.CMvPolynomial 3 𝔽 :=
  CPoly.Lawful.fromUnlawful <|
    ((0 : CPoly.Unlawful 3 𝔽).insert ⟨#[1, 1, 1], by decide⟩ (1 : 𝔽))
      |>.insert ⟨#[0, 0, 0], by decide⟩ (1 : 𝔽)

def domain : List 𝔽 := [0, 1]

def claim : 𝔽 := (2 : 𝔽)  -- = honestClaim, mod 7

def statement : SumcheckProtocolStatement 𝔽 3 where
  domain := domain
  claim := claim
  polynomial := poly
  domain_nodup := by decide

-- Smoke test: honestClaim is indeed 2 mod 7.
example : honestClaim (n := 3) domain poly = (2 : 𝔽) := by native_decide

/-! ## k = 1 partial run -/

def k1 : Fin 4 := ⟨1, by decide⟩

-- 1 challenge for the partial run.
def challenges_k1 : Fin 1 → 𝔽 := ![(3 : 𝔽)]

-- The honest prover's transcript at k=1.
def transcript_k1 : Transcript 𝔽 1 :=
  proverTranscript k1 statement (sumcheckHonestProver k1) challenges_k1

-- The verifier accepts the honest k=1 partial-run transcript.
example :
    isVerifierAccepts k1 statement.domain statement.polynomial statement.claim
      transcript_k1 = true := by
  native_decide

/-! ## k = 2 partial run -/

def k2 : Fin 4 := ⟨2, by decide⟩

def challenges_k2 : Fin 2 → 𝔽 := ![(3 : 𝔽), (5 : 𝔽)]

def transcript_k2 : Transcript 𝔽 2 :=
  proverTranscript k2 statement (sumcheckHonestProver k2) challenges_k2

example :
    isVerifierAccepts k2 statement.domain statement.polynomial statement.claim
      transcript_k2 = true := by
  native_decide

/-! ## k = 3 (full run, residual collapses to `eval`) -/

def k3 : Fin 4 := ⟨3, by decide⟩

def challenges_k3 : Fin 3 → 𝔽 := ![(3 : 𝔽), (5 : 𝔽), (6 : 𝔽)]

def transcript_k3 : Transcript 𝔽 3 :=
  proverTranscript k3 statement (sumcheckHonestProver k3) challenges_k3

example :
    isVerifierAccepts k3 statement.domain statement.polynomial statement.claim
      transcript_k3 = true := by
  native_decide

end __PartialRunTests__
