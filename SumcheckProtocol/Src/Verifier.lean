import CompPoly.Multivariate.CMvPolynomial
import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Hypercube

@[simp] def verifierCheck {𝔽} [CommRing 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (maxDegree : ℕ)
  (roundClaim : 𝔽)
  (roundP : CPoly.CMvPolynomial 1 𝔽) : Bool :=
  let roundIdentityOk : Prop :=
    domain.foldl (fun acc a =>
      acc + CPoly.CMvPolynomial.eval (fun _ : Fin 1 => a) roundP) 0
      = roundClaim
  let degBoundOk : Prop :=
    CPoly.CMvPolynomial.degreeOf ⟨0, by decide⟩ roundP ≤ maxDegree
  decide roundIdentityOk && decide degBoundOk

-- the verifier checks the transcript given an initial claim, parameterised by
-- the stop round `k : Fin (n + 1)`. The prover ran `k.val` rounds, leaving
-- `n - k.val` variables unbound; the verifier accepts iff the first `k.val`
-- rounds are internally consistent AND the final claim equals the residual
-- sum over the remaining boolean hypercube.
--
-- When `k.val = n` (full run), `residualSum_full_eq_eval` collapses the final
-- check to `p.eval challenges`, recovering the original full-run verifier.
def isVerifierAccepts
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (initialClaim : 𝔽)
  (t : Transcript 𝔽 k.val) : Bool :=
  let claims := t.claims initialClaim
  have hk_le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  let roundsOk : Bool :=
    (List.finRange k.val).all (fun i : Fin k.val =>
      verifierCheck domain (indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩)
        (claims (Fin.castSucc i)) (t.roundPolys i)
      &&
      decide (claims i.succ = nextClaim (t.challenges i) (t.roundPolys i))
    )
  let finalOk : Bool :=
    decide (claims (Fin.last k.val) =
      residualSum (𝔽 := 𝔽) domain t.challenges p hk_le)
  roundsOk && finalOk
