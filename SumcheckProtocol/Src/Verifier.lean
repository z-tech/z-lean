import CompPoly.Multivariate.CMvPolynomial
import SumcheckProtocol.Src.Transcript
import SumcheckProtocol.Src.CMvPolynomial

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

-- the verifier checks the transcript given an initial claim
def isVerifierAccepts
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (initialClaim : 𝔽)
  (t : Transcript 𝔽 n) : Bool :=
  let claims := t.claims initialClaim
  let roundsOk : Bool :=
    (List.finRange n).all (fun i : Fin n =>
      verifierCheck domain (indDegreeK p i) (claims (Fin.castSucc i)) (t.roundPolys i)
      &&
      decide (claims i.succ = nextClaim (t.challenges i) (t.roundPolys i))
    )
  let finalOk : Bool :=
    decide (claims (Fin.last n) = CPoly.CMvPolynomial.eval t.challenges p)
  roundsOk && finalOk
