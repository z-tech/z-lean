import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.IP.Statement

def honestRoundPoly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honestProverMessageAt (domain := domain) (p := p) (i := i) (challenges := challengeSubset ch i)

def BadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (round_poly: CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin n → 𝔽)
  (round_num : Fin n) : Prop :=
  round_poly ≠ honestRoundPoly domain p challenges round_num

def LastBadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) : Prop :=
  let t := proverTranscriptFull st P r
  ∃ i : Fin n,
    t.roundPolys i ≠ honestRoundPoly st.domain st.polynomial r i
    ∧
    ∀ j : Fin n, i < j →
      t.roundPolys j = honestRoundPoly st.domain st.polynomial r j

def RoundDisagreeButAgreeAtChallenge
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) (i : Fin n) : Prop :=
  let t := proverTranscriptFull st P r
  t.roundPolys i ≠ honestRoundPoly (domain := st.domain) (p := st.polynomial) (ch := r) i
    ∧ nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
        = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
          (honestRoundPoly (domain := st.domain) (p := st.polynomial) (ch := r) i)
