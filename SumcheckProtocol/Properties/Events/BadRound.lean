import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.IP.Statement

/-- The honest prover's round-`i` polynomial under the full-run shape
(`i : Fin n`, `ch : Fin n → 𝔽`). Unchanged from its pre-partial-run shape:
existing proofs that consume it continue to work.

Partial-run events compare against a `Fin k.val`-shaped variant by computing
`honestProverMessageAt` directly with the appropriate Fin lifts. -/
def honestRoundPoly
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin n → 𝔽)
  (i : Fin n) : CPoly.CMvPolynomial 1 𝔽 :=
  honestProverMessageAt (domain := domain) (p := p) (i := i) (challenges := challengeSubset ch i)

/-- The partial-run analogue of `honestRoundPoly`: round-`i` honest message
where `i : Fin k.val` and challenges live in `Fin k.val → 𝔽`. Computed by
direct invocation of `honestProverMessageAt` with the Fin lifts.

Definitionally equal to `honestRoundPoly domain p ch i` when `k = ⟨n, _⟩`
(both reduce to the same `honestProverMessageAt` application). -/
def honestRoundPolyAtK
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (ch : Fin k.val → 𝔽)
  (i : Fin k.val) : CPoly.CMvPolynomial 1 𝔽 :=
  honestProverMessageAt (domain := domain) (p := p)
    (i := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩)
    (challenges := fun j : Fin i.val => ch ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

/-- At the full-run point, `honestRoundPolyAtK` collapses to the original
`honestRoundPoly`. Bridges Fin-shape proof obligations in downstream proofs
that operate on the full-run case. -/
@[simp] lemma honestRoundPolyAtK_full {𝔽 : Type _} {n : ℕ}
    [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (ch : Fin n → 𝔽) (i : Fin n) :
    honestRoundPolyAtK ⟨n, Nat.lt_succ_self n⟩ domain p ch i
      = honestRoundPoly domain p ch i := rfl

/-- A "bad round" within the first `k.val` rounds of a partial run: the
prover's round-`i` polynomial differs from the honest one. -/
def BadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (domain : List 𝔽)
  (round_poly: CPoly.CMvPolynomial 1 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (challenges : Fin k.val → 𝔽)
  (round_num : Fin k.val) : Prop :=
  round_poly ≠ honestRoundPolyAtK k domain p challenges round_num

def LastBadRound
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽) : Prop :=
  let t := proverTranscript k st P r
  ∃ i : Fin k.val,
    t.roundPolys i ≠ honestRoundPolyAtK k st.domain st.polynomial r i
    ∧
    ∀ j : Fin k.val, i < j →
      t.roundPolys j = honestRoundPolyAtK k st.domain st.polynomial r j

def RoundDisagreeButAgreeAtChallenge
  {𝔽 : Type _} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽) (i : Fin k.val) : Prop :=
  let t := proverTranscript k st P r
  t.roundPolys i ≠ honestRoundPolyAtK (k := k) (domain := st.domain) (p := st.polynomial) (ch := r) i
    ∧ nextClaim (𝔽 := 𝔽) (roundChallenge := r i) (t.roundPolys i)
        = nextClaim (𝔽 := 𝔽) (roundChallenge := r i)
          (honestRoundPolyAtK (k := k) (domain := st.domain) (p := st.polynomial) (ch := r) i)
