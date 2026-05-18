import InteractiveProtocol.Src.Protocol
import SumcheckProtocol.Src

/-- A sumcheck statement bundles the evaluation domain, the claimed sum, and
the polynomial whose hypercube-sum is being asserted.

`domain_nodup` ensures the claim counts each assignment exactly once; without
it `honestClaim` would inflate the true sum on repeated domain values, and the
soundness theorem's Schwartz–Zippel argument silently assumes uniform
sampling from `𝔽` not `𝔽 \ domain`. -/
structure SumcheckProtocolStatement (𝔽 : Type*) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) where
  domain : List 𝔽
  claim : 𝔽
  polynomial : CPoly.CMvPolynomial n 𝔽
  domain_nodup : domain.Nodup

-- need predicate so we can quantify over false/ true statements
def sumcheckClaimIsCorrect {𝔽 : Type*} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]
    (st : SumcheckProtocolStatement 𝔽 n) : Prop :=
  st.claim = honestClaim st.domain st.polynomial

-- this is the actual mapping into the framework
def sumcheckProtocol {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    PublicCoinProtocol (SumcheckProtocolStatement 𝔽 n) 𝔽 n where
  ProverMessage := fun _ => CPoly.CMvPolynomial 1 𝔽
  Transcript := (Fin n → CPoly.CMvPolynomial 1 𝔽) × (Fin n → 𝔽)
  mkTranscript := fun msgs chs => (msgs, chs)
  challenges := fun tr => tr.2
  proverMessage := fun tr i => tr.1 i
  verifierAccepts := fun st tr =>
    isVerifierAccepts st.domain st.polynomial st.claim
      { roundPolys := tr.1, challenges := tr.2 } = true
  verifierDecides := fun _ _ => inferInstance
  challenges_mk := fun _ _ => rfl
  proverMessage_mk := fun _ _ _ => rfl

-- the honest sumcheck prover as a generic Prover
def sumcheckHonestProver {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)) where
  respond := fun st i chs =>
    honestProverMessageAt st.domain st.polynomial i chs

-- construct a Transcript from a Prover and challenges
def proverTranscript
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  { roundPolys := fun i => P.respond st i (challengeSubset r i)
    challenges := r }

@[simp] lemma proverTranscript_challenges
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) :
    (proverTranscript st P r).challenges = r := rfl

@[simp] lemma proverTranscript_round_polys
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) (i : Fin n) :
    (proverTranscript st P r).roundPolys i = P.respond st i (challengeSubset r i) := rfl
