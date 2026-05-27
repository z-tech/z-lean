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

-- this is the actual mapping into the framework.
-- `k : Fin (n + 1)` is the stop round: protocol runs `k.val` rounds, ending with
-- a residual claim about `sum over remaining n - k.val boolean variables of
-- p(challenges, _)`. `k = ⟨n, _⟩` recovers the full-run protocol (final claim
-- equals `p.eval challenges` by `residualSum_full_eq_eval`).
def sumcheckProtocol {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (k : Fin (n + 1)) :
    PublicCoinProtocol (SumcheckProtocolStatement 𝔽 n) 𝔽 k.val where
  ProverMessage := fun _ => CPoly.CMvPolynomial 1 𝔽
  Transcript := (Fin k.val → CPoly.CMvPolynomial 1 𝔽) × (Fin k.val → 𝔽)
  mkTranscript := fun msgs chs => (msgs, chs)
  challenges := fun tr => tr.2
  proverMessage := fun tr i => tr.1 i
  verifierAccepts := fun st tr =>
    isVerifierAccepts k st.domain st.polynomial st.claim
      { roundPolys := tr.1, challenges := tr.2 } = true
  verifierDecides := fun _ _ => inferInstance
  challenges_mk := fun _ _ => rfl
  proverMessage_mk := fun _ _ _ => rfl

-- the honest sumcheck prover as a generic Prover, partial-run aware.
def sumcheckHonestProver {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (k : Fin (n + 1)) :
    Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k) where
  respond := fun st i chs =>
    -- Round `i : Fin k.val` corresponds to variable `i.val` of the polynomial
    -- (same i used by the symbolic spec); lift to `Fin n` via `k.val ≤ n`.
    honestProverMessageAt st.domain st.polynomial
      ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩ chs

-- construct a Transcript from a Prover and challenges
def proverTranscript
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (k : Fin (n + 1))
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
    (r : Fin k.val → 𝔽) : Transcript 𝔽 k.val :=
  { roundPolys := fun i => P.respond st i (challengeSubset r i)
    challenges := r }

@[simp] lemma proverTranscript_challenges
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (k : Fin (n + 1))
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
    (r : Fin k.val → 𝔽) :
    (proverTranscript k st P r).challenges = r := rfl

@[simp] lemma proverTranscript_round_polys
    {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (k : Fin (n + 1))
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
    (r : Fin k.val → 𝔽) (i : Fin k.val) :
    (proverTranscript k st P r).roundPolys i = P.respond st i (challengeSubset r i) := rfl

/-! ### Full-run aliases

Backward-compatibility shims for callers that pre-date the partial-run
refactor. `sumcheckProtocolFull n` and `proverTranscriptFull` are
`sumcheckProtocol ⟨n, _⟩` and `proverTranscript ⟨n, _⟩` specialised to the
full-run case (`k = n`); both are `abbrev`s so they're definitionally
transparent for typeclass resolution and tactic rewriting.

These will be removed in Step 3 of the partial-run epic when soundness and
completeness theorems get properly k-parameterized. -/

/-- Full-run sumcheck protocol: `sumcheckProtocol ⟨n, _⟩`. -/
abbrev sumcheckProtocolFull {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    PublicCoinProtocol (SumcheckProtocolStatement 𝔽 n) 𝔽 n :=
  sumcheckProtocol ⟨n, Nat.lt_succ_self n⟩

/-- Full-run prover transcript: `proverTranscript ⟨n, _⟩`. -/
abbrev proverTranscriptFull {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (st : SumcheckProtocolStatement 𝔽 n)
    (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)))
    (r : Fin n → 𝔽) : Transcript 𝔽 n :=
  proverTranscript ⟨n, Nat.lt_succ_self n⟩ st P r

/-- Full-run honest prover: `sumcheckHonestProver ⟨n, _⟩`. -/
abbrev sumcheckHonestProverFull {𝔽 : Type*} {n : ℕ} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] :
    Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n)) :=
  sumcheckHonestProver ⟨n, Nat.lt_succ_self n⟩
