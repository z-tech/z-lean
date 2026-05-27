import SumcheckProtocol.IP.Statement
import SumcheckProtocol.IP.InteractiveProtocol
import SumcheckProtocol.IP.SharpSAT.Arithmetize
import SumcheckProtocol.IP.SharpSAT.CNF
import SumcheckProtocol.IP.SharpSAT.Degree
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Properties.Lemmas.Hypercube
import InteractiveProtocol.Properties.IPClass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

namespace SharpSAT

open CPoly

/-- A #SAT instance: a 3-CNF formula together with a claimed count. -/
structure SharpSATInstance (n : ℕ) where
  formula : CNF3 n
  count : ℕ

/-- A #SAT instance is *valid* when the claimed count matches the true count. -/
def SharpSATInstance.Valid {n : ℕ} (I : SharpSATInstance n) : Prop :=
  I.count = numSatisfying I.formula

section Bridge

-- Sum over Bool: with the standard Fintype instance `{true, false}` the sum
-- unfolds to `g true + g false`.
lemma sum_univ_bool {β : Type*} [AddCommMonoid β] (g : Bool → β) :
    (∑ b : Bool, g b) = g true + g false := by
  rw [show (Finset.univ : Finset Bool) = ({true, false} : Finset Bool) from rfl,
      Finset.sum_insert (by decide : (true : Bool) ∉ ({false} : Finset Bool)),
      Finset.sum_singleton]

-- Sum over Fin (n+1) → Bool splits into the false branch plus the true branch.
lemma sum_bool_succ {β : Type*} [AddCommMonoid β] {n : ℕ}
    (F : (Fin (n+1) → Bool) → β) :
    (∑ x : (Fin (n+1) → Bool), F x) =
      (∑ x : (Fin n → Bool), F (Fin.cons false x)) +
      (∑ x : (Fin n → Bool), F (Fin.cons true x)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp F,
      Fintype.sum_prod_type]
  rw [sum_univ_bool]
  rw [add_comm]
  rfl

-- Bool-hypercube at n = 0 is a singleton.
lemma sum_bool_zero {β : Type*} [AddCommMonoid β] (F : (Fin 0 → Bool) → β) :
    (∑ x : (Fin 0 → Bool), F x) = F Fin.elim0 := by
  rw [Fintype.sum_unique]; congr

-- sumOverDomainRecursive with domain [0,1] equals the Bool-hypercube sum (coerced).
lemma sumOverDomain_zeroOne_eq_boolSum {𝔽 : Type*} [Field 𝔽] {n : ℕ}
    (F : (Fin n → 𝔽) → 𝔽) :
    sumOverDomainRecursive [(0 : 𝔽), 1] (· + ·) 0 F =
      ∑ x : (Fin n → Bool), F (fun i => boolToField (x i)) := by
  induction n with
  | zero =>
      rw [sum_over_domain_recursive_zero,
          sum_bool_zero (fun x => F (fun i => boolToField (x i)))]
      congr; funext i; exact i.elim0
  | succ n ih =>
      rw [sum_over_domain_recursive_succ,
          sum_bool_succ (fun x => F (fun i => boolToField (x i)))]
      simp only [List.foldl_cons, List.foldl_nil, zero_add]
      rw [ih, ih]
      congr 1
      all_goals {
        apply Finset.sum_congr rfl
        intro x _
        congr
        funext i
        cases i using Fin.cases <;> simp [Fin.cons, boolToField]
      }

-- Unwrap `honestClaim` at domain [0,1] into the Bool-hypercube sum.
lemma honestClaim_zeroOne_eq_boolSum
    {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (p : CMvPolynomial n 𝔽) :
    honestClaim [(0 : 𝔽), 1] p =
      ∑ x : (Fin n → Bool), p.eval (fun i => boolToField (x i)) := by
  unfold honestClaim residualSum
  simp only [Nat.sub_zero]
  rw [sumOverDomain_zeroOne_eq_boolSum]
  apply Finset.sum_congr rfl
  intro x _
  congr
  funext i
  simp [addCasesFun]

end Bridge

section

variable {𝔽 : Type*} [Field 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

-- Map a #SAT instance into the sumcheck statement over the boolean hypercube {0,1}.
def SharpSATInstance.toSumcheckProtocol {n : ℕ} (I : SharpSATInstance n) :
    SumcheckProtocolStatement 𝔽 n :=
  { domain := [0, 1]
    claim := (I.count : 𝔽)
    polynomial := arithmetize (𝔽 := 𝔽) I.formula
    domain_nodup := by
      -- `[0, 1]` is `Nodup` provided `(0 : 𝔽) ≠ 1`, which holds in any field.
      simp [List.Nodup, zero_ne_one] }

/-- **#SAT arithmetization bridge.** Summing the arithmetized polynomial over
the boolean hypercube `{0,1}^n` yields the number of satisfying assignments
(embedded into the field). This is the reduction that lets #SAT plug into the
sumcheck protocol. -/
theorem honestClaim_arithmetize_eq_numSatisfying {n : ℕ} (φ : CNF3 n) :
    honestClaim [(0 : 𝔽), 1] (arithmetize (𝔽 := 𝔽) φ) = (numSatisfying φ : 𝔽) := by
  rw [honestClaim_zeroOne_eq_boolSum]
  simp_rw [eval_arithmetize_eq_indicator]
  unfold numSatisfying
  rw [Finset.sum_boole]

-- For a valid instance, the induced sumcheck claim is correct.
theorem toSumcheckProtocol_valid_claim_correct
    {n : ℕ} {I : SharpSATInstance n} (h : I.Valid) :
    sumcheckClaimIsCorrect (I.toSumcheckProtocol (𝔽 := 𝔽)) := by
  unfold sumcheckClaimIsCorrect SharpSATInstance.toSumcheckProtocol SharpSATInstance.Valid at *
  simp only
  rw [honestClaim_arithmetize_eq_numSatisfying, h]

end

section

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] [DecidableEq 𝔽]

/-- **#SAT completeness.** For every valid #SAT instance, the sumcheck honest
prover convinces the verifier with probability 1. -/
theorem sharpSAT_completeness {n : ℕ}
    (I : SharpSATInstance n) (h : I.Valid) :
    probAccept
      (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))
      (I.toSumcheckProtocol (𝔽 := 𝔽))
      sumcheckHonestProverFull = 1 :=
  sumcheck_hasPerfectCompleteness
    (I.toSumcheckProtocol (𝔽 := 𝔽))
    (toSumcheckProtocol_valid_claim_correct (𝔽 := 𝔽) h)

/-- **#SAT soundness.** If the claim (as a field element) does not equal the
true count (as a field element), no prover can convince the verifier with
probability more than the sumcheck soundness error on the arithmetized formula.
See `sharpSAT_soundnessError_le` in `Degree.lean` for a concrete bound. -/
theorem sharpSAT_soundness {n : ℕ}
    (I : SharpSATInstance n)
    (h : (I.count : 𝔽) ≠ (numSatisfying I.formula : 𝔽))
    (P : Prover (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))) :
    probAccept
      (sumcheckProtocolFull (𝔽 := 𝔽) (n := n))
      (I.toSumcheckProtocol (𝔽 := 𝔽))
      P
      ≤ soundnessError (arithmetize (𝔽 := 𝔽) I.formula) := by
  have hFalse : ¬ sumcheckClaimIsCorrect (I.toSumcheckProtocol (𝔽 := 𝔽)) := by
    unfold sumcheckClaimIsCorrect SharpSATInstance.toSumcheckProtocol
    simp only
    rw [honestClaim_arithmetize_eq_numSatisfying]
    exact h
  exact sumcheck_hasSoundnessError (I.toSumcheckProtocol (𝔽 := 𝔽)) P hFalse

end

/-! ### Packaging into `InIPFamily`

To fit `InIP`'s `ε ≤ 1/3` bound, the field must grow with instance size. We
therefore package `#SAT ∈ IP` as an `InIPFamily`: at size `k`, instances have
arity `k` and at most `k` clauses, and the field `F k` must (a) be large
enough for the Schwartz–Zippel bound (`9k² ≤ |F k|`) and (b) separate counts
at the `ℕ → F k` coercion (so `¬Valid` at `ℕ` transports to a false claim at
`F k`). Existence of a concrete `F : ℕ → Type` with these properties (e.g.
`ZMod p` for a prime `p` in the right range) is a separate construction. -/

/-- Size-indexed #SAT input type: instances of arity `k` with at most `k`
clauses and count in `[0, 2^k]`. The count bound exists so that, for a field
whose characteristic exceeds `2^k`, the coercion from `ℕ` into that field is
injective on the relevant values — ensuring that if the claimed count is
wrong at `ℕ` it is wrong at the field too, and the sumcheck soundness bound
fires. -/
structure SharpSATFamilyInput (k : ℕ) where
  instance_ : SharpSATInstance k
  formula_len_bound : instance_.formula.length ≤ k
  count_bound : instance_.count ≤ 2 ^ k

/-- **#SAT ∈ IP (family version).** Assuming a field scheme `F : ℕ → Type`
where `F k` is large enough (for soundness) and separates `ℕ` on small values
(for `¬Valid ↔ ¬sumcheckClaimIsCorrect`), bounded-size #SAT instances are in
`InIPFamily`. -/
theorem sharpSAT_inIPFamily
    (F : ℕ → Type) [∀ k, Field (F k)] [∀ k, Fintype (F k)]
    [∀ k, BEq (F k)] [∀ k, LawfulBEq (F k)] [∀ k, DecidableEq (F k)]
    (hFieldSize : ∀ k, 9 * k * k ≤ Fintype.card (F k))
    (hFieldInj : ∀ k (a b : ℕ), a ≤ 2 ^ k → b ≤ 2 ^ k →
      (a : F k) = (b : F k) → a = b) :
    InIPFamily
      (Inputs := SharpSATFamilyInput)
      (L := fun _ I => I.instance_.Valid) := by
  refine InIPFamily.of_hasProperties
    (S := fun k => SumcheckProtocolStatement (F k) k)
    (C := F) (n := fun k => k)
    (ip := fun k => sumcheckProtocolFull (𝔽 := F k) (n := k))
    (encode := fun _ I => I.instance_.toSumcheckProtocol (𝔽 := F _))
    (honest := fun _ => sumcheckHonestProverFull)
    (isTrue := fun _ => sumcheckClaimIsCorrect)
    (ε_S := fun _ st => soundnessError st.polynomial)
    ?hcorrespond ?hcomplete ?hsound ?hεbound
  case hcomplete =>
    intro k; exact sumcheck_hasPerfectCompleteness
  case hsound =>
    intro k; exact sumcheck_hasSoundnessError
  case hcorrespond =>
    intro k I
    show I.instance_.Valid ↔ sumcheckClaimIsCorrect (I.instance_.toSumcheckProtocol (𝔽 := F k))
    unfold SharpSATInstance.Valid SharpSATInstance.toSumcheckProtocol
      sumcheckClaimIsCorrect
    simp only
    rw [honestClaim_arithmetize_eq_numSatisfying]
    constructor
    · intro h; exact congrArg (Nat.cast : ℕ → F k) h
    · intro h
      exact hFieldInj k _ _ I.count_bound
        (numSatisfying_le I.instance_.formula) h
  case hεbound =>
    intro k I
    show soundnessError (arithmetize (𝔽 := F k) I.instance_.formula) ≤ 1/3
    refine le_trans (sharpSAT_soundnessError_le (𝔽 := F k) I.instance_.formula) ?_
    unfold fieldSize
    rcases Nat.eq_zero_or_pos (Fintype.card (F k)) with hz | hpos
    · have hkz : k = 0 := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · exact hk
        · exfalso
          have h9 : 9 * k * k ≤ 0 := hz ▸ hFieldSize k
          nlinarith
      subst hkz; simp
    have hpos' : (0 : ℚ) < (Fintype.card (F k) : ℚ) := by exact_mod_cast hpos
    rw [div_le_iff₀ hpos']
    have hlen : (I.instance_.formula.length : ℚ) ≤ (k : ℚ) := by
      exact_mod_cast I.formula_len_bound
    have h9 : (9 * k * k : ℚ) ≤ (Fintype.card (F k) : ℚ) := by
      exact_mod_cast hFieldSize k
    have hknn : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.zero_le k
    have hlennn : (0 : ℚ) ≤ (I.instance_.formula.length : ℚ) := by
      exact_mod_cast Nat.zero_le _
    push_cast
    nlinarith

/-! ### Concrete field scheme discharging the hypotheses

Construct a concrete `F : ℕ → Type` with `F k = ZMod p_k` where `p_k` is a
prime `≥ max(2^k + 1, 9k² + 1)`. Existence is `Nat.exists_infinite_primes`;
the prime is selected by `Classical.choose`. This discharges both hypotheses
of `sharpSAT_inIPFamily` and yields an unconditional #SAT ∈ IP theorem. -/

/-- A prime at least `max(2^k + 1, 9k² + 1)`, selected via Euclid. -/
noncomputable def sharpSATPrime (k : ℕ) : ℕ :=
  (Nat.exists_infinite_primes (max (2 ^ k + 1) (9 * k * k + 1))).choose

private lemma sharpSATPrime_ge (k : ℕ) :
    max (2 ^ k + 1) (9 * k * k + 1) ≤ sharpSATPrime k :=
  (Nat.exists_infinite_primes (max (2 ^ k + 1) (9 * k * k + 1))).choose_spec.1

private lemma sharpSATPrime_isPrime (k : ℕ) : Nat.Prime (sharpSATPrime k) :=
  (Nat.exists_infinite_primes (max (2 ^ k + 1) (9 * k * k + 1))).choose_spec.2

instance sharpSATPrime_fact (k : ℕ) : Fact (Nat.Prime (sharpSATPrime k)) :=
  ⟨sharpSATPrime_isPrime k⟩

/-- The field at size `k`: `ZMod p_k` where `p_k` is the prime above. -/
abbrev sharpSATField (k : ℕ) : Type := ZMod (sharpSATPrime k)

private lemma sharpSATField_card (k : ℕ) :
    Fintype.card (sharpSATField k) = sharpSATPrime k :=
  ZMod.card (sharpSATPrime k)

private lemma sharpSATField_size_bound (k : ℕ) :
    9 * k * k ≤ Fintype.card (sharpSATField k) := by
  rw [sharpSATField_card]
  have := sharpSATPrime_ge k
  omega

private lemma sharpSATField_count_bound (k : ℕ) :
    2 ^ k < sharpSATPrime k := by
  have := sharpSATPrime_ge k
  omega

private lemma sharpSATField_cast_inj (k : ℕ) (a b : ℕ)
    (ha : a ≤ 2 ^ k) (hb : b ≤ 2 ^ k)
    (h : (a : sharpSATField k) = (b : sharpSATField k)) :
    a = b := by
  have hp : 2 ^ k < sharpSATPrime k := sharpSATField_count_bound k
  have ha' : a < sharpSATPrime k := lt_of_le_of_lt ha hp
  have hb' : b < sharpSATPrime k := lt_of_le_of_lt hb hp
  rw [ZMod.natCast_eq_natCast_iff] at h
  -- h : a ≡ b [MOD sharpSATPrime k], i.e. a % p = b % p.
  have := h  -- unfold Nat.ModEq manually
  rw [Nat.ModEq] at this
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this

/-- **#SAT ∈ IP (unconditional).** Bounded-size #SAT instances are in
`InIPFamily`, with the field scheme `sharpSATField k = ZMod p_k` discharging
the field hypotheses. -/
theorem sharpSAT_inIPFamily_concrete :
    InIPFamily
      (Inputs := SharpSATFamilyInput)
      (L := fun _ I => I.instance_.Valid) :=
  sharpSAT_inIPFamily sharpSATField sharpSATField_size_bound
    sharpSATField_cast_inj

end SharpSAT
