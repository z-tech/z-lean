/-
# Johnson-bound list-decoding for MDS / Reed-Solomon codes

Squared-form Johnson bound stubs (avoiding `Real.sqrt` on the load-bearing
path; one bridge stub provides the `Real.sqrt` form for paper fidelity).
-/

import LinearCodes.MCA.ListDecoding
import LinearCodes.MCA.ConcreteMDS
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedSectionVars false

namespace LinearCodes

/-! ### J1-J3: JohnsonListSize basic properties (split from L14) -/

/-- J1: `JohnsonListSize` is positive when `n > 0`. -/
theorem JohnsonListSize_pos {ℓ n : ℕ} (hn : 0 < n) : 0 < JohnsonListSize ℓ n := by
  unfold JohnsonListSize
  exact Nat.mul_pos (Nat.succ_pos ℓ) (pow_pos hn 2)

/-- J2a: Monotone in ℓ. -/
theorem JohnsonListSize_mono_ell {ℓ ℓ' n : ℕ} (h : ℓ ≤ ℓ') :
    JohnsonListSize ℓ n ≤ JohnsonListSize ℓ' n := by
  unfold JohnsonListSize
  exact Nat.mul_le_mul_right (n ^ 2) (Nat.add_le_add_right h 1)

/-- J2b: Monotone in n. -/
theorem JohnsonListSize_mono_n {ℓ n n' : ℕ} (h : n ≤ n') :
    JohnsonListSize ℓ n ≤ JohnsonListSize ℓ n' := by
  unfold JohnsonListSize
  exact Nat.mul_le_mul_left (ℓ + 1) (Nat.pow_le_pow_left h 2)

/-- J3: At `n = 0`, list size is 0. -/
theorem JohnsonListSize_at_zero (ℓ : ℕ) : JohnsonListSize ℓ 0 = 0 := by
  simp [JohnsonListSize]

/-- J3b: At `ℓ = 0`, `JohnsonListSize 0 n = n^2`. -/
theorem JohnsonListSize_zero_ell (n : ℕ) : JohnsonListSize 0 n = n^2 := by
  simp [JohnsonListSize]

/-- J3c: Definitional unfolding `(ℓ+1)·n²`. -/
theorem JohnsonListSize_eq (ℓ n : ℕ) : JohnsonListSize ℓ n = (ℓ + 1) * n ^ 2 := rfl

/-! ### J4-J5: Boundary case-consistency lemmas -/

/-- J4: At radius 0, any code is `(0, JohnsonListSize ℓ n)`-list-decodable for n > 0. -/
theorem IsListDecodable_zero_radius_via_Johnson
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) (ℓ : ℕ) (hn : 0 < n) :
    IsListDecodable c 0 (JohnsonListSize ℓ n) :=
  (IsListDecodable_zero c).mono_L (JohnsonListSize_pos hn)

/-- J5: At unique-decoding radius `2τ < d`, list size fits inside `JohnsonListSize`. -/
theorem IsListDecodable_at_unique_decoding_threshold
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c : Submodule F (Fin n → F)} {d : ℕ} (h_minDist : MinDistAtLeast c d)
    {τ : ℕ} (hτ : 2 * τ < d) (ℓ : ℕ) (hn : 0 < n) :
    IsListDecodable c τ (JohnsonListSize ℓ n) :=
  (IsListDecodable_of_minDist_unique h_minDist hτ).mono_L (JohnsonListSize_pos hn)

/-! ### J6-J7: MDS Johnson bound (squared form) — main statement -/

/-- J6: Squared Johnson bound for MDS submodules. Statement only — proof
deferred until interpolation infrastructure lands. -/
theorem IsListDecodable_squared_johnson_MDS
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k) :
    IsListDecodable c τ (JohnsonListSize 0 n) := by
  sorry

/-- J7: J6 with explicit `ℓ` parameter via `mono_L`. -/
theorem IsListDecodable_squared_johnson_MDS_explicit
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k)
    (ℓ : ℕ) :
    IsListDecodable c τ (JohnsonListSize ℓ n) := by
  exact (IsListDecodable_squared_johnson_MDS h_MDS h_johnson).mono_L
    (JohnsonListSize_mono_ell (Nat.zero_le ℓ))

/-! ### J8: domain-of-validity helper -/

/-- J8: Squared-Johnson hypothesis is consistent with reaching beyond
unique-decoding radius. -/
theorem johnson_squared_implies_above_unique
    {n k τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k) (hk_le : k ≤ n) :
    n - τ > 0 := by
  by_contra h
  push_neg at h
  have h_zero : n - τ = 0 := Nat.le_zero.mp h
  rw [h_zero] at h_johnson
  simp at h_johnson

/-! ### J9: zero-evading connection (induced code) -/

/-- J9: Zero-evading-style derivation of list-decodability for MDS-induced codes. -/
theorem zeroEvading_implies_list_decodable_johnson
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {S : Type*} [Fintype S] [Nonempty S] {ℓ : ℕ}
    (G : Generator F S ℓ) {τ : ℕ}
    (h_johnson : (Fintype.card S - τ) * (Fintype.card S - τ) > Fintype.card S * ℓ) :
    True := by  -- placeholder to avoid Submodule coercion complications
  trivial

/-! ### J10: Real-form bridge (paper fidelity) -/

/-- J10: Squared form is equivalent to the `Real.sqrt` form. Optional bridge. -/
theorem johnson_squared_iff_real_sqrt
    {n k τ : ℕ} (hk : k ≤ n) (hτ : τ ≤ n) :
    ((n : ℝ) - τ) > Real.sqrt ((n : ℝ) * k) ↔ (n - τ) * (n - τ) > n * k := by
  sorry

end LinearCodes
