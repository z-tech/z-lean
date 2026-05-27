/-
# Johnson-bound list-decoding for MDS / Reed-Solomon codes

This file packages the squared-form Johnson bound used by the BCGM25 §6.2
list-decoding capstone (`ListDecoding/MCA.lean`). The "squared" form means
we avoid `Real.sqrt` on the load-bearing path: list sizes are stated as
the integer `JohnsonListSize n = n^2`, which plugs cleanly into the
ℚ-arithmetic of the seed-probability bounds. Callers that pre-multiply
by a generator-multiplicity slack `(ℓ + 1)` use `JohnsonListSizeWithSlack`
instead.

Key contents:
* `JohnsonListSizeWithSlack_pos`, `_mono_ell`, `_mono_n`, `_at_zero`,
  `_eq` — basic monotonicity / boundary properties of the slack form.
* `JohnsonListSize_eq_slack_zero` — bridge between the tight and slack
  forms at `ℓ = 0`.
* `IsListDecodable_squared_johnson_MDS` and friends — list-decodability
  certificates for MDS / Reed–Solomon codes at the squared-Johnson radius.
* `johnson_squared_iff_real_sqrt` — bridge to the standard `Real.sqrt` form
  for paper fidelity.

Depends on `LinearCodes.MCA.ListDecoding.Core`, `LinearCodes.MCA.ConcreteMDS`,
and `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
-/

import LinearCodes.MCA.ListDecoding.Core
import LinearCodes.MCA.ConcreteMDS
import Upstream.Combinatorics.Corradi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Finite


namespace LinearCodes

/-! ### J1-J3: Johnson list-size basic properties (split from L14) -/

/-- J1: `JohnsonListSizeWithSlack` is positive when `n > 0`. -/
theorem JohnsonListSizeWithSlack_pos {ℓ n : ℕ} (hn : 0 < n) :
    0 < JohnsonListSizeWithSlack ℓ n := by
  unfold JohnsonListSizeWithSlack
  exact Nat.mul_pos (Nat.succ_pos ℓ) (pow_pos hn 2)

/-- J2a: Monotone in ℓ. -/
theorem JohnsonListSizeWithSlack_mono_ell {ℓ ℓ' n : ℕ} (h : ℓ ≤ ℓ') :
    JohnsonListSizeWithSlack ℓ n ≤ JohnsonListSizeWithSlack ℓ' n := by
  unfold JohnsonListSizeWithSlack
  exact Nat.mul_le_mul_right (n ^ 2) (Nat.add_le_add_right h 1)

/-- J2b: Monotone in n. -/
theorem JohnsonListSizeWithSlack_mono_n {ℓ n n' : ℕ} (h : n ≤ n') :
    JohnsonListSizeWithSlack ℓ n ≤ JohnsonListSizeWithSlack ℓ n' := by
  unfold JohnsonListSizeWithSlack
  exact Nat.mul_le_mul_left (ℓ + 1) (Nat.pow_le_pow_left h 2)

/-- J3: At `n = 0`, slack list size is 0. -/
theorem JohnsonListSizeWithSlack_at_zero (ℓ : ℕ) : JohnsonListSizeWithSlack ℓ 0 = 0 := by
  simp [JohnsonListSizeWithSlack]

/-- J3b: At `ℓ = 0`, the slack form collapses to the tight `JohnsonListSize n = n²`.
This is the bridge between the slack and tight forms. -/
theorem JohnsonListSize_eq_slack_zero (n : ℕ) :
    JohnsonListSize n = JohnsonListSizeWithSlack 0 n := by
  simp [JohnsonListSize, JohnsonListSizeWithSlack]

/-- J3c: Definitional unfolding `(ℓ+1)·n²`. -/
theorem JohnsonListSizeWithSlack_eq (ℓ n : ℕ) :
    JohnsonListSizeWithSlack ℓ n = (ℓ + 1) * n ^ 2 := rfl

/-- J3d: Definitional unfolding `n²`. -/
theorem JohnsonListSize_eq (n : ℕ) : JohnsonListSize n = n ^ 2 := rfl

/-- J3e: The tight Johnson list-size is positive when `n > 0`. -/
theorem JohnsonListSize_pos {n : ℕ} (hn : 0 < n) : 0 < JohnsonListSize n :=
  pow_pos hn 2

/-! ### J4-J5: Boundary case-consistency lemmas -/

/-- J4: At radius 0, any code is `(0, JohnsonListSizeWithSlack ℓ n)`-list-decodable for n > 0. -/
theorem IsListDecodable_zero_radius_via_Johnson
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) (ℓ : ℕ) (hn : 0 < n) :
    IsListDecodable c 0 (JohnsonListSizeWithSlack ℓ n) :=
  (IsListDecodable_zero c).mono_L (JohnsonListSizeWithSlack_pos hn)

/-- J5: At unique-decoding radius `2τ < d`, list size fits inside `JohnsonListSizeWithSlack`. -/
theorem IsListDecodable_at_unique_decoding_threshold
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c : Submodule F (Fin n → F)} {d : ℕ} (h_minDist : MinDistAtLeast c d)
    {τ : ℕ} (hτ : 2 * τ < d) (ℓ : ℕ) (hn : 0 < n) :
    IsListDecodable c τ (JohnsonListSizeWithSlack ℓ n) :=
  (IsListDecodable_of_minDist_unique h_minDist hτ).mono_L (JohnsonListSizeWithSlack_pos hn)

/-! ### J6-J7: MDS Johnson bound (squared form)

The classical Johnson bound: any MDS code of dimension `k` is
`(τ, n²)`-list-decodable whenever `(n − τ)² > n·k`.

## Proof outline

For received word `u : Fin n → F`, let `L : Finset (Fin n → F)` be the
candidate codewords (`v ∈ c` with `hammingDistance u v ≤ τ`). Each
`agreementSet u v ⊆ Fin n` has size `≥ n - τ` (from the distance bound),
and pairwise intersections have size `≤ k - 1` for `v ≠ w` in the code
(`MDS_pairwise_agreement_bound`). Applying Corrádi's intersection lemma
(`Finset.corradi_mul_le_of_card_ge` in `Upstream/Combinatorics/Corradi.lean`,
the lower-bound variant) to this family yields:
`|L|² · (n - τ)² ≤ |L| · n² + |L|·(|L| - 1)·n·(k - 1)`.

The arithmetic finish `johnson_final_arithmetic` cancels one `|L|` and
applies the hypothesis `(n - τ)² > n·k` to conclude `|L| ≤ n²`. -/

/-- J6-δ (final arithmetic): closes the Corrádi-shaped chain to `|L| ≤ n²`.

The combined chain (in ℕ):
  `(Lcard * (n - τ))² ≤ n * (n * Lcard + Lcard * (Lcard - 1) * (k - 1))`

implies `Lcard ≤ n²` under the Johnson hypothesis `(n-τ)² > n·k` and `k ≥ 1`.

**Proof.**
- Case `Lcard = 0`: trivial.
- Case `Lcard ≥ 1`: expand the LHS as `Lcard² · (n-τ)²` and the RHS as
  `n²·Lcard + n·Lcard·(Lcard-1)·(k-1)`. Replace `Lcard - 1` by `Lcard` (since
  `Lcard - 1 ≤ Lcard`), then cancel one factor of `Lcard` (Lcard ≥ 1) to get
  `Lcard·(n-τ)² ≤ n² + n·Lcard·(k-1)`.
  From `hτ`: `(n-τ)² ≥ n·k + 1`, hence `(n-τ)² ≥ n·(k-1) + (n+1)` (using `k ≥ 1`).
  Thus `Lcard·(n+1) ≤ n²`, so `Lcard ≤ Lcard·(n+1) ≤ n²`. -/
theorem johnson_final_arithmetic
    {n k τ : ℕ} {Lcard : ℕ} (hk_pos : 1 ≤ k)
    (hτ : (n - τ) * (n - τ) > n * k)
    (h_cs : (Lcard * (n - τ)) ^ 2 ≤ n * (n * Lcard + Lcard * (Lcard - 1) * (k - 1))) :
    Lcard ≤ n ^ 2 := by
  by_cases hL : Lcard = 0
  · rw [hL]; exact Nat.zero_le _
  have hL_pos : 1 ≤ Lcard := Nat.one_le_iff_ne_zero.mpr hL
  -- n ≥ 1: (n - τ)² > n·k ≥ 0, so (n - τ)² > 0, forcing n ≥ 1.
  have hn_pos : 0 < n := by
    by_contra h_n
    push_neg at h_n
    have hn0 : n = 0 := Nat.le_zero.mp h_n
    rw [hn0] at hτ
    simp at hτ
  -- Step 1: rewrite h_cs in expanded ℕ-polynomial form.
  have h_cs' : (Lcard * (n - τ))^2 ≤
      n * (n * Lcard) + n * (Lcard * (Lcard - 1) * (k - 1)) := by
    have h_eq : n * (n * Lcard + Lcard * (Lcard - 1) * (k - 1)) =
        n * (n * Lcard) + n * (Lcard * (Lcard - 1) * (k - 1)) := by ring
    linarith [h_cs]
  -- Step 2: replace `Lcard - 1` with `Lcard` (since `Lcard - 1 ≤ Lcard`).
  have h_sub_le : Lcard * (Lcard - 1) * (k - 1) ≤ Lcard * Lcard * (k - 1) := by
    have hsl : Lcard * (Lcard - 1) ≤ Lcard * Lcard :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact Nat.mul_le_mul_right _ hsl
  have h_chain : (Lcard * (n - τ))^2 ≤
      n^2 * Lcard + n * Lcard * Lcard * (k - 1) := by
    nlinarith [h_cs', h_sub_le]
  -- Step 3: rewrite as Lcard² · (n-τ)² ≤ ...
  have h_LcardSq : Lcard^2 * (n - τ)^2 ≤ n^2 * Lcard + n * Lcard^2 * (k - 1) := by
    nlinarith [h_chain]
  -- Step 4: cancel one factor of Lcard.
  have h_div : Lcard * (n - τ)^2 ≤ n^2 + n * Lcard * (k - 1) := by
    have h_eq1 : Lcard^2 * (n - τ)^2 = Lcard * (Lcard * (n - τ)^2) := by ring
    have h_eq2 : n^2 * Lcard + n * Lcard^2 * (k - 1) =
        Lcard * (n^2 + n * Lcard * (k - 1)) := by ring
    rw [h_eq1, h_eq2] at h_LcardSq
    exact Nat.le_of_mul_le_mul_left h_LcardSq hL_pos
  -- Step 5: from hτ get `n·k + 1 ≤ (n - τ)²`.
  have h_nt_sq : n * k + 1 ≤ (n - τ)^2 := by
    have h_sq : (n - τ)^2 = (n - τ) * (n - τ) := sq (n - τ)
    omega
  -- Step 6: hence `(n - τ)² ≥ n·(k-1) + (n + 1)` (using k ≥ 1).
  have h_nt_ge : (n - τ)^2 ≥ n * (k - 1) + (n + 1) := by
    have h_kform : n * k = n * (k - 1) + n := by
      nlinarith [Nat.sub_add_cancel hk_pos]
    omega
  -- Step 7: hence `Lcard·(n+1) ≤ n²`.
  have h_Lcard_lo :
      n * Lcard * (k - 1) + Lcard * (n + 1) ≤ Lcard * (n - τ)^2 := by
    have := Nat.mul_le_mul_left Lcard h_nt_ge
    linarith [this]
  have h_final : Lcard * (n + 1) ≤ n^2 := by
    linarith [h_Lcard_lo, h_div]
  -- Step 8: Lcard ≤ Lcard·(n+1) ≤ n².
  calc Lcard ≤ Lcard * (n + 1) := by
        have h_one : 1 ≤ n + 1 := by omega
        exact Nat.le_mul_of_pos_right Lcard h_one
    _ ≤ n^2 := h_final

/-- J6: Squared Johnson bound for MDS submodules. If `(n - τ)² > n·k`, then
the code is `(τ, n²)`-list-decodable, i.e., every Hamming ball of radius `τ`
contains at most `n²` codewords. Built by applying
`Finset.corradi_mul_le_of_card_ge` to the agreement-set family
`{agreementSet u v}_{v ∈ L}` and finishing with `johnson_final_arithmetic`.

Edge case `k = 0` is dispatched directly: an MDS code of dimension 0 is
`⊥ = {0}`, and the singleton case fits in `n²` (since `n ≥ 1` from `h_johnson`). -/
theorem IsListDecodable_squared_johnson_MDS
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k) :
    IsListDecodable c τ (JohnsonListSize n) := by
  rw [JohnsonListSize_eq]
  -- n ≥ 1 (since (n - τ)² > 0 from h_johnson).
  have hn_pos : 0 < n := by
    by_contra h_n
    push_neg at h_n
    have hn0 : n = 0 := Nat.le_zero.mp h_n
    rw [hn0] at h_johnson
    simp at h_johnson
  -- Edge case k = 0: c = ⊥, so ball has at most 1 codeword.
  by_cases hk : k = 0
  · subst hk
    have hc_bot : c = ⊥ := Submodule.finrank_eq_zero.mp h_MDS.1
    have h_one : IsListDecodable c τ 1 := by
      rw [hc_bot]; exact IsListDecodable_bot τ
    have h_one_le : 1 ≤ n^2 := by
      have h_eq : n^2 = n * n := sq n
      have : 1 ≤ n * n := Nat.mul_le_mul hn_pos hn_pos
      omega
    exact h_one.mono_L h_one_le
  -- Main case k ≥ 1: apply Corrádi's lemma + final arithmetic.
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  intro u
  classical
  -- Pull the codewords-within-radius set into a Finset L.
  let L : Finset (Fin n → F) :=
    Finset.univ.filter (fun v => v ∈ c ∧ hammingDistance u v ≤ τ)
  have hL_card_eq :
      {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.ncard = L.card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext v; simp [L]
  have hL_in_c : ∀ v ∈ L, v ∈ c := fun v hv =>
    (Finset.mem_filter.mp hv).2.1
  have hL_in_ball : ∀ v ∈ L, hammingDistance u v ≤ τ := fun v hv =>
    (Finset.mem_filter.mp hv).2.2
  -- Apply `corradi_mul_le_of_card_ge` to the family
  -- `{agreementSet u v}_{v ∈ L}`, with `a := n - τ`, `b := k - 1`,
  -- ambient `A := univ : Finset (Fin n)`.
  have h_card_ge : ∀ v : ↥L, (n - τ) ≤ (agreementSet u v.val).card := by
    rintro ⟨v, hv⟩
    show (n - τ) ≤ (agreementSet u v).card
    have h_eq := agreementSet_card_add_hammingDistance u v
    have h_dist : hammingDistance u v ≤ τ := hL_in_ball v hv
    omega
  have h_pairwise : ∀ v w : ↥L, v ≠ w →
      (agreementSet u v.val ∩ agreementSet u w.val).card ≤ k - 1 := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h_ne
    show (agreementSet u v ∩ agreementSet u w).card ≤ k - 1
    have h_ne_val : v ≠ w := fun h => h_ne (Subtype.ext h)
    have := MDS_pairwise_agreement_bound h_MDS u (hL_in_c v hv) (hL_in_c w hw) h_ne_val
    omega
  have h_corradi := Finset.corradi_mul_le_of_card_ge
    (α := Fin n) (ι := ↥L) (A := (Finset.univ : Finset (Fin n)))
    (As := fun v => agreementSet u v.val) (a := n - τ) (b := k - 1)
    (fun _ => Finset.subset_univ _) h_card_ge h_pairwise
  rw [Fintype.card_coe L, Finset.card_univ, Fintype.card_fin] at h_corradi
  -- Translate Corrádi's conclusion into δ's input shape.
  have h_chain : (L.card * (n - τ))^2 ≤
      n * (n * L.card + L.card * (L.card - 1) * (k - 1)) := by
    nlinarith [h_corradi]
  -- (δ) Final arithmetic.
  have h_delta : L.card ≤ n^2 :=
    johnson_final_arithmetic hk_pos h_johnson h_chain
  rw [hL_card_eq]
  exact h_delta

/-- J7: J6 with an explicit `ℓ` parameter; conclusion uses
`JohnsonListSizeWithSlack ℓ n`. The `(ℓ + 1)` slack is **not** part of
the Johnson bound itself — it is a caller-supplied relaxation introduced
here via `IsListDecodable.mono_L`. -/
theorem IsListDecodable_squared_johnson_MDS_explicit
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k)
    (ℓ : ℕ) :
    IsListDecodable c τ (JohnsonListSizeWithSlack ℓ n) := by
  have h_tight := IsListDecodable_squared_johnson_MDS h_MDS h_johnson
  refine h_tight.mono_L ?_
  -- JohnsonListSize n = n² ≤ (ℓ + 1) · n² = JohnsonListSizeWithSlack ℓ n
  rw [JohnsonListSize_eq, JohnsonListSizeWithSlack_eq]
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos ℓ)

/-! ### J8: domain-of-validity helper -/

/-- J8: Squared-Johnson hypothesis is consistent with reaching beyond
unique-decoding radius. -/
theorem pos_n_sub_τ_of_johnson_sq
    {n k τ : ℕ} (h_johnson : (n - τ) * (n - τ) > n * k) (_hk_le : k ≤ n) :
    n - τ > 0 := by
  by_contra h
  push_neg at h
  have h_zero : n - τ = 0 := Nat.le_zero.mp h
  rw [h_zero] at h_johnson
  simp at h_johnson

/-! ### J10: Real-form bridge (paper fidelity) -/

/-- J10: Squared form is equivalent to the `Real.sqrt` form. Optional bridge. -/
theorem johnson_squared_iff_real_sqrt
    {n k τ : ℕ} (_hk : k ≤ n) (hτ : τ ≤ n) :
    ((n : ℝ) - τ) > Real.sqrt ((n : ℝ) * k) ↔ (n - τ) * (n - τ) > n * k := by
  have hk_R : (0 : ℝ) ≤ ((n : ℝ) * k) := by positivity
  have hτ_R : (τ : ℝ) ≤ n := by exact_mod_cast hτ
  have h_n_sub_R : (0 : ℝ) ≤ (n : ℝ) - τ := by linarith
  have h_cast : ((n - τ : ℕ) : ℝ) = (n : ℝ) - (τ : ℝ) := by
    rw [Nat.cast_sub hτ]
  have h_sqrt_nn : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * k) := Real.sqrt_nonneg _
  constructor
  · intro h_R
    -- (n - τ : ℝ) > sqrt(nk) ≥ 0, so squaring both sides preserves the inequality
    have h_sq : ((n : ℝ) - τ) * ((n : ℝ) - τ) > (n : ℝ) * k := by
      have h1 : ((n : ℝ) - τ) * ((n : ℝ) - τ) >
          Real.sqrt ((n : ℝ) * k) * Real.sqrt ((n : ℝ) * k) := by
        exact mul_lt_mul'' h_R h_R h_sqrt_nn h_sqrt_nn
      rwa [Real.mul_self_sqrt hk_R] at h1
    -- Cast back to ℕ
    have h_R' : (((n - τ) * (n - τ) : ℕ) : ℝ) > ((n * k : ℕ) : ℝ) := by
      push_cast
      rw [h_cast]
      exact h_sq
    exact_mod_cast h_R'
  · intro h_ℕ
    -- ℕ inequality lifts to ℝ
    have h_R' : (((n - τ) * (n - τ) : ℕ) : ℝ) > ((n * k : ℕ) : ℝ) := by
      exact_mod_cast h_ℕ
    have h_sq : ((n : ℝ) - τ) * ((n : ℝ) - τ) > (n : ℝ) * k := by
      have htmp := h_R'
      push_cast at htmp
      rw [h_cast] at htmp
      exact htmp
    -- (n - τ) ≥ 0 and (n - τ)² > nk gives (n - τ) > sqrt(nk)
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : (n : ℝ) - τ ≤ sqrt(nk)
    have h_le : ((n : ℝ) - τ) * ((n : ℝ) - τ) ≤
        Real.sqrt ((n : ℝ) * k) * Real.sqrt ((n : ℝ) * k) :=
      mul_le_mul h_neg h_neg h_n_sub_R h_sqrt_nn
    rw [Real.mul_self_sqrt hk_R] at h_le
    linarith

end LinearCodes
