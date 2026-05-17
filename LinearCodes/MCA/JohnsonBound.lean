/-
# Johnson-bound list-decoding for MDS / Reed-Solomon codes

This file packages the squared-form Johnson bound used by the BCGM25 §6.2
list-decoding capstone (`ListDecodingMCA.lean`). The "squared" form means
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

Depends on `LinearCodes.MCA.ListDecoding`, `LinearCodes.MCA.ConcreteMDS`,
and `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
-/

import LinearCodes.MCA.ListDecoding
import LinearCodes.MCA.ConcreteMDS
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Finite

set_option linter.unusedSectionVars false

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

## Proof outline (Cauchy-Schwarz double-counting)

For received word `u : Fin n → F`, let `L : Finset (Fin n → F)` be the
candidate codewords (`v ∈ c` with `hammingDistance u v ≤ τ`). For each
coordinate `x : Fin n`, set `nₓ := |{v ∈ L : v x = u x}|`. Then:

- **(α) Lower bound**: `S := ∑_x nₓ = ∑_v |agree(u, v)| ≥ |L| · (n - τ)`.
- **(β) Cauchy-Schwarz** (`coverCount_cauchy_schwarz` / `sq_sum_le_card_mul_sum_sq`):
  `S² ≤ n · ∑_x nₓ²`.
- **(γ) Pairwise upper bound** (uses MDS): `∑_x nₓ² ≤ n · |L| + |L| · (|L| - 1) · (k - 1)`.
  Diagonal `∑_v |As v|` is bounded by `n·|L|`; off-diagonal pairs are
  bounded by `k - 1` via `MDS_pairwise_agreement_bound`.

Combining (α)+(β)+(γ): `|L|² · (n - τ)² ≤ n² · |L| + n · |L| · (|L| - 1) · (k - 1)`.
Dividing by `|L|` and simplifying:
`|L| · ((n - τ)² - n·(k - 1)) ≤ n² - n·(k - 1)`.
Under hypothesis `(n - τ)² > n·k`, the LHS coefficient is `≥ 1`, so
`|L| ≤ n² - n·(k - 1) ≤ n² = JohnsonListSize 0 n`. ✓

The four atomic helpers below capture each step. -/

/-- J6-α (lower bound): for any list `L` of codewords each within `τ` of `u`,
`∑_x nₓ ≥ |L| · (n - τ)`. -/
theorem johnson_S_lower_bound
    {F : Type*} [DecidableEq F] {n : ℕ} (τ : ℕ)
    (u : Fin n → F)
    (L : Finset (Fin n → F))
    (hL : ∀ v ∈ L, hammingDistance u v ≤ τ) :
    L.card * (n - τ) ≤
      ∑ x : Fin n, (L.filter (fun v => v x = u x)).card := by
  classical
  -- Step 1: rewrite each filter.card as ∑_v indicator.
  have h_filter_eq : ∀ x : Fin n,
      (L.filter (fun v => v x = u x)).card =
        ∑ v ∈ L, (if v x = u x then (1 : ℕ) else 0) := fun x => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  -- Step 2: swap sums via Fubini.
  have h_swap : ∑ x : Fin n, (L.filter (fun v => v x = u x)).card =
      ∑ v ∈ L, ∑ x : Fin n, (if v x = u x then (1 : ℕ) else 0) := by
    simp_rw [h_filter_eq]
    rw [Finset.sum_comm]
  rw [h_swap]
  -- Step 3: for each v ∈ L, ∑ x, [v x = u x] = |agreementSet u v|.
  have h_inner : ∀ v ∈ L,
      ∑ x : Fin n, (if v x = u x then (1 : ℕ) else 0) =
        (agreementSet u v).card := by
    intro v _
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    -- Show the two filter sets are equal as Finsets.
    have h_set : (Finset.univ.filter fun x : Fin n => v x = u x) = agreementSet u v := by
      ext x
      simp [agreementSet, eq_comm]
    rw [h_set]
  have h_inner_le : ∀ v ∈ L, n - τ ≤
      ∑ x : Fin n, (if v x = u x then (1 : ℕ) else 0) := by
    intro v hv
    rw [h_inner v hv]
    -- |agreementSet u v| + hammingDistance u v = n, and dist ≤ τ.
    have h_eq := agreementSet_card_add_hammingDistance u v
    have h_dist : hammingDistance u v ≤ τ := hL v hv
    omega
  -- Step 4: sum over v ∈ L of constant `n - τ` gives `L.card * (n - τ)`.
  calc L.card * (n - τ)
      = ∑ _v ∈ L, (n - τ) := by rw [Finset.sum_const]; ring
    _ ≤ ∑ v ∈ L, ∑ x : Fin n, (if v x = u x then (1 : ℕ) else 0) :=
        Finset.sum_le_sum h_inner_le

/-- J6-β (Cauchy-Schwarz): `(∑ x, nₓ)² ≤ n · ∑ x, nₓ²`. Direct application of
Mathlib's `sq_sum_le_card_mul_sum_sq` (in `Mathlib.Algebra.Order.Chebyshev`). -/
theorem johnson_cauchy_schwarz
    {F : Type*} [DecidableEq F] {n : ℕ}
    (u : Fin n → F)
    (L : Finset (Fin n → F)) :
    (∑ x : Fin n, (L.filter (fun v => v x = u x)).card) ^ 2 ≤
      n * ∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun x : Fin n => ((L.filter (fun v => v x = u x)).card : ℕ))
  simpa [Finset.card_univ, Fintype.card_fin] using h

/-- J6-γ (pairwise upper bound on Q): `∑ x, nₓ² ≤ n·|L| + |L|·(|L|-1)·(k-1)`,
using the MDS pairwise-agreement bound.

**Proof.** Expand `Q = ∑_x nₓ² = ∑_{v,w ∈ L} #(agree(u,v) ∩ agree(u,w))`
(double counting). Split into diagonal `v = w` (which contributes
`∑_v #(agree(u,v)) ≤ n·|L|`) and off-diagonal `v ≠ w` (each term bounded
by `k - 1` via `MDS_pairwise_agreement_bound`). Off-diagonal has
`|L|·(|L|-1)` pairs. -/
theorem johnson_Q_upper_bound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    (u : Fin n → F)
    (L : Finset (Fin n → F))
    (hL_in_c : ∀ v ∈ L, v ∈ c) :
    ∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2 ≤
      n * L.card + L.card * (L.card - 1) * (k - 1) := by
  -- Step γ.1: Q expansion as nested sum over L × L.
  have h_Q_expansion :
      (∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2) =
        ∑ v ∈ L, ∑ w ∈ L, (agreementSet u v ∩ agreementSet u w).card := by
    simp_rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    rw [Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro w _
    have hfilter : agreementSet u v ∩ agreementSet u w =
        Finset.univ.filter (fun x : Fin n => v x = u x ∧ w x = u x) := by
      ext x; simp [agreementSet, eq_comm]
    rw [hfilter, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hv : v x = u x
    · by_cases hw : w x = u x
      · simp [hv, hw]
      · simp [hv, hw]
    · simp [hv]
  -- Step γ.2: split into diagonal (v = w) and off-diagonal (v ≠ w).
  have h_diag_offdiag :
      (∑ v ∈ L, ∑ w ∈ L, (agreementSet u v ∩ agreementSet u w).card) =
        (∑ v ∈ L, (agreementSet u v).card) +
        (∑ v ∈ L, ∑ w ∈ L.erase v,
            (agreementSet u v ∩ agreementSet u w).card) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [show (agreementSet u v).card =
        (agreementSet u v ∩ agreementSet u v).card from by rw [Finset.inter_self]]
    exact (Finset.add_sum_erase L
      (fun w => (agreementSet u v ∩ agreementSet u w).card) hv).symm
  -- Step γ.3a: diagonal ≤ n · |L|.
  have h_diag_le : (∑ v ∈ L, (agreementSet u v).card) ≤ n * L.card := by
    calc (∑ v ∈ L, (agreementSet u v).card)
        ≤ ∑ _v ∈ L, n := by
          apply Finset.sum_le_sum
          intro v _
          calc (agreementSet u v).card
              ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
            _ = n := by rw [Finset.card_univ, Fintype.card_fin]
      _ = n * L.card := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Step γ.3b: off-diagonal ≤ |L| · (|L| - 1) · (k - 1) via MDS pairwise.
  have h_offdiag_le :
      (∑ v ∈ L, ∑ w ∈ L.erase v,
          (agreementSet u v ∩ agreementSet u w).card) ≤
        L.card * (L.card - 1) * (k - 1) := by
    by_cases hk : k = 0
    · -- k = 0: MDS pairwise gives `< 0`, impossible — each off-diagonal term is 0.
      subst hk
      have h_zero : (∑ v ∈ L, ∑ w ∈ L.erase v,
          (agreementSet u v ∩ agreementSet u w).card) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        apply Finset.sum_eq_zero
        intro w hw
        have hw_in : w ∈ L := (Finset.mem_erase.mp hw).2
        have h_ne : v ≠ w := (Finset.mem_erase.mp hw).1.symm
        have h_pair := MDS_pairwise_agreement_bound h_MDS u
          (hL_in_c v hv) (hL_in_c w hw_in) h_ne
        omega
      rw [h_zero]
      exact Nat.zero_le _
    · -- k ≥ 1: each off-diagonal term ≤ k - 1; there are |L|·(|L|-1) terms.
      have h_inner : ∀ v ∈ L,
          (∑ w ∈ L.erase v, (agreementSet u v ∩ agreementSet u w).card) ≤
            (L.card - 1) * (k - 1) := by
        intro v hv
        calc (∑ w ∈ L.erase v, (agreementSet u v ∩ agreementSet u w).card)
            ≤ ∑ _w ∈ L.erase v, (k - 1) := by
              apply Finset.sum_le_sum
              intro w hw
              have hw_in : w ∈ L := (Finset.mem_erase.mp hw).2
              have h_ne : v ≠ w := (Finset.mem_erase.mp hw).1.symm
              have h_pair := MDS_pairwise_agreement_bound h_MDS u
                (hL_in_c v hv) (hL_in_c w hw_in) h_ne
              omega
          _ = (L.erase v).card * (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ = (L.card - 1) * (k - 1) := by rw [Finset.card_erase_of_mem hv]
      calc (∑ v ∈ L, ∑ w ∈ L.erase v,
              (agreementSet u v ∩ agreementSet u w).card)
          ≤ ∑ _v ∈ L, (L.card - 1) * (k - 1) := Finset.sum_le_sum h_inner
        _ = L.card * ((L.card - 1) * (k - 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = L.card * (L.card - 1) * (k - 1) := by ring
  -- Combine.
  rw [h_Q_expansion, h_diag_offdiag]
  exact Nat.add_le_add h_diag_le h_offdiag_le

/-- J6-δ (final arithmetic): combining (α), (β), (γ) yields `|L| ≤ n²`.

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
contains at most `n²` codewords. Composes the four atomic helpers
`johnson_S_lower_bound` (α), `johnson_cauchy_schwarz` (β),
`johnson_Q_upper_bound` (γ), and `johnson_final_arithmetic` (δ).

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
  -- Main case k ≥ 1: apply the four helpers.
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
  -- (α) S lower bound.
  have h_alpha : L.card * (n - τ) ≤
      ∑ x : Fin n, (L.filter (fun v => v x = u x)).card :=
    johnson_S_lower_bound τ u L hL_in_ball
  -- (β) Cauchy-Schwarz.
  have h_beta :
      (∑ x : Fin n, (L.filter (fun v => v x = u x)).card) ^ 2 ≤
        n * ∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2 :=
    johnson_cauchy_schwarz u L
  -- (γ) Q upper bound.
  have h_gamma :
      ∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2 ≤
        n * L.card + L.card * (L.card - 1) * (k - 1) :=
    johnson_Q_upper_bound h_MDS u L hL_in_c
  -- Chain α + β + γ to a single Cauchy-Schwarz inequality on Lcard.
  have h_chain : (L.card * (n - τ))^2 ≤
      n * (n * L.card + L.card * (L.card - 1) * (k - 1)) := by
    calc (L.card * (n - τ))^2
        ≤ (∑ x : Fin n, (L.filter (fun v => v x = u x)).card) ^ 2 :=
          Nat.pow_le_pow_left h_alpha _
      _ ≤ n * ∑ x : Fin n, ((L.filter (fun v => v x = u x)).card) ^ 2 := h_beta
      _ ≤ n * (n * L.card + L.card * (L.card - 1) * (k - 1)) :=
          Nat.mul_le_mul_left n h_gamma
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
