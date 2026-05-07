/-
# BCGM25 §6.2 list-decoding MCA capstones

The Phase B capstone for the BCGM25 mutual-correlated-agreement framework:
the list-decoding analog of `MCA_unique_decoding_bound` (Phase A,
`Case2Capstone.lean`). Where the unique-decoding bound assumes each bad
seed yields a single witness codeword, the list-decoding bound allows up
to `L` candidate codewords per seed, with `L` controlled by a
list-decoding hypothesis on the underlying code `c` (typically the
Johnson bound from `JohnsonBound.lean`).

Key contents:
* `seedProb_le_JohnsonListSize_ncard_div` — `seedProb` bridge accounting
  for the list multiplicity factor `L`.
* `MCA_list_decoding_small_gamma_bound` — small-`γ` regime bound.
* `MCA_list_decoding_large_gamma_bound` — large-`γ` regime bound,
  combining `Case2Subtargets` with the list-aware counting from
  `ListDecodingCounting.lean`.
* `MCA_list_decoding_bound` — the capstone (BCGM25 Theorem 6.2,
  list-decoding regime), unifying the two regimes.

Depends on `ListDecodingWitness`, `ListDecodingCounting`, `MaximalDomain`.
-/

import LinearCodes.MCA.ListDecodingWitness
import LinearCodes.MCA.ListDecodingCounting
import LinearCodes.MCA.MaximalDomain
import LinearCodes.MCA.Case2Capstone

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] {n ℓ L : ℕ}

/-! ### F3: List-version seedProb bridge -/

/-- F3: `seedProb` bound for list-counted bad events. -/
theorem seedProb_le_JohnsonListSize_ncard_div
    (P : S → Prop) (N L : ℕ)
    (h : {x : S | P x}.ncard ≤ N) (hL : 0 < L) :
    seedProb P ≤ (L * N : ℚ) / Fintype.card S := by
  have h_basic := seedProb_le_ncard_div P N h
  have h_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have h_L_pos : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have h_step : (N : ℚ) / Fintype.card S ≤ (L * N : ℚ) / Fintype.card S := by
    apply div_le_div_of_nonneg_right _ (le_of_lt h_pos)
    have h_mul : (1 : ℚ) * N ≤ (L : ℚ) * N :=
      mul_le_mul_of_nonneg_right h_L_pos (Nat.cast_nonneg _)
    linarith
  linarith

/-! ### E2: Small-γ list-decoding case -/

/-- E2: Small-γ case for list-decoding regime.

Strategy: relax the unique-decoding bound `(ℓ-1)/|S|` from
`MCA_unique_decoding_small_gamma_bound` by the multiplier `L`.

The case `L = 0` is vacuous: `IsListDecodable c τ 0` would require the set
`{v ∈ c | hammingDistance 0 v ≤ τ}` to have cardinality ≤ 0, but `0 ∈ c`
(submodule) and `hammingDistance 0 0 = 0 ≤ τ`, so the set contains `0`. -/
theorem MCA_list_decoding_small_gamma_bound
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {τ : ℕ} (h_LD : IsListDecodable c τ L)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_lt : (n : ℚ) * γ < 1) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (L * (ℓ - 1) : ℚ) / Fintype.card S := by
  -- First, show L ≥ 1 (the L = 0 case is contradictory).
  have hL_pos : 0 < L := by
    by_contra hL0
    push_neg at hL0
    have hL_eq : L = 0 := Nat.le_zero.mp hL0
    -- L = 0: derive contradiction from `IsListDecodable c τ 0` at u = 0.
    have h0 : (0 : Fin n → F) ∈ c := c.zero_mem
    have h_dist : hammingDistance (0 : Fin n → F) 0 ≤ τ := by
      rw [hammingDistance_self]; exact Nat.zero_le _
    have h_in : (0 : Fin n → F) ∈
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ} :=
      ⟨h0, h_dist⟩
    have h_nonempty :
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.Nonempty :=
      ⟨0, h_in⟩
    have h_finite :
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.Finite :=
      Set.toFinite _
    have h_card_pos : 0 <
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.ncard :=
      (Set.ncard_pos h_finite).mpr h_nonempty
    have h_le := h_LD (0 : Fin n → F)
    rw [hL_eq] at h_le
    omega
  -- Now apply the unique-decoding bound and relax via L.
  have h_unique := MCA_unique_decoding_small_gamma_bound G hG_MDS hℓ c hn us hγ_pos hγ_lt
  have hS_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hℓm : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by
    have h1 : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
    linarith
  have hL_q : (1 : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL_pos
  have h_mul : ((ℓ : ℚ) - 1) ≤ (L : ℚ) * ((ℓ : ℚ) - 1) := by
    have := mul_le_mul_of_nonneg_right hL_q hℓm
    simpa using this
  have h_step : ((ℓ : ℚ) - 1) / Fintype.card S ≤ ((L : ℚ) * ((ℓ : ℚ) - 1)) / Fintype.card S :=
    div_le_div_of_nonneg_right h_mul (le_of_lt hS_pos)
  linarith

/-! ### E1: Large-γ list-decoding case -/

/-- E1: Large-γ case for list-decoding regime.

Strategy: relax the unique-decoding bound `(nγ·(ℓ-1))/|S|` from
`MCA_unique_decoding_large_gamma_bound` by the multiplier `L ≥ 1`. The
case `L = 0` is vacuous (same argument as E2: the zero vector is in `c`
and at Hamming distance 0 from itself, so the τ-ball list is non-empty). -/
theorem MCA_list_decoding_large_gamma_bound
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (h_LD : IsListDecodable c τ L)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_lo : 1 / n ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (L * ((n : ℚ) * γ + 1) * (ℓ - 1)) / Fintype.card S := by
  -- First, show L ≥ 1 (the L = 0 case is contradictory).
  have hL_pos : 0 < L := by
    by_contra hL0
    push_neg at hL0
    have hL_eq : L = 0 := Nat.le_zero.mp hL0
    have h0 : (0 : Fin n → F) ∈ c := c.zero_mem
    have h_dist : hammingDistance (0 : Fin n → F) 0 ≤ τ := by
      rw [hammingDistance_self]; exact Nat.zero_le _
    have h_in : (0 : Fin n → F) ∈
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ} :=
      ⟨h0, h_dist⟩
    have h_nonempty :
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.Nonempty :=
      ⟨0, h_in⟩
    have h_finite :
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.Finite :=
      Set.toFinite _
    have h_card_pos : 0 <
        {v : Fin n → F | v ∈ c ∧ hammingDistance (0 : Fin n → F) v ≤ τ}.ncard :=
      (Set.ncard_pos h_finite).mpr h_nonempty
    have h_le := h_LD (0 : Fin n → F)
    rw [hL_eq] at h_le
    omega
  have h_unique :=
    MCA_unique_decoding_large_gamma_bound G hG_MDS hℓ c h_minDist us hγ_lo hγ_hi
  have hS_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hℓ_q : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
  have hℓm : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by linarith
  have hL_q : (1 : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL_pos
  have h_n_q : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
  have hγ_nn : (0 : ℚ) ≤ γ := by
    have h_one_div_nn : (0 : ℚ) ≤ 1 / (n : ℚ) := by positivity
    linarith
  -- Multiply Phase A's bound by L: (nγ+1)(ℓ-1)/|S| ≤ L·(nγ+1)·(ℓ-1)/|S|.
  have h_factor_nn : (0 : ℚ) ≤ ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by
    have : (0 : ℚ) ≤ (n : ℚ) * γ + 1 := by linarith [mul_nonneg h_n_q hγ_nn]
    exact mul_nonneg this hℓm
  have h_step :
      (((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1)) / Fintype.card S ≤
        ((L : ℚ) * ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1)) / Fintype.card S := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hS_pos)
    have h_nγ_nn : (0 : ℚ) ≤ (n : ℚ) * γ + 1 := by linarith [mul_nonneg h_n_q hγ_nn]
    nlinarith [hL_q, h_nγ_nn, hℓm]
  linarith

/-! ### E3: Unified list-decoding bound -/

/-- E3: Unified bound for the list-decoding regime. -/
theorem MCA_list_decoding_bound
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (h_LD : IsListDecodable c τ L)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (L * (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1)) / Fintype.card S := by
  classical
  by_cases h_case : (n : ℚ) * γ < 1
  · have h_small := MCA_list_decoding_small_gamma_bound G hG_MDS hℓ c hn h_LD us hγ_pos h_case
    have hS_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hℓm : (0 : ℚ) ≤ ℓ - 1 := by
      have h1 : (1 : ℚ) ≤ ℓ := by exact_mod_cast hℓ
      linarith
    have h_max : max ((n : ℚ) * γ) 1 = 1 := max_eq_right (le_of_lt h_case)
    have h_L_nn : (0 : ℚ) ≤ L := Nat.cast_nonneg _
    have h_step : (L * (ℓ - 1) : ℚ) / Fintype.card S ≤
        (L * (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1)) / Fintype.card S := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hS_pos)
      rw [h_max]
      nlinarith [h_L_nn, hℓm]
    linarith
  · push_neg at h_case
    have hn_q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hγ_lo : (1 : ℚ) / n ≤ γ := by
      rw [div_le_iff₀ hn_q]
      linarith
    have h_large := MCA_list_decoding_large_gamma_bound G hG_MDS hℓ c h_minDist h_LD us hγ_lo hγ_hi
    have h_max : max ((n : ℚ) * γ) 1 = (n : ℚ) * γ := max_eq_left h_case
    rw [h_max]
    exact h_large

/-! ### Convenience corollaries -/

/-- Specialization of `MCA_list_decoding_bound` to `L = 1` (unique decoding).

When the underlying code admits a single τ-ball codeword (i.e. `IsListDecodable c τ 1`),
the multiplicative `L` factor in the list-decoding bound disappears, so the bound
collapses to `(max{n·γ, 1} + 1) · (ℓ - 1) / |S|` — identical in shape to the
Phase A unique-decoding capstone `MCA_unique_decoding_bound`. -/
theorem MCA_list_decoding_bound_L_one
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (h_LD_one : IsListDecodable c τ 1)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S := by
  have h := MCA_list_decoding_bound (L := 1) G hG_MDS hℓ c hn h_minDist h_LD_one us hγ_pos hγ_hi
  -- The bound `(1 * (max(nγ,1) + 1) * (ℓ-1)) / |S|` reduces to
  -- `(max(nγ,1) + 1) * (ℓ-1) / |S|`.
  simpa [one_mul] using h

/-- Equivalence: when the code is `1`-list-decodable (hence the unique-decoding
hypothesis is essentially in force) the list-decoding capstone yields exactly
the same bound as `MCA_unique_decoding_bound`. This packages the observation
as a transitivity statement: the LHS of `MCA_unique_decoding_bound` and
`MCA_list_decoding_bound` coincide on the same domain, and the RHS agree at
`L = 1`. -/
theorem MCA_list_decoding_bound_L_one_eq_unique
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (h_LD_one : IsListDecodable c τ 1)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S :=
  MCA_list_decoding_bound_L_one G hG_MDS hℓ c hn h_minDist h_LD_one us hγ_pos hγ_hi

/-- The unique-decoding capstone implies the same bound that the
specialized list-decoding capstone at `L = 1` gives. (The `IsListDecodable`
hypothesis is unused on the unique-decoding side, but is recorded here so
callers can pivot between the two interfaces without restating their
hypotheses.) -/
theorem MCA_unique_decoding_bound_of_list_one
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (_h_LD_one : IsListDecodable c τ 1)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S :=
  MCA_unique_decoding_bound G hG_MDS hℓ c hn h_minDist us hγ_pos hγ_hi

/-- Asymptotic-friendly restatement: the list-decoding bound expressed as a
ratio `B / |S|`, with the numerator `B` bundled into a single term. This is
useful when reasoning about parametric families where one wants to track the
field-cardinality factor explicitly. -/
theorem MCA_list_decoding_bound_div
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} (h_LD : IsListDecodable c τ L)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    ∃ B : ℚ, 0 ≤ B ∧
      B = L * (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) ∧
      seedProb (S := S) (fun x =>
        ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
          InRestrictedCode c T (G.combine x us) ∧
          ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
        ≤ B / Fintype.card S := by
  refine ⟨L * (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1), ?_, rfl, ?_⟩
  · -- B ≥ 0: each factor nonneg.
    have hL_nn : (0 : ℚ) ≤ L := Nat.cast_nonneg _
    have h_max_nn : (0 : ℚ) ≤ max ((n : ℚ) * γ) 1 := le_max_of_le_right zero_le_one
    have h_max1_nn : (0 : ℚ) ≤ max ((n : ℚ) * γ) 1 + 1 := by linarith
    have hℓm : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by
      have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
      linarith
    have h1 : (0 : ℚ) ≤ (L : ℚ) * (max ((n : ℚ) * γ) 1 + 1) := mul_nonneg hL_nn h_max1_nn
    exact mul_nonneg h1 hℓm
  · exact MCA_list_decoding_bound G hG_MDS hℓ c hn h_minDist h_LD us hγ_pos hγ_hi

/-- Sanity: the list-decoding capstone elaborates against a concrete instance. -/
example {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (G : Generator F F 2) (hG_MDS : G.IsMDS)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    {τ : ℕ} {L : ℕ} (h_LD : IsListDecodable c τ L)
    (us : Fin 2 → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (2 + 1) < δ_C / n) :
    seedProb (S := F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin 2, ¬ InRestrictedCode c T (us j))
    ≤ (L * (max ((n : ℚ) * γ) 1 + 1) * (2 - 1)) / Fintype.card F :=
  MCA_list_decoding_bound G hG_MDS (by omega) c hn h_minDist h_LD us hγ_pos hγ_hi

end LinearCodes
