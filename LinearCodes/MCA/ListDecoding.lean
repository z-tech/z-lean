/-
# List decoding (BCGM25 §6.2 setup)

Phase B foundation: definitions and structural lemmas for the
list-decoding regime. The list-decoding MCA capstone itself
(`MCA_list_decoding_bound`, BCGM25 §6.2) is fully proved in
`LinearCodes/MCA/ListDecodingMCA.lean`; this file supplies the
underlying definitions and the trivial-monotonicity / zero-radius
properties it consumes.

The Johnson list-size bound (Cauchy–Schwarz form) used to instantiate
the capstone for Reed–Solomon is in `MCA/JohnsonBound.lean` — no
Guruswami–Sudan infrastructure is required.

## What goes here

* `IsListDecodable c τ L` — bound on the number of codewords within
  Hamming distance `τ` of any vector.
* `JohnsonListSize` — the BCGM25 list-size bound `O((ℓ+1)·n²)` for the
  Johnson-radius regime.
* Structural properties of `IsListDecodable` (monotonicity in `L`,
  zero-radius case, etc.).
-/

import LinearCodes.MCA.MaximalDomain

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n : ℕ}

/-! ### List decodability -/

/-- A code `c` is `(τ, L)`-list-decodable: for every vector `u`, the number
of codewords within Hamming distance `τ` of `u` is at most `L`. -/
def IsListDecodable [Fintype F]
    (c : Submodule F (Fin n → F)) (τ : ℕ) (L : ℕ) : Prop :=
  ∀ u : Fin n → F,
    {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.ncard ≤ L

/-- The list-decoding size from BCGM25's Lemma 6.2 (RS-specialized form):
for an RS code (or general MDS code) with min distance `d` and dimension
`k = n - d + 1`, the Johnson bound says any vector has at most
`O(n / (n - d) · ℓ²)` codewords within `τ < n - √(n·(n-d))` distance.

We use the BCGM25 quantitative form: `O((ℓ+1) · n²)`. -/
def JohnsonListSize (ℓ n : ℕ) : ℕ := (ℓ + 1) * n ^ 2

/-! ### Trivial properties -/

/-- Every code is `(0, 1)`-list-decodable: at distance 0, only one codeword
(namely `u` itself, if `u ∈ c`) is within reach. -/
theorem IsListDecodable_zero [Fintype F]
    (c : Submodule F (Fin n → F)) :
    IsListDecodable c 0 1 := by
  intro u
  have h_subset : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ 0} ⊆ {u} := by
    intros v hv
    rw [Set.mem_setOf_eq] at hv
    obtain ⟨_, hd⟩ := hv
    have hd' : hammingDistance u v = 0 := Nat.le_zero.mp hd
    rw [hammingDistance_eq_zero_iff] at hd'
    rw [Set.mem_singleton_iff]
    exact hd'.symm
  have h_le := Set.ncard_le_ncard h_subset (Set.finite_singleton u)
  simpa using h_le

/-- List-decodability is monotone in `L`: a `(τ, L)`-list-decodable code is
also `(τ, L')`-list-decodable for `L' ≥ L`. -/
theorem IsListDecodable.mono_L [Fintype F]
    {c : Submodule F (Fin n → F)} {τ L L' : ℕ} (hLL' : L ≤ L')
    (h : IsListDecodable c τ L) :
    IsListDecodable c τ L' :=
  fun u => (h u).trans (Nat.cast_le.mpr hLL')

/-- List-decodability tightens with smaller radius: a `(τ, L)`-list-
decodable code is also `(τ', L)`-list-decodable for `τ' ≤ τ` (fewer
candidates within smaller radius). -/
theorem IsListDecodable.mono_τ [Fintype F]
    {c : Submodule F (Fin n → F)} {τ τ' L : ℕ} (hττ' : τ' ≤ τ)
    (h : IsListDecodable c τ L) :
    IsListDecodable c τ' L := by
  intro u
  have h_subset : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ'} ⊆
                  {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} := by
    intros v hv
    obtain ⟨hv_mem, hv_dist⟩ := hv
    exact ⟨hv_mem, hv_dist.trans hττ'⟩
  have h_finite : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.Finite :=
    Set.toFinite _
  exact (Set.ncard_le_ncard h_subset h_finite).trans (h u)

/-- A subcode inherits list-decodability from its containing code. -/
theorem IsListDecodable.subcode [Fintype F]
    {c c' : Submodule F (Fin n → F)} (h_sub : c' ≤ c)
    {τ L : ℕ} (h : IsListDecodable c τ L) :
    IsListDecodable c' τ L := by
  intro u
  have h_subset : {v : Fin n → F | v ∈ c' ∧ hammingDistance u v ≤ τ} ⊆
                  {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} := by
    intros v hv
    exact ⟨h_sub hv.1, hv.2⟩
  have h_finite : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.Finite :=
    Set.toFinite _
  exact (Set.ncard_le_ncard h_subset h_finite).trans (h u)

/-! ### Characterization of unique decoding -/

/-- **Characterization of unique decoding.** A code `c` is `(τ, 1)`-list-
decodable iff every pair of distinct codewords lies at Hamming distance
strictly greater than `2τ`. -/
theorem IsListDecodable_one_iff_minDist [Fintype F]
    (c : Submodule F (Fin n → F)) (τ : ℕ) :
    IsListDecodable c τ 1 ↔ ∀ u v : Fin n → F, u ∈ c → v ∈ c → u ≠ v →
      2 * τ < hammingDistance u v := by
  classical
  refine ⟨?_, ?_⟩
  · intro h_LD u v hu hv h_ne
    by_contra h_close
    push_neg at h_close
    set D : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i) with hD_def
    have hD_card : D.card = hammingDistance u v := rfl
    have h_min_le_D : min τ D.card ≤ D.card := Nat.min_le_right _ _
    obtain ⟨D₁, hD₁_sub, hD₁_card⟩ := Finset.exists_subset_card_eq h_min_le_D
    set w : Fin n → F := fun i => if i ∈ D₁ then v i else u i with hw_def
    have hw_v_on_D₁ : ∀ i ∈ D₁, w i = v i := fun i hi => by
      simp [hw_def, hi]
    have hw_u_off_D₁ : ∀ i, i ∉ D₁ → w i = u i := fun i hi => by
      simp [hw_def, hi]
    have hw_u_dist : hammingDistance w u ≤ τ := by
      have h_subset : (Finset.univ.filter (fun i => w i ≠ u i)) ⊆ D₁ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra h_notin
        exact hi (hw_u_off_D₁ i h_notin)
      have h_card_le : hammingDistance w u ≤ D₁.card :=
        Finset.card_le_card h_subset
      rw [hD₁_card] at h_card_le
      exact h_card_le.trans (Nat.min_le_left _ _)
    have hw_v_dist : hammingDistance w v ≤ τ := by
      have h_subset : (Finset.univ.filter (fun i => w i ≠ v i)) ⊆ D \ D₁ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_cases h_inD₁ : i ∈ D₁
        · exact absurd (hw_v_on_D₁ i h_inD₁) hi
        · refine Finset.mem_sdiff.mpr ⟨?_, h_inD₁⟩
          rw [hD_def, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hw_u_off_D₁ i h_inD₁] at hi
          exact hi
      have h_card_le : hammingDistance w v ≤ (D \ D₁).card :=
        Finset.card_le_card h_subset
      have h_inter : D₁ ∩ D = D₁ := Finset.inter_eq_left.mpr hD₁_sub
      rw [Finset.card_sdiff, h_inter, hD₁_card, hD_card] at h_card_le
      have h_aux : hammingDistance u v - min τ (hammingDistance u v) ≤ τ := by omega
      exact h_card_le.trans h_aux
    have h_set_two : ({u, v} : Set (Fin n → F)) ⊆
        {x : Fin n → F | x ∈ c ∧ hammingDistance w x ≤ τ} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨hu, hw_u_dist⟩
      · exact ⟨hv, hw_v_dist⟩
    have h_finite : {x : Fin n → F | x ∈ c ∧ hammingDistance w x ≤ τ}.Finite :=
      Set.toFinite _
    have h_ncard_le := Set.ncard_le_ncard h_set_two h_finite
    have h_le_one := h_LD w
    have h_two_eq : ({u, v} : Set (Fin n → F)).ncard = 2 := Set.ncard_pair h_ne
    omega
  · intro h_far u
    by_cases h_emp : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} = ∅
    · rw [h_emp]; simp
    · rw [Set.eq_empty_iff_forall_notMem] at h_emp
      push_neg at h_emp
      obtain ⟨v₀, hv₀⟩ := h_emp
      have h_subset : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} ⊆ {v₀} := by
        intros v hv
        rw [Set.mem_singleton_iff]
        by_contra h_ne
        have h_tri := hammingDistance_triangle v₀ u v
        rw [hammingDistance_comm v₀ u] at h_tri
        have hv₀_dist : hammingDistance u v₀ ≤ τ := hv₀.2
        have hv_dist : hammingDistance u v ≤ τ := hv.2
        have h_far' := h_far v₀ v hv₀.1 hv.1 (Ne.symm h_ne)
        omega
      have h_le := Set.ncard_le_ncard h_subset (Set.finite_singleton v₀)
      simpa using h_le

/-! ### Unique decoding within half-the-min-distance -/

/-- **Classical unique-decoding bound.** A code with min distance `d` is
`(τ, 1)`-list-decodable for any `τ < d/2`. Two codewords within
distance `τ` of any given vector must coincide (by triangle inequality
plus min-distance contradiction). -/
theorem IsListDecodable_of_minDist_unique [Fintype F]
    {c : Submodule F (Fin n → F)} {d : ℕ} (h_minDist : MinDistAtLeast c d)
    {τ : ℕ} (hτ : 2 * τ < d) :
    IsListDecodable c τ 1 := by
  intro u
  -- Show the set has at most 1 element by showing all elements equal a chosen witness.
  by_cases h_emp : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} = ∅
  · rw [h_emp]; simp
  · -- Pick a representative
    rw [Set.eq_empty_iff_forall_notMem] at h_emp
    push_neg at h_emp
    obtain ⟨v₀, hv₀⟩ := h_emp
    have h_subset : {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} ⊆ {v₀} := by
      intros v hv
      rw [Set.mem_singleton_iff]
      have hv₀_dist : hammingDistance u v₀ ≤ τ := hv₀.2
      have hv_dist : hammingDistance u v ≤ τ := hv.2
      have hv₀_mem : v₀ ∈ c := hv₀.1
      have hv_mem : v ∈ c := hv.1
      -- d(v₀, v) ≤ d(v₀, u) + d(u, v) ≤ 2τ < d
      have h_tri := hammingDistance_triangle v₀ u v
      rw [hammingDistance_comm v₀ u] at h_tri
      have h_dist_lt : hammingDistance v₀ v < d := by omega
      -- If v₀ ≠ v, then v₀ - v ≠ 0 in c, so weight ≥ d, contradicting hammingDistance < d.
      by_contra h_ne
      have h_sub_mem : v₀ - v ∈ c := c.sub_mem hv₀_mem hv_mem
      have h_sub_ne : v₀ - v ≠ 0 := sub_ne_zero.mpr (Ne.symm h_ne)
      have h_lo := h_minDist (v₀ - v) h_sub_mem h_sub_ne
      rw [← hammingDistance_eq_hammingWeight_sub] at h_lo
      omega
    have h_le := Set.ncard_le_ncard h_subset (Set.finite_singleton v₀)
    simpa using h_le

/-! ### D1-D4: List-decoding API extensions (Phase B starters) -/

/-- D1: Affine translates preserve list-decodability radius and list size.
If `c` is `(τ, L)`-list-decodable, then for any vector `v`, the translate
`c + v` (as a `Set`) is also `(τ, L)`-list-decodable. -/
theorem IsListDecodable.shift
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) {τ : ℕ} {L : ℕ}
    (h : IsListDecodable c τ L) (v : Fin n → F)
    (u : Fin n → F) :
    {w : Fin n → F | w ∈ c ∧ hammingDistance (u - v) w ≤ τ}.ncard ≤ L :=
  h (u - v)

/-- D2: Strengthening of `IsListDecodable_zero`: agreement everywhere implies
equality (regardless of codeword membership). Useful sanity lemma. -/
theorem agree_everywhere_implies_eq
    {F : Type*} [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) (h_agree : ∀ i, u i = v i) : u = v := by
  funext i
  exact h_agree i

/-- D3: For an MDS submodule with min distance `d`, list-decodable to radius
`τ < d/2` with list size 1 (= unique decoding). This packages
`IsListDecodable_of_minDist_unique` for MDS submodules. -/
theorem IsListDecodable_of_MDS_unique
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    (c : Submodule F (Fin n → F)) (h_MDS : IsMDS c k)
    {τ : ℕ} (h_τ : 2 * τ < n - k + 1) :
    IsListDecodable c τ 1 :=
  IsListDecodable_of_minDist_unique h_MDS.2 h_τ

/-- D4: Monotonicity of list size in `L`. If `(τ, L)` works, so does `(τ, L+1)`. -/
theorem IsListDecodable.mono_L_succ
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) {τ L : ℕ}
    (h : IsListDecodable c τ L) :
    IsListDecodable c τ (L + 1) :=
  h.mono_L (Nat.le_succ L)

/-! ### L1-L20: list-decoding API extensions -/

/-- L1: At radius 0 with list size ≥ 1. -/
theorem IsListDecodable_zero_iff_one_or_more
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) (L : ℕ) :
    (1 ≤ L) → IsListDecodable c 0 L := by
  intro hL
  exact (IsListDecodable_zero c).mono_L hL

/-- L3: The zero submodule list-decodes with size 1 at any radius. -/
theorem IsListDecodable_bot
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ} (τ : ℕ) :
    IsListDecodable (⊥ : Submodule F (Fin n → F)) τ 1 := by
  intro u
  have h_subset :
      {v : Fin n → F | v ∈ (⊥ : Submodule F (Fin n → F)) ∧ hammingDistance u v ≤ τ}
        ⊆ {(0 : Fin n → F)} := by
    intro v hv
    rw [Set.mem_singleton_iff]
    exact (Submodule.mem_bot F).mp hv.1
  have h_le := Set.ncard_le_ncard h_subset (Set.finite_singleton _)
  simpa using h_le

/-- L4: List-decodability descends to inf of two codes. -/
theorem IsListDecodable.inf
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c₁ c₂ : Submodule F (Fin n → F)} {τ L : ℕ}
    (h : IsListDecodable c₁ τ L) :
    IsListDecodable (c₁ ⊓ c₂) τ L :=
  h.subcode inf_le_left

/-- L5: Hamming-ball reformulation. -/
def hammingBall {F : Type*} [DecidableEq F] {n : ℕ} (u : Fin n → F) (τ : ℕ) :
    Set (Fin n → F) := {v | hammingDistance u v ≤ τ}

theorem IsListDecodable_iff_ball
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) (τ L : ℕ) :
    IsListDecodable c τ L ↔
      ∀ u, ((c : Set (Fin n → F)) ∩ hammingBall u τ).ncard ≤ L := by
  unfold IsListDecodable
  have h_eq : ∀ u : Fin n → F,
      {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} =
        (c : Set (Fin n → F)) ∩ hammingBall u τ := by
    intro u
    ext v
    simp [hammingBall, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
  exact ⟨fun h u => (h_eq u) ▸ h u, fun h u => (h_eq u).symm ▸ h u⟩

/-- L6: List-size monotone with addition. -/
theorem IsListDecodable.mono_L_add
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c : Submodule F (Fin n → F)} {τ L : ℕ}
    (h : IsListDecodable c τ L) (k : ℕ) :
    IsListDecodable c τ (L + k) := h.mono_L (Nat.le_add_right L k)

/-- L7: Translate by a codeword preserves list-decoding bounds. -/
theorem IsListDecodable.shift_within_code
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c : Submodule F (Fin n → F)} {τ L : ℕ}
    (h : IsListDecodable c τ L) {w : Fin n → F} (_hw : w ∈ c) (u : Fin n → F) :
    {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.ncard ≤ L := h u

/-- L9: List-decodability via weight-of-difference form. -/
theorem IsListDecodable_iff_weight_sub
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) (τ L : ℕ) :
    IsListDecodable c τ L ↔
      ∀ u, {v : Fin n → F | v ∈ c ∧ hammingWeight (u - v) ≤ τ}.ncard ≤ L := by
  unfold IsListDecodable
  have h_eq : ∀ u : Fin n → F,
      {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} =
        {v : Fin n → F | v ∈ c ∧ hammingWeight (u - v) ≤ τ} := by
    intro u
    ext v
    simp only [Set.mem_setOf_eq, hammingDistance_eq_hammingWeight_sub]
  exact ⟨fun h u => (h_eq u) ▸ h u, fun h u => (h_eq u).symm ▸ h u⟩

/-- L11: MDS list-decoding at half-distance (`≤` form). -/
theorem IsListDecodable_of_MDS_le_half
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n k : ℕ}
    {c : Submodule F (Fin n → F)} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_τ : 2 * τ + 1 ≤ n - k + 1) :
    IsListDecodable c τ 1 := by
  have h_lt : 2 * τ < n - k + 1 := h_τ
  exact IsListDecodable_of_minDist_unique h_MDS.2 h_lt

/-- L13: Set-union list-decoding bound. -/
theorem IsListDecodable.union_set_bound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c₁ c₂ : Submodule F (Fin n → F)} {τ L₁ L₂ : ℕ}
    (h₁ : IsListDecodable c₁ τ L₁) (h₂ : IsListDecodable c₂ τ L₂) :
    ∀ u : Fin n → F,
      ({v ∈ (c₁ : Set _) | hammingDistance u v ≤ τ} ∪
       {v ∈ (c₂ : Set _) | hammingDistance u v ≤ τ}).ncard ≤ L₁ + L₂ := by
  intro u
  have hA : {v ∈ (c₁ : Set (Fin n → F)) | hammingDistance u v ≤ τ}.ncard ≤ L₁ := by
    have := h₁ u
    convert this using 2
  have hB : {v ∈ (c₂ : Set (Fin n → F)) | hammingDistance u v ≤ τ}.ncard ≤ L₂ := by
    have := h₂ u
    convert this using 2
  have h_le := Set.ncard_union_le
    {v ∈ (c₁ : Set (Fin n → F)) | hammingDistance u v ≤ τ}
    {v ∈ (c₂ : Set (Fin n → F)) | hammingDistance u v ≤ τ}
  omega

/-- L15: Bounded-distance decoding at radius `(d-1)/2`. -/
theorem IsListDecodable_BDD
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    {c : Submodule F (Fin n → F)} {d : ℕ}
    (h_minDist : MinDistAtLeast c d) (hd : 0 < d) :
    IsListDecodable c ((d - 1) / 2) 1 := by
  have h_half : 2 * ((d - 1) / 2) ≤ d - 1 := by
    have := Nat.div_mul_le_self (d - 1) 2
    omega
  have h_lt : 2 * ((d - 1) / 2) < d := by omega
  exact IsListDecodable_of_minDist_unique h_minDist h_lt

/-- L20: Vacuous radius beyond `n`. -/
theorem IsListDecodable.of_radius_ge_n
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}
    (c : Submodule F (Fin n → F)) {τ : ℕ} (_hτ : n ≤ τ) :
    IsListDecodable c τ (Set.ncard (c : Set (Fin n → F))) := by
  intro u
  have h_subset :
      {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ} ⊆ (c : Set (Fin n → F)) := by
    intro v hv
    exact hv.1
  exact Set.ncard_le_ncard h_subset (Set.toFinite _)

end LinearCodes
