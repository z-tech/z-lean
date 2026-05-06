/-
# List-decoding counting bounds

Group D of the BCGM25 §6.2 decomposition. The list versions of the
double-counting infrastructure that powers Lemma 5.3 (large-`T̃` bound)
and the degree bound at coordinates outside the maximal agreement set.

Key contents:
* `list_strict_superset_count_bound` — multiplicity-aware generalization
  of `strict_superset_count_bound`: counts seed-list pairs `(i, k)`
  whose witness set strictly contains a fixed `A`, giving a bound of
  the shape `t·L ≤ (ℓ' − 1)·L · (|α| − |A|)`.
* `bad_pair_count_per_coord_le_list` — per-coordinate degree bound on
  bad seed-list pairs.
* `exists_Ttilde_choose_card_large` — produces a "large" maximal
  agreement set `T̃` together with a choice function selecting one
  candidate codeword per seed.
* `degree_bound_at_non_Ttilde_list` — degree bound at coordinates
  outside `T̃`.

Depends on `LinearCodes.MCA.ListDecodingCstars`,
`LinearCodes.MCA.ListDecodingDomains`, and
`Mathlib.Combinatorics.Pigeonhole`.
-/

import LinearCodes.MCA.ListDecodingCstars
import LinearCodes.MCA.ListDecodingDomains
import Mathlib.Combinatorics.Pigeonhole

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ L : ℕ}

/-! ### D1: Multiplicity-aware strict_superset_count_bound -/

/-- D1: Generalize `strict_superset_count_bound` to count seed-list pairs. -/
theorem list_strict_superset_count_bound {α : Type*} [Fintype α] [DecidableEq α]
    {ℓ' t L : ℕ} (hℓ : 1 ≤ ℓ')
    (A : Finset α) (Bs : Fin t → Fin L → Finset α)
    (h_strict : ∀ i k, A ⊂ Bs i k)
    (h_degree : ∀ j ∉ A,
      ((Finset.univ : Finset (Fin t × Fin L)).filter
        (fun p => j ∈ Bs p.1 p.2)).card ≤ (ℓ' - 1) * L) :
    t * L ≤ (ℓ' - 1) * L * (Fintype.card α - A.card) := by
  -- Direct double-counting over pairs (p, j) with j ∈ Bs p.1 p.2 \ A.
  set P : Finset (Fin t × Fin L) := Finset.univ with hP_def
  have hP_card : P.card = t * L := by
    rw [hP_def, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have h_subset_A : A ⊆ (Finset.univ : Finset α) := Finset.subset_univ A
  have h_compl_card :
      ((Finset.univ : Finset α) \ A).card = Fintype.card α - A.card := by
    rw [Finset.card_sdiff_of_subset h_subset_A, Finset.card_univ]
  -- LHS rewrite: filter cardinality as sum of indicators.
  have h_lhs_card : ∀ j : α,
      (P.filter fun p : Fin t × Fin L => j ∈ Bs p.1 p.2).card =
        ∑ p ∈ P, (if j ∈ Bs p.1 p.2 then 1 else 0 : ℕ) := by
    intro j
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  -- RHS rewrite: |Bs p.1 p.2 \ A| as a sum of indicators over j ∉ A.
  have h_rhs_card : ∀ p : Fin t × Fin L,
      (Bs p.1 p.2 \ A).card =
        ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (if j ∈ Bs p.1 p.2 then 1 else 0 : ℕ) := by
    intro p
    rw [show (Bs p.1 p.2 \ A) =
            ((Finset.univ : Finset α) \ A).filter (fun j => j ∈ Bs p.1 p.2) from ?_,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  -- Double counting identity.
  have h_double :
      ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (P.filter fun p : Fin t × Fin L => j ∈ Bs p.1 p.2).card =
        ∑ p ∈ P, (Bs p.1 p.2 \ A).card := by
    simp_rw [h_lhs_card, h_rhs_card]
    rw [Finset.sum_comm]
  -- Upper bound via degree hypothesis.
  have h_bound_top :
      ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (P.filter fun p : Fin t × Fin L => j ∈ Bs p.1 p.2).card ≤
        (ℓ' - 1) * L * (Fintype.card α - A.card) := by
    calc ∑ j ∈ ((Finset.univ : Finset α) \ A),
            (P.filter fun p : Fin t × Fin L => j ∈ Bs p.1 p.2).card
        ≤ ∑ _j ∈ ((Finset.univ : Finset α) \ A), (ℓ' - 1) * L := by
            apply Finset.sum_le_sum
            intros j hj
            rw [Finset.mem_sdiff] at hj
            exact h_degree j hj.2
      _ = ((Finset.univ : Finset α) \ A).card * ((ℓ' - 1) * L) := by
            rw [Finset.sum_const]; rfl
      _ = (Fintype.card α - A.card) * ((ℓ' - 1) * L) := by rw [h_compl_card]
      _ = (ℓ' - 1) * L * (Fintype.card α - A.card) := by ring
  -- Lower bound: each Bs p.1 p.2 \ A is nonempty (strict superset).
  have h_bound_bot : t * L ≤ ∑ p ∈ P, (Bs p.1 p.2 \ A).card := by
    have h1 : ∀ p ∈ P, 1 ≤ (Bs p.1 p.2 \ A).card := by
      intros p _
      obtain ⟨j, hj_in, hj_not⟩ := Finset.exists_of_ssubset (h_strict p.1 p.2)
      exact Finset.Nonempty.card_pos
        ⟨j, Finset.mem_sdiff.mpr ⟨hj_in, hj_not⟩⟩
    calc t * L = P.card := hP_card.symm
      _ = ∑ _p ∈ P, (1 : ℕ) := by rw [Finset.sum_const]; simp
      _ ≤ ∑ p ∈ P, (Bs p.1 p.2 \ A).card :=
            Finset.sum_le_sum h1
  calc t * L ≤ ∑ p ∈ P, (Bs p.1 p.2 \ A).card := h_bound_bot
    _ = ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (P.filter fun p : Fin t × Fin L => j ∈ Bs p.1 p.2).card :=
        h_double.symm
    _ ≤ (ℓ' - 1) * L * (Fintype.card α - A.card) := h_bound_top

/-! ### D2: Per-coord list count bound -/

/-- D2: For coord `i ∉ Ttilde_choose`, count of bad seeds with combine-equality
at `i` is bounded by `(ℓ-1) · L`. -/
theorem bad_pair_count_per_coord_le_list
    [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    (choose : Fin ℓ → Fin L)
    (B_set : Finset S)
    {i : Fin n} (hi_notT : i ∉ Ttilde_choose us cstars_fam choose) :
    ((B_set.filter
      (fun x => G.combine x us i = G.combine x (cstars_fam choose) i)).card : ℚ)
      ≤ (ℓ - 1 : ℚ) := by
  classical
  let cstars := cstars_fam choose
  let Ttilde : Finset (Fin n) :=
    Finset.univ.filter (fun i' => ∀ j, us j i' = cstars j i')
  have hTtilde_def : ∀ i', i' ∈ Ttilde ↔ ∀ j, us j i' = cstars j i' := by
    intro i'; simp [Ttilde]
  have hi_notTtilde : i ∉ Ttilde := by
    rw [show Ttilde = Ttilde_choose us cstars_fam choose from rfl]
    exact hi_notT
  exact bad_pair_count_per_coord_le hG_MDS hℓ us cstars Ttilde hTtilde_def B_set hi_notTtilde

/-! ### D3: List version of Lemma 5.3 -/

/-- D3: There exists a choice function for which `Ttilde_choose` has size
`≥ n(1-γ) - 1`.

STRATEGY (Strategy A, hypothesis strengthened by `L^(ℓ-1)`):
The natural pigeonhole strategy assigns each `x ∈ B_set` to some
`choose(x) : Fin ℓ → Fin L` via `Classical.choose` on `h_agree`, then
selects the most-popular fiber `B' ⊆ B_set` with size `> (nγ+1)(ℓ-1)`,
and applies Phase A's `Ttilde_card_gt_of_MDS_aggregate` to that `B'`
with `cstars := cstars_fam choose₀` (where `choose₀` is the popular choice).
Pigeonhole over the codomain of size `L^ℓ` therefore requires
`|B_set| > L^ℓ · (nγ+1)(ℓ-1)` — a factor of `L^(ℓ-1)` stronger than the
naive `L · (nγ+1)(ℓ-1)` bound suggested by D1's pair-counting form.

TRADE-OFF: a tighter (and harder) approach would inline a list-aware
aggregate count that works directly over the parameterized family
`cstars_fam` without restricting to a single fiber. We take the
simpler strengthened-hypothesis route here. -/
theorem exists_Ttilde_choose_card_large
    [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hn : 0 < n)
    (B_set : Finset S)
    (h_size : (B_set.card : ℚ) > ((n : ℚ) * γ + 1) * (ℓ - 1) * (L : ℚ) ^ ℓ)
    (h_agree : ∀ x ∈ B_set, ∃ choose : Fin ℓ → Fin L, ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x (cstars_fam choose) i) :
    ∃ choose : Fin ℓ → Fin L,
      ((Ttilde_choose us cstars_fam choose).card : ℚ) ≥ n * (1 - γ) - 1 := by
  classical
  -- Setup: cast helpers.
  have hℓ_Q : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
  have hℓ_sub_nn : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by linarith
  have hn_Q : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
  have hnγ1_pos : (0 : ℚ) < (n : ℚ) * γ + 1 := by
    have : (0 : ℚ) ≤ (n : ℚ) * γ := mul_nonneg hn_Q hγ_pos
    linarith
  have hnγ1_nn : (0 : ℚ) ≤ (n : ℚ) * γ + 1 := le_of_lt hnγ1_pos
  have h_factor_nn : (0 : ℚ) ≤ ((n : ℚ) * γ + 1) * (ℓ - 1) :=
    mul_nonneg hnγ1_nn hℓ_sub_nn
  have hL_pow_nn : (0 : ℚ) ≤ (L : ℚ) ^ ℓ :=
    pow_nonneg (by exact_mod_cast Nat.zero_le L) ℓ
  -- B_set is nonempty: B_set.card ≥ 1 (else h_size : 0 > nonneg, contradiction).
  have hB_pos : 0 < B_set.card := by
    rcases Nat.eq_zero_or_pos B_set.card with hc | hc
    · exfalso
      rw [hc] at h_size
      simp at h_size
      have : ((n : ℚ) * γ + 1) * (ℓ - 1) * (L : ℚ) ^ ℓ ≥ 0 :=
        mul_nonneg h_factor_nn hL_pow_nn
      linarith
    · exact hc
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hB_pos
  -- Inhabit `Fin ℓ → Fin L` using the witness from `h_agree x₀`.
  obtain ⟨choose₀_default, _, _, _⟩ := h_agree x₀ hx₀
  haveI : Nonempty (Fin ℓ → Fin L) := ⟨choose₀_default⟩
  -- Define the choice function f : S → (Fin ℓ → Fin L).
  let f : S → (Fin ℓ → Fin L) := fun x =>
    if hx : x ∈ B_set then (h_agree x hx).choose else choose₀_default
  -- For x ∈ B_set, f x is a witness from h_agree.
  have hf_witness : ∀ x ∈ B_set, ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x (cstars_fam (f x)) i := by
    intro x hx
    have h_spec := (h_agree x hx).choose_spec
    have hfx : f x = (h_agree x hx).choose := by simp [f, hx]
    rw [hfx]
    exact h_spec
  -- Apply pigeonhole. Codomain has cardinality L^ℓ.
  set t : Finset (Fin ℓ → Fin L) := (Finset.univ : Finset (Fin ℓ → Fin L)) with ht_def
  have ht_card : t.card = L ^ ℓ := by
    rw [ht_def, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hf_maps : ∀ x ∈ B_set, f x ∈ t := fun x _ => Finset.mem_univ _
  -- Pigeonhole hypothesis (over ℚ): (#t) • A < (#B_set) where A = (nγ+1)(ℓ-1).
  have h_pigeon_hyp : (t.card : ℕ) • (((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1)) <
      (B_set.card : ℚ) := by
    rw [nsmul_eq_mul, ht_card]
    push_cast
    -- Goal: (L : ℚ) ^ ℓ * ((n*γ+1)*(ℓ-1)) < B_set.card
    linarith
  -- Apply pigeonhole (ℚ-valued head version) to get choose₀ with fiber > A.
  obtain ⟨choose₀, _, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hf_maps h_pigeon_hyp
  -- Define B' := preimage of choose₀ under f, restricted to B_set.
  set B' : Finset S := B_set.filter (fun x => f x = choose₀) with hB'_def
  have hB'_sub : B' ⊆ B_set := Finset.filter_subset _ _
  have hB'_size : (B'.card : ℚ) > ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := hfiber
  -- Build h_agree' for B' with cstars := cstars_fam choose₀.
  have h_agree' : ∀ x ∈ B', ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x (cstars_fam choose₀) i := by
    intro x hx
    rw [hB'_def, Finset.mem_filter] at hx
    obtain ⟨hx_B, hfx⟩ := hx
    obtain ⟨Tx, hTx_card, hTx_agree⟩ := hf_witness x hx_B
    refine ⟨Tx, hTx_card, ?_⟩
    intro i hi
    have := hTx_agree i hi
    rw [hfx] at this
    exact this
  -- Apply Phase A's `Ttilde_card_gt_of_MDS_aggregate` to (B', cstars_fam choose₀).
  set cstars : Fin ℓ → (Fin n → F) := cstars_fam choose₀ with hcstars_def
  set Ttilde : Finset (Fin n) := Ttilde_choose us cstars_fam choose₀ with hTtilde_def
  have h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i := by
    intro i
    rw [hTtilde_def, hcstars_def]
    exact mem_Ttilde_choose us cstars_fam choose₀ i
  have h_concl :
      (Ttilde.card : ℚ) ≥ n * (1 - γ) - 1 :=
    Ttilde_card_gt_of_MDS_aggregate hG_MDS hℓ us cstars hγ_pos hn B'
      h_agree' hB'_size Ttilde h_Ttilde_def
  exact ⟨choose₀, h_concl⟩

/-! ### D4: Degree bound for list version -/

/-- D4: For `j ∉ Ttilde_choose`, count of bad seeds with `j ∈ Bx` is `≤ (ℓ-1)·L`. -/
theorem degree_bound_at_non_Ttilde_list
    [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    (choose : Fin ℓ → Fin L)
    {γ : ℚ}
    {B_set : Finset S}
    (Bx : ∀ x ∈ B_set, Finset (Fin n))
    (h_Bx_eq : ∀ x (hx : x ∈ B_set), ∀ i ∈ Bx x hx,
      G.combine x us i = G.combine x (cstars_fam choose) i)
    (j : Fin n) (hj_notT : j ∉ Ttilde_choose us cstars_fam choose) :
    (B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx)).card ≤ ℓ - 1 := by
  -- Reduce to Phase A `degree_bound_at_non_Ttilde` with `cstars := cstars_fam choose`
  -- and `Ttilde := Ttilde_choose us cstars_fam choose`.
  set cstars : Fin ℓ → (Fin n → F) := cstars_fam choose with hcstars_def
  set Ttilde : Finset (Fin n) := Ttilde_choose us cstars_fam choose with hTtilde_def
  have h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j', us j' i = cstars j' i := by
    intro i
    rw [hTtilde_def, hcstars_def]
    exact mem_Ttilde_choose us cstars_fam choose i
  have hj_notTtilde : j ∉ Ttilde := by
    rw [hTtilde_def]; exact hj_notT
  exact degree_bound_at_non_Ttilde (γ := γ) hG_MDS hℓ us cstars Ttilde
    h_Ttilde_def Bx h_Bx_eq j hj_notTtilde

end LinearCodes
