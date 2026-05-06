/-
# List-decoding counting bounds

Group D of §6.2: list versions of Lemma 5.3 and the degree bound.
-/

import LinearCodes.MCA.ListDecodingCstars
import LinearCodes.MCA.ListDecodingDomains

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
`≥ n(1-γ) - 1`. -/
theorem exists_Ttilde_choose_card_large
    [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hn : 0 < n)
    (B_set : Finset S)
    (h_size : (B_set.card : ℚ) > ((n : ℚ) * γ + 1) * (ℓ - 1) * L)
    (h_agree : ∀ x ∈ B_set, ∃ choose : Fin ℓ → Fin L, ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x (cstars_fam choose) i) :
    ∃ choose : Fin ℓ → Fin L,
      ((Ttilde_choose us cstars_fam choose).card : ℚ) ≥ n * (1 - γ) - 1 := by
  sorry

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
