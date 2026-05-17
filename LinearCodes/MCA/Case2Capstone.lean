/-
# §6.1 Case 2 capstone: MCA unique-decoding large-γ bound

This file contains **BCGM25 Theorem 6.1 (unique-decoding regime)**, namely
`MCA_unique_decoding_bound`, together with its large-γ ingredient
`MCA_unique_decoding_large_gamma_bound` (the §6.1 Case 2 capstone). It wires
together the sub-targets from `Case2/` with the
maximal-agreement infrastructure from `MaximalDomain.lean` to prove the
weakened §6.1 Case 2 capstone:

## Naming crosswalk

Two unrelated case-numberings appear in this codebase. They look similar
but mean different things — don't confuse them.

* **Lean's "Case 1 / Case 2"** (this file, `Case2/`,
  `MCA_unique_decoding_small_gamma_bound` vs `_large_gamma_bound`):
  internal branching by `γ < 1/n` vs `γ ≥ 1/n` in the proof of
  Theorem 6.1. Both cases prove the *same* statement; the split is
  purely about which counting argument applies.
* **BCGM25 / BCIKS18 "case (a) / case (b)"** (in `RS/`
  as `rs_MCA_caseA`): the paper-level distinction between the
  *structural* form of MCA (case (a): "∀ α gives δ-close combination ⇒
  MCA") and the *quantitative* form (case (b): the seed-probability
  bound). These are two *equivalent views* of the same theorem
  (BCIKS18 Thm 1.2 / BCGM25 Thm 9.2), not branches of one proof.

```
seedProb (...) ≤ ((n·γ + 1)·(ℓ-1)) / |S|
```

## Bound: integer-honest form vs BCGM25's real-number form

The Lean statements here yield `(n·γ + 1)·(ℓ-1)/|S|` (and the unified
Theorem 6.1 bound `(max{n·γ,1} + 1)·(ℓ-1)/|S|`), which is the
integer-tight lossless bound `|S| > M·(γn+1)` of BCH+25 (eprint 2025/2055)
Theorem 4.1 with `M = ℓ-1`; BCH+25 Remark 2.5 proves this matches an
explicit adversarial saturation. BCGM25's stated `n·γ·(ℓ-1)/|S|` is the
real-number form, sufficient only for the strict bad-seed shape
`{x : Δ_x = 0}`; for the Case 2 reduction's `B_set := {x : Δ_x ≤ nγ}`
it is genuinely insufficient (concrete counterexample in
`LinearCodes/MCA/Lemma53Examples.lean`).

The hypothesis-side analysis lives in
`Ttilde_card_gt_of_MDS_aggregate` (BCGM25 Lemma 5.3) — see its docstring,
plus `LinearCodes/doc/literature-survey-lemma-5-3.md` and
`LinearCodes/doc/lemma-5-3-numerical-analysis.md`. The `+1` is absorbed
identically into both the small-γ and large-γ branches via
`max_one_nGamma_relax_v2`.

## Why this file exists separately from `MaximalDomain.lean`

The two theorems live here, not in `MaximalDomain.lean`, to avoid a circular
import. `Case2/` imports `MaximalDomain.lean` for the
`IsCADomain`/`IsMaxAgreementDomain` predicates used by sub-target F (etc.),
so the capstone — which uses both `Case2.*` and `MaximalDomain` —
has to live strictly above both of them.
-/

import LinearCodes.MCA.MaximalDomain
import LinearCodes.MCA.Case2.Lemma53


-- File-level `variable` block is used by most theorems but legitimately
-- unused in a few. Suppression kept rather than narrowing per-theorem.
set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-! ### §6.1 Case 2: γ ≥ 1/n MCA bound -/

/-- **§6.1 Case 2 MCA bound.** For an MDS generator and
γ ∈ [1/n, δ_C/(ℓ+1)), the MCA bad-event probability is bounded by
`((n·γ + 1)·(ℓ-1))/|S|`.

This is the **integer-tight** lossless bound — matching BCH+25 (eprint
2025/2055) Theorem 4.1 with `M = ℓ-1`, proven tight in Remark 2.5.
BCGM25's stated `n·γ·(ℓ-1)/|S|` is the real-number form; for the
Case 2 reduction's bad-seed set `{x : Δ_x ≤ nγ}` it is insufficient
(see `LinearCodes/MCA/Lemma53Examples.lean`). -/
theorem MCA_unique_decoding_large_gamma_bound
    [Fintype S] [DecidableEq S] [Nonempty S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_lo : 1 / n ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ ((n : ℚ) * γ + 1) * (ℓ - 1) / Fintype.card S := by
  classical
  -- Notation: bad_pred is the per-seed MCA bad-event predicate.
  set bad_pred : S → Prop := fun x =>
    ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j) with hbad_def
  by_contra h_gt
  push_neg at h_gt
  -- h_gt : ((n*γ+1)*(ℓ-1))/|S| < seedProb bad_pred.
  -- Setup: positivity / sign facts.
  have h_S_pos_nat : 0 < Fintype.card S := Fintype.card_pos
  have h_S_pos : (0 : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast h_S_pos_nat
  have h_S_ne : (Fintype.card S : ℚ) ≠ 0 := ne_of_gt h_S_pos
  -- 0 < n: follows from 1/n ≤ γ. If n = 0 then 1/0 = 0 ≤ γ trivially.
  -- We need 0 < n separately; derive from hγ_hi: if n = 0, RHS = δ_C/0 = 0 in ℚ,
  -- and we'd need γ*(ℓ+1) < 0; but the proof requires positive n elsewhere.
  -- We *can* still derive 0 ≤ γ either way, but we proceed by case-splitting.
  by_cases hn0 : n = 0
  · -- n = 0 case: bad_pred x ⇒ ∃ T ⊆ Finset (Fin 0), ∃ j, ¬InRestrictedCode c T (us j).
    -- But Fin 0 is empty so T = ∅ and inRestrictedCode_empty rules out the j.
    -- Hence bad_pred is everywhere False, seedProb = 0, and h_gt < 0 yields contradiction
    -- once we observe the RHS is nonneg.
    exfalso
    subst hn0
    have h_pred_false : ∀ x : S, ¬ bad_pred x := by
      intro x hbad
      obtain ⟨T, _, _, j, hj⟩ := hbad
      have hT_empty : T = ∅ := by
        ext i; exact i.elim0
      rw [hT_empty] at hj
      exact hj (inRestrictedCode_empty c (us j))
    have h_seedProb_zero : seedProb (S := S) bad_pred = 0 := by
      have heq : bad_pred = (fun _ : S => False) :=
        funext (fun x => propext ⟨fun h => (h_pred_false x h).elim, fun h => h.elim⟩)
      rw [heq]; exact seedProb_const_false
    have hℓm_nn0 : (0 : ℚ) ≤ ((ℓ : ℚ) - 1) := by
      have : (1 : ℚ) ≤ ℓ := by exact_mod_cast hℓ
      linarith
    have h_rhs_nn : (0 : ℚ) ≤ (((0 : ℕ) : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by
      have h_factor_nn : (0 : ℚ) ≤ ((0 : ℕ) : ℚ) * γ + 1 := by push_cast; linarith
      exact mul_nonneg h_factor_nn hℓm_nn0
    have h_div_nn : (0 : ℚ) ≤ (((0 : ℕ) : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) / Fintype.card S :=
      div_nonneg h_rhs_nn (le_of_lt h_S_pos)
    -- h_gt asserts that the RHS (which equals h_div_nn quantity) is < seedProb = 0.
    have : seedProb (S := S) bad_pred = 0 := h_seedProb_zero
    linarith [h_gt, this, h_div_nn]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hn_pos_Q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
  have hn_ne_Q : (n : ℚ) ≠ 0 := ne_of_gt hn_pos_Q
  -- 0 ≤ γ from 1/n ≤ γ (and 0 < n).
  have hγ_pos : (0 : ℚ) ≤ γ := by
    have h1 : (0 : ℚ) ≤ 1 / (n : ℚ) := by positivity
    linarith [hγ_lo]
  have hℓ_ge_one : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
  have hℓm_nn : (0 : ℚ) ≤ ((ℓ : ℚ) - 1) := by linarith
  have hnγ_nn : (0 : ℚ) ≤ (n : ℚ) * γ := mul_nonneg (le_of_lt hn_pos_Q) hγ_pos
  -- Bridge seedProb → filter card on B_set.
  let bad_dec : DecidablePred bad_pred := Classical.decPred _
  set B_set : Finset S := Finset.univ.filter bad_pred with hB_def
  -- |B_set| = (filter card under classical decidability) and seedProb bad_pred =
  -- |B_set|/|S|; so |B_set| > (n*γ+1)*(ℓ-1).
  have h_seedProb_eq :
      seedProb (S := S) bad_pred = (B_set.card : ℚ) / Fintype.card S := by
    show (Finset.univ.filter bad_pred).card / (Fintype.card S : ℚ) = _
    rfl
  have hB_size_q : (B_set.card : ℚ) > ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by
    rw [h_seedProb_eq] at h_gt
    rw [div_lt_div_iff_of_pos_right h_S_pos] at h_gt
    exact h_gt
  -- Derive |B_set| ≥ ℓ from hB_size_q (since 1 ≤ n*γ from hγ_lo).
  have hnγ_ge_one : (1 : ℚ) ≤ (n : ℚ) * γ := by
    have h := hγ_lo
    -- 1/n ≤ γ and 0 < n: multiply by n.
    have : 1 ≤ (n : ℚ) * γ := by
      have h1 := mul_le_mul_of_nonneg_left h (le_of_lt hn_pos_Q)
      rw [mul_div_assoc', mul_one, div_self hn_ne_Q] at h1
      linarith
    exact this
  have hnγ1_ge_two : (2 : ℚ) ≤ (n : ℚ) * γ + 1 := by linarith
  have hB_card_lower_Q : ((ℓ : ℚ) - 1) ≤ (B_set.card : ℚ) := by
    have h_step : (1 : ℚ) * ((ℓ : ℚ) - 1) ≤ ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hℓm_nn
    have : ((ℓ : ℚ) - 1) ≤ ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by linarith
    linarith [hB_size_q]
  have hB_card_ℓ : ℓ ≤ B_set.card := by
    -- |B_set| ≥ ℓ-1 in ℚ, but we need ℓ. Sharper: hB_size_q strict ⇒ |B_set| ≥ (ℓ-1)+1 = ℓ
    -- since (n*γ+1)*(ℓ-1) ≥ 1*(ℓ-1) = ℓ-1, hence |B_set| > ℓ-1, hence |B_set| ≥ ℓ.
    have h1 : ((B_set.card : ℚ)) > ((ℓ : ℚ) - 1) := by
      have h_step : (1 : ℚ) * ((ℓ : ℚ) - 1) ≤ ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hℓm_nn
      linarith
    -- Convert to ℕ.
    have h2 : (((ℓ - 1 : ℕ) : ℚ)) < (B_set.card : ℚ) := by
      have hcast : ((ℓ - 1 : ℕ) : ℚ) = ((ℓ : ℚ) - 1) := by
        rw [Nat.cast_sub hℓ, Nat.cast_one]
      linarith
    have h3 : (ℓ - 1 : ℕ) < B_set.card := by exact_mod_cast h2
    omega
  -- Extract distinct ℓ seeds + witnesses.
  obtain ⟨xs, h_xs_inj, h_xs_in⟩ :=
    exists_distinct_seeds_in_finset (S := S) (ℓ := ℓ) B_set hB_card_ℓ
  have h_bad_pointwise : ∀ x ∈ B_set, bad_pred x := fun x hx =>
    (Finset.mem_filter.mp hx).2
  -- Build per-seed MCABadWitness for each of the ℓ chosen seeds.
  let ws : ∀ k, MCABadWitness G c us γ (xs k) := fun k =>
    mkMCABadWitness G c us γ (xs k) (h_bad_pointwise (xs k) (h_xs_in k))
  -- Build the cstars via MDS-surjectivity.
  obtain ⟨cstars, h_cstars_mem, h_cstars_eq⟩ :=
    exists_cstars_of_MDS hG_MDS xs h_xs_inj (fun k => (ws k).cw)
      (fun k => (ws k).cw_mem)
  -- Define the global agreement set Ttilde.
  set Ttilde : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => ∀ j, us j i = cstars j i)
    with hTtilde_def
  have hTtilde_iff : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i := by
    intro i; simp [hTtilde_def]
  -- For each x ∈ B_set, derive the agreement set Tx with combine-equality.
  have h_agree_for_lemma : ∀ x ∈ B_set, ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x cstars i := by
    intro x hx
    let w_x : MCABadWitness G c us γ x :=
      mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2)
    have h_cw_eq : w_x.cw = G.combine x cstars :=
      bad_witness_cw_eq_combine_cstars hG_MDS hℓ h_minDist us hγ_hi hn_pos
        xs h_xs_inj ws cstars h_cstars_mem h_cstars_eq w_x
    refine ⟨w_x.T, w_x.T_size, ?_⟩
    intro i hi
    -- w_x.agree i hi : w_x.cw i = G.combine x us i
    -- h_cw_eq : w_x.cw = G.combine x cstars
    have hcw_at_i : w_x.cw i = G.combine x cstars i := by rw [h_cw_eq]
    rw [← hcw_at_i, w_x.agree i hi]
  -- Apply Lemma 5.3 (paper-tight via integer rounding): |Ttilde| ≥ n*(1-γ).
  have hTtilde_size : (Ttilde.card : ℚ) ≥ n * (1 - γ) :=
    Ttilde_card_gt_of_MDS_aggregate hG_MDS hℓ us cstars hγ_pos hn_pos
      B_set h_agree_for_lemma hB_size_q Ttilde hTtilde_iff
  -- For each x ∈ B_set, build Bx (max-agreement domain extension of w_x.T).
  let Bx : ∀ x ∈ B_set, Finset (Fin n) := fun x hx =>
    (MCABadWitness.exists_maxAgreement_extending
      (mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2))).choose
  have h_Bx_spec : ∀ x (hx : x ∈ B_set),
      (mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2)).T ⊆ Bx x hx ∧
      IsMaxAgreementDomain c
        (G.combine x us)
        (Bx x hx) := fun x hx =>
    (MCABadWitness.exists_maxAgreement_extending
      (mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2))).choose_spec
  -- Combine equality on Bx (used by both Ttilde_subset_maxAgreementDomain and degree_bound).
  have h_Bx_eq : ∀ x (hx : x ∈ B_set),
      ∀ i ∈ Bx x hx, G.combine x us i = G.combine x cstars i := by
    intro x hx i hi
    let w_x : MCABadWitness G c us γ x :=
      mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2)
    have h_cw_eq : w_x.cw = G.combine x cstars :=
      bad_witness_cw_eq_combine_cstars hG_MDS hℓ h_minDist us hγ_hi hn_pos
        xs h_xs_inj ws cstars h_cstars_mem h_cstars_eq w_x
    obtain ⟨v, hv_mem, hv_agree⟩ := (h_Bx_spec x hx).2.1
    have hwT_sub_Bx := (h_Bx_spec x hx).1
    -- Outer split: handle the degenerate case δ_C > n (forces c = {0}) directly.
    by_cases hδ_top : δ_C > n
    · -- δ_C > n: every codeword in c is zero. Hence G.combine x us = 0 on Bx and
      -- G.combine x cstars = 0 globally.
      have h_null : ∀ u ∈ c, u = 0 := by
        intro u hu
        by_contra hu_ne
        have h_dist := h_minDist u hu hu_ne
        have h_le : hammingWeight u ≤ n := hammingWeight_le u
        omega
      have hv_zero : v = 0 := h_null v hv_mem
      have hwx_zero : w_x.cw = 0 := h_null _ w_x.cw_mem
      have h_combine_cstars_zero : G.combine x cstars = 0 := by
        rw [← h_cw_eq]; exact hwx_zero
      have h_us_eq : G.combine x us i = 0 := by
        have hagree_i := hv_agree i hi
        rw [hv_zero] at hagree_i
        -- hagree_i : (0 : Fin n → F) i = G.combine x us i.
        have : (0 : Fin n → F) i = (0 : F) := rfl
        rw [this] at hagree_i
        exact hagree_i.symm
      rw [h_us_eq, h_combine_cstars_zero]
      rfl
    push_neg at hδ_top
    -- Standard case δ_C ≤ n: w_x.T.card > n - δ_C, and codeword uniqueness applies.
    have hwT_size_gt : w_x.T.card > n - δ_C := by
      have hsize := w_x.T_size
      have h_n_minus : (((n - δ_C : ℕ) : ℚ)) = (n : ℚ) - δ_C := Nat.cast_sub hδ_top
      have hn_minus_lt : ((n : ℚ) - δ_C) < n * (1 - γ) := by
        have hℓ1_ge_1 : (1 : ℚ) ≤ (ℓ : ℚ) + 1 := by linarith
        have hγ_le : γ ≤ γ * ((ℓ : ℚ) + 1) := by
          have h_step : γ * 1 ≤ γ * ((ℓ : ℚ) + 1) :=
            mul_le_mul_of_nonneg_left hℓ1_ge_1 hγ_pos
          linarith
        have hγ_lt_δ_n : γ < (δ_C : ℚ) / n := lt_of_le_of_lt hγ_le hγ_hi
        have hnγ_lt_δ : (n : ℚ) * γ < δ_C := by
          have h_step := mul_lt_mul_of_pos_left hγ_lt_δ_n hn_pos_Q
          have h_simp : (n : ℚ) * ((δ_C : ℚ) / n) = δ_C := by field_simp
          linarith [h_simp ▸ h_step]
        have heq : (n : ℚ) * (1 - γ) = n - n * γ := by ring
        rw [heq]; linarith
      have hQ : ((n - δ_C : ℕ) : ℚ) < (w_x.T.card : ℚ) := by
        rw [h_n_minus]; linarith
      exact_mod_cast hQ
    -- v = w_x.cw via codeword_eq_of_agree_on_large_set.
    have h_eq_v_wcw : v = w_x.cw := by
      apply codeword_eq_of_agree_on_large_set h_minDist hv_mem w_x.cw_mem hwT_size_gt
      intro k hk
      rw [hv_agree k (hwT_sub_Bx hk)]
      rw [w_x.agree k hk]
    -- G.combine x us i = v i = w_x.cw i = G.combine x cstars i.
    have h1 := hv_agree i hi
    rw [h_eq_v_wcw, h_cw_eq] at h1
    exact h1.symm
  -- Index B_set by Fin t (where t := |B_set|).
  let t := B_set.card
  let bequiv : Fin t ≃ B_set := (Finset.equivFinOfCardEq (rfl : B_set.card = t)).symm
  let xfun : Fin t → S := fun k => (bequiv k).val
  have hxfun_inj : Function.Injective xfun := by
    intro a b hab
    apply bequiv.injective
    exact Subtype.ext hab
  have hxfun_in_B : ∀ k, xfun k ∈ B_set := fun k => (bequiv k).property
  let Bxs : Fin t → Finset (Fin n) := fun k => Bx (xfun k) (hxfun_in_B k)
  -- Strict superset Ttilde ⊊ Bxs k via Ttilde_subset_maxAgreementDomain
  -- + CAdomain_strictly_subset_maxAgreementDomain.
  have h_Ttilde_def_pt : ∀ i ∈ Ttilde, ∀ j, us j i = cstars j i := by
    intro i hi
    exact (hTtilde_iff i).mp hi
  have h_Ttilde_CA : IsCADomain c us Ttilde := by
    intro j
    refine ⟨cstars j, h_cstars_mem j, ?_⟩
    intro i hi
    exact ((hTtilde_iff i).mp hi j).symm
  have h_strict : ∀ k, Ttilde ⊂ Bxs k := by
    intro k
    set x := xfun k
    have hx : x ∈ B_set := hxfun_in_B k
    let w_x : MCABadWitness G c us γ x :=
      mkMCABadWitness G c us γ x ((Finset.mem_filter.mp hx).2)
    have hwT_sub : w_x.T ⊆ Bxs k := (h_Bx_spec x hx).1
    have hBx_max : IsMaxAgreementDomain c (G.combine x us) (Bxs k) :=
      (h_Bx_spec x hx).2
    have hTtilde_sub : Ttilde ⊆ Bxs k :=
      Ttilde_subset_maxAgreementDomain (G := G) (c := c)
        us cstars h_cstars_mem Ttilde h_Ttilde_def_pt hBx_max (h_Bx_eq x hx)
    exact CAdomain_strictly_subset_maxAgreementDomain
      (G := G) (c := c) us w_x hwT_sub h_Ttilde_CA hTtilde_sub
  -- Degree bound: each j ∉ Ttilde lies in at most ℓ-1 of the Bxs k.
  have h_degree : ∀ j : Fin n, j ∉ Ttilde →
      (Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).card ≤ ℓ - 1 := by
    intro j hj_notT
    -- Use `degree_bound_at_non_Ttilde` on B_set, then reindex via `xfun` injection.
    -- The image of (filter on Fin t) under `xfun` is contained in
    -- (filter on B_set). Hence card LHS ≤ card RHS ≤ ℓ-1.
    have h_Ttilde_def_full : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i := hTtilde_iff
    have h_RHS_le := degree_bound_at_non_Ttilde (G := G) (γ := γ) hG_MDS hℓ us cstars
      Ttilde h_Ttilde_def_full Bx h_Bx_eq j hj_notT
    -- Build the image map from {k : j ∈ Bxs k} to {x ∈ B_set : j ∈ Bx x _}.
    have h_image_sub :
        (Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).image xfun ⊆
        B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx) := by
      intro x hx_mem
      rw [Finset.mem_image] at hx_mem
      obtain ⟨k, hk_filt, rfl⟩ := hx_mem
      rw [Finset.mem_filter] at hk_filt
      have hx_in_B : xfun k ∈ B_set := hxfun_in_B k
      rw [Finset.mem_filter]
      refine ⟨hx_in_B, hx_in_B, ?_⟩
      exact hk_filt.2
    have h_image_card :
        ((Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).image xfun).card =
        (Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).card :=
      Finset.card_image_of_injective _ hxfun_inj
    calc (Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).card
        = ((Finset.univ.filter (fun k : Fin t => j ∈ Bxs k)).image xfun).card :=
            h_image_card.symm
      _ ≤ (B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx)).card :=
            Finset.card_le_card h_image_sub
      _ ≤ ℓ - 1 := h_RHS_le
  -- Apply strict_superset_count_bound.
  have h_count := strict_superset_count_bound (α := Fin n) (ℓ := ℓ) (t := t)
    (by omega : 1 ≤ ℓ) Ttilde Bxs h_strict h_degree
  -- h_count : t ≤ (ℓ-1) * (Fintype.card (Fin n) - Ttilde.card).
  have h_univ_n : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [h_univ_n] at h_count
  -- Convert to ℚ.
  have hT_le_n : Ttilde.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ Ttilde)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have h_count_Q :
      (B_set.card : ℚ) ≤ ((ℓ : ℚ) - 1) * ((n : ℚ) - Ttilde.card) := by
    -- t = B_set.card.
    have h_eq_t : (B_set.card : ℕ) = t := rfl
    -- (n - Ttilde.card : ℕ) cast = n - Ttilde.card in ℚ.
    have h_cast_sub : ((n - Ttilde.card : ℕ) : ℚ) = (n : ℚ) - Ttilde.card :=
      Nat.cast_sub hT_le_n
    have h_cast_lm1 : ((ℓ - 1 : ℕ) : ℚ) = ((ℓ : ℚ) - 1) := by
      rw [Nat.cast_sub hℓ, Nat.cast_one]
    have h_count_Q1 : (t : ℚ) ≤ ((ℓ - 1 : ℕ) : ℚ) * ((n - Ttilde.card : ℕ) : ℚ) := by
      exact_mod_cast h_count
    rw [h_cast_sub, h_cast_lm1] at h_count_Q1
    exact h_count_Q1
  -- Now: (n - Ttilde.card : ℚ) ≤ n*γ + 1 (from hTtilde_size : Ttilde.card ≥ n*(1-γ)).
  -- Note: we have the *paper-tight* bound `≥ n*(1-γ)`, but only need
  -- the weaker `≤ n*γ + 1` form here, retained for compatibility.
  have h_n_minus_T : ((n : ℚ) - Ttilde.card) ≤ (n : ℚ) * γ + 1 := by
    have h : (Ttilde.card : ℚ) ≥ (n : ℚ) * (1 - γ) - 1 := by linarith [hTtilde_size]
    have h_expand : (n : ℚ) * (1 - γ) - 1 = (n : ℚ) - n * γ - 1 := by ring
    linarith [h_expand ▸ h]
  -- Combine: |B_set| ≤ (ℓ-1)*(n*γ + 1) = (n*γ+1)*(ℓ-1), contradicting hB_size_q.
  have h_final : (B_set.card : ℚ) ≤ ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by
    have h_step :
        ((ℓ : ℚ) - 1) * ((n : ℚ) - Ttilde.card) ≤
        ((ℓ : ℚ) - 1) * ((n : ℚ) * γ + 1) :=
      mul_le_mul_of_nonneg_left h_n_minus_T hℓm_nn
    have h_comm : ((ℓ : ℚ) - 1) * ((n : ℚ) * γ + 1) =
                  ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by ring
    linarith [h_step]
  linarith

/-! ### BCGM25 Theorem 6.1 unified bound (unique-decoding regime) -/

/-- Helper C1: relax both the small-γ bound `(ℓ-1)/|S|` and the large-γ
bound `((n·γ+1)·(ℓ-1))/|S|` to the unified `(max(n·γ,1)+1)·(ℓ-1)/|S|`. -/
theorem max_one_nGamma_relax_v2
    {S : Type*} [Fintype S] [Nonempty S] {ℓ : ℕ}
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hℓ : 0 < ℓ) (n : ℕ) :
    ((ℓ : ℚ) - 1) / Fintype.card S ≤
        (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S
    ∧ ((n : ℚ) * γ + 1) * (ℓ - 1) / Fintype.card S ≤
        (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S := by
  have hN_pos : (0 : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast Fintype.card_pos
  have hℓm1_nn : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
    linarith
  have hnγ_nn : (0 : ℚ) ≤ (n : ℚ) * γ := mul_nonneg (by exact_mod_cast Nat.zero_le _) hγ_pos
  refine ⟨?_, ?_⟩
  · -- (ℓ-1)/|S| ≤ (max(nγ,1)+1)(ℓ-1)/|S|, i.e. 1 ≤ max(nγ,1)+1.
    apply div_le_div_of_nonneg_right _ (le_of_lt hN_pos)
    have h_max_ge_one : (1 : ℚ) ≤ max ((n : ℚ) * γ) 1 := le_max_right _ _
    have h_factor_ge_one : (1 : ℚ) ≤ max ((n : ℚ) * γ) 1 + 1 := by linarith
    have : (1 : ℚ) * ((ℓ : ℚ) - 1) ≤ (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) :=
      mul_le_mul_of_nonneg_right h_factor_ge_one hℓm1_nn
    linarith
  · -- (nγ+1)(ℓ-1)/|S| ≤ (max(nγ,1)+1)(ℓ-1)/|S|, since nγ+1 ≤ max(nγ,1)+1.
    apply div_le_div_of_nonneg_right _ (le_of_lt hN_pos)
    have h_le : (n : ℚ) * γ + 1 ≤ max ((n : ℚ) * γ) 1 + 1 := by
      have : (n : ℚ) * γ ≤ max ((n : ℚ) * γ) 1 := le_max_left _ _
      linarith
    exact mul_le_mul_of_nonneg_right h_le hℓm1_nn

/-- **BCGM25 Theorem 6.1 (unique-decoding regime).** For an MDS
generator and `γ · (ℓ + 1) < δ_C / n`, the MCA bad-event probability is
bounded by `(max{n·γ, 1} + 1)·(ℓ-1) / |S|`. The proof case-splits on
`γ < 1/n` (Case 1, `MCA_unique_decoding_small_gamma_bound`) vs `γ ≥ 1/n`
(Case 2, `MCA_unique_decoding_large_gamma_bound`).

**Hypothesis use.** `h_minDist` is consumed *only* on the large-γ
(γ ≥ 1/n) branch — Case 1 reduces to the strict bad-seed shape
`Δ_x = 0`, which does not need the min-distance witness. Callers
known to be in the small-γ regime should prefer
`MCA_unique_decoding_small_gamma_bound` directly, which drops the
`h_minDist` and `δ_C` hypotheses entirely.

This bound is the integer-honest form of BCGM25's `max{n·γ,1}·(ℓ-1)/|S|`,
matching BCH+25 (eprint 2025/2055) Theorem 4.1 (tight per Remark 2.5).
For the Case 2 reduction's bad-seed shape, the real-number form is
genuinely insufficient — see header comment and
`LinearCodes/MCA/Lemma53Examples.lean`. -/
theorem MCA_unique_decoding_bound
    [Fintype S] [DecidableEq S] [Nonempty S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * (ℓ - 1) / Fintype.card S := by
  classical
  obtain ⟨h_relax_small, h_relax_large⟩ :=
    max_one_nGamma_relax_v2 (S := S) hγ_pos hℓ n
  by_cases h_small : (n : ℚ) * γ < 1
  · -- Case 1 (small γ): apply MCA_unique_decoding_small_gamma_bound, then relax.
    have h_le := MCA_unique_decoding_small_gamma_bound (S := S) G hG_MDS hℓ c hn us
      hγ_pos h_small
    exact le_trans h_le h_relax_small
  · -- Case 2 (large γ): need 1/n ≤ γ. Derive from ¬(n·γ < 1) i.e. n·γ ≥ 1.
    push_neg at h_small
    have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
    have hγ_lo : 1 / (n : ℚ) ≤ γ := by
      rw [div_le_iff₀ hn_pos]
      linarith
    have h_le := MCA_unique_decoding_large_gamma_bound (S := S) G hG_MDS hℓ c h_minDist us
      hγ_lo hγ_hi
    exact le_trans h_le h_relax_large

-- Sanity: the capstone elaborates against a concrete instance.
-- Don't actually evaluate it; just verify the types fit.
example {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (G : Generator F F 2) (hG_MDS : G.IsMDS)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin 2 → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (2 + 1) < δ_C / n) :
    seedProb (S := F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin 2, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * (2 - 1) / Fintype.card F :=
  MCA_unique_decoding_bound G hG_MDS (by omega) c hn h_minDist us hγ_pos hγ_hi

/-! ### Reader-friendly aliases

The paper-faithful `MCA_*` names are convenient for cross-referencing
BCGM25 / BCIKS18 but opaque to readers who haven't read those papers.
We expose long-form aliases so external callers can discover the
theorems via their full natural-language names. -/

@[inherit_doc MCA_unique_decoding_bound]
alias correlatedAgreement_uniqueDecoding_error := MCA_unique_decoding_bound

end LinearCodes
