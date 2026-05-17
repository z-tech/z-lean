/-
# MDS-bridge sub-targets for Case 2 (BCGM25 Theorem 6.1)

The MDS-structure half of the Case 2 decomposition. Given the counting
primitives from `Case2/Counting.lean`, this file builds the chain that
turns the unique-decoding regime's bad-event predicate into a counting
problem on the bad-seed set:

* Sub-target D — coordinate-wise CA from MDS-equality
  (`isCADomain_of_combines_agree`).
* Sub-target F — strictness of `Ttilde ⊊ Bₓ`
  (`CAdomain_strictly_subset_maxAgreementDomain`).
* Sub-target E1 — existence of `cstars` from MDS-surjectivity
  (`exists_cstars_of_MDS`).
* Sub-target E2 — codeword equality from triangle + min-distance
  (`bad_witness_cw_eq_combine_cstars`).
* Sub-target E6 — `Ttilde ⊆ Bₓ` for each bad seed
  (`Ttilde_subset_maxAgreementDomain`).
* Sub-target E8 — degree bound for `strict_superset_count_bound`
  (`degree_bound_at_non_Ttilde`).

(Formerly the middle of `LinearCodes/MCA/Case2/`,
extracted as part of the P2 file-split refactor.)
-/

import LinearCodes.MCA.Case2.Counting
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- File-level variables are used by most theorems but legitimately
-- unused in some. Suppression kept for this file.
set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-! ### Sub-target D: coordinate-wise CA from MDS-equality -/

/-- If `combine (xs k) us i = combine (xs k) cstars i` for all `k` at every
`i ∈ Ttilde`, then on `Ttilde`, `us j i = cstars j i` (by MDS coordinatewise).
Hence `Ttilde` is a CA domain via the `cstars j` witnesses. -/
theorem isCADomain_of_combines_agree
    [DecidableEq S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)}
    (us cstars : Fin ℓ → (Fin n → F)) (h_cstars : ∀ k, cstars k ∈ c)
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (Ttilde : Finset (Fin n))
    (h_agree : ∀ i ∈ Ttilde, ∀ k,
      G.combine (xs k) us i = G.combine (xs k) cstars i) :
    IsCADomain c us Ttilde ∧ (∀ j i, i ∈ Ttilde → cstars j i = us j i) := by
  -- Step 1: prove the coordinate-wise equality on Ttilde via MDS.
  have h_eq : ∀ j i, i ∈ Ttilde → cstars j i = us j i := by
    intro j i hi
    -- Define v j = us j i - cstars j i and show dotMap G v vanishes at all xs k.
    set v : Fin ℓ → F := fun j => us j i - cstars j i with hv_def
    have h_zero : ∀ k, G.dotMap v (xs k) = 0 := by
      intro k
      have hk := h_agree i hi k
      have h_sum_eq :
          ∑ j : Fin ℓ, G (xs k) j * us j i =
          ∑ j : Fin ℓ, G (xs k) j * cstars j i := hk
      have h_sub :
          ∑ j : Fin ℓ, G (xs k) j * (us j i - cstars j i) = 0 := by
        have h_split :
            (∑ j : Fin ℓ, G (xs k) j * (us j i - cstars j i)) =
              (∑ j : Fin ℓ, G (xs k) j * us j i)
                - (∑ j : Fin ℓ, G (xs k) j * cstars j i) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        rw [h_split, h_sum_eq, sub_self]
      simpa [Generator.dotMap_apply, hv_def] using h_sub
    have hv_zero : v = 0 :=
      hG_MDS.dotMap_distinct_seeds_eq_zero xs h_distinct h_zero
    have hj : v j = 0 := by simpa using congrFun hv_zero j
    have h_sub_zero : us j i - cstars j i = 0 := by simpa [hv_def] using hj
    exact (sub_eq_zero.mp h_sub_zero).symm
  refine ⟨?_, h_eq⟩
  -- Step 2: IsCADomain c us Ttilde — use cstars j as witnesses.
  intro j
  refine ⟨cstars j, h_cstars j, ?_⟩
  intro i hi
  exact h_eq j i hi

/-! ### Sub-target F: strictness of `Ttilde ⊊ Bₓ` -/

/-- A maximal agreement domain B containing the bad witness's T strictly
contains any CA domain `Ttilde` that's also contained. The strictness comes
from the bad row in `MCABadWitness`. -/
theorem CAdomain_strictly_subset_maxAgreementDomain
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} {x : S} (w : MCABadWitness G c us γ x)
    {B Ttilde : Finset (Fin n)}
    (hwT_sub : w.T ⊆ B)
    (hTtilde_CA : IsCADomain c us Ttilde)
    (hTtilde_sub : Ttilde ⊆ B) :
    Ttilde ⊂ B := by
  refine ⟨hTtilde_sub, ?_⟩
  intro hBsub
  obtain ⟨j₀, hj₀⟩ := w.bad_row
  have hwT_sub_Ttilde : w.T ⊆ Ttilde := fun i hi => hBsub (hwT_sub hi)
  exact hj₀ (inRestrictedCode_mono hwT_sub_Ttilde (hTtilde_CA j₀))

/-! ### Sub-target E1: existence of `cstars` (MDS-surjectivity) -/

/-- MDS-surjectivity: given ℓ distinct seeds and ℓ codewords (one per seed),
there exist `cstars : Fin ℓ → (Fin n → F)` (all codewords) such that
`G.combine (xs k) cstars = cs k` for every `k`. The `cstars j` are in `c`
because each is an `F`-linear combination of the `cs k`'s (via `M⁻¹`).

Proof strategy: let `Φ : (Fin ℓ → (Fin n → F)) →ₗ[F] (Fin ℓ → (Fin n → F))`
send `vs ↦ fun k => G.combine (xs k) vs`. By
`all_us_mem_of_combine_at_distinct_seeds` (MDS), `Φ` has trivial kernel
(any `vs ≠ 0` would give `vs k ∉ {0}`-codeword case). Source/target both
finite dimensional with equal dimension ⇒ `Φ` is surjective. Hit
`cs : Fin ℓ → (Fin n → F)` to get the preimage `cstars`. Membership in `c`
follows because `cstars j = ∑_k (M⁻¹)_{jk} • cs k` is a linear combination
in the submodule. -/
theorem exists_cstars_of_MDS [DecidableEq S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)}
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (cs : Fin ℓ → (Fin n → F)) (h_cs : ∀ k, cs k ∈ c) :
    ∃ cstars : Fin ℓ → (Fin n → F),
      (∀ j, cstars j ∈ c) ∧
      (∀ k, G.combine (xs k) cstars = cs k) := by
  classical
  -- The matrix M k j := G (xs k) j.
  let M : Matrix (Fin ℓ) (Fin ℓ) F := fun k j => G (xs k) j
  -- M.mulVec is injective by MDS rigidity at distinct seeds.
  have hM_inj : Function.Injective M.mulVec := by
    intro v w hvw
    have h_diff : v - w = 0 := by
      apply hG_MDS.dotMap_distinct_seeds_eq_zero xs h_distinct
      intro i
      have hM_diff : M.mulVec (v - w) = 0 := by
        rw [Matrix.mulVec_sub, hvw, sub_self]
      have h_at_i : M.mulVec (v - w) i = 0 := by
        rw [hM_diff]; rfl
      -- M.mulVec (v - w) i = ∑ j, M i j * (v - w) j = G.dotMap (v - w) (xs i).
      have h_unfold : M.mulVec (v - w) i = ∑ j, G (xs i) j * (v j - w j) := by
        show ∑ j, G (xs i) j * (v - w) j = ∑ j, G (xs i) j * (v j - w j)
        refine Finset.sum_congr rfl ?_
        intro j _; rfl
      rw [h_unfold] at h_at_i
      simpa [Generator.dotMap_apply] using h_at_i
    have hvw_eq : v = w := by
      have := sub_eq_zero.mp h_diff
      exact this
    exact hvw_eq
  -- Hence M is a unit.
  have hM_unit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  -- Hence M.det is a unit.
  have hdet_unit : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hM_unit
  -- Define cstars j i := ∑ k, M⁻¹ j k * cs k i.
  refine ⟨fun j => ∑ k : Fin ℓ, M⁻¹ j k • cs k, ?_, ?_⟩
  · -- Membership: each cstars j is a finite F-linear combination of cs k ∈ c.
    intro j
    refine Submodule.sum_mem _ ?_
    intro k _
    exact Submodule.smul_mem _ _ (h_cs k)
  · -- Combine identity: G.combine (xs k') cstars = cs k'.
    intro k'
    funext i
    have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet_unit
    have h_id : ∀ k : Fin ℓ, (∑ j : Fin ℓ, M k' j * M⁻¹ j k) =
        if k' = k then (1 : F) else 0 := by
      intro k
      have := congrFun (congrFun hMM k') k
      simpa [Matrix.mul_apply, Matrix.one_apply, M] using this
    rw [Generator.combine_apply]
    -- Unfold cstars, then swap sums, apply h_id, collapse the `if`.
    have step1 :
        ∑ j : Fin ℓ, G (xs k') j *
            ((∑ k : Fin ℓ, M⁻¹ j k • cs k) i) =
          ∑ j : Fin ℓ, ∑ k : Fin ℓ, M k' j * (M⁻¹ j k * cs k i) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rfl
    rw [step1, Finset.sum_comm]
    have step2 :
        ∑ k : Fin ℓ, ∑ j : Fin ℓ, M k' j * (M⁻¹ j k * cs k i) =
          ∑ k : Fin ℓ, (∑ j : Fin ℓ, M k' j * M⁻¹ j k) * cs k i := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [step2]
    simp_rw [h_id]
    -- Now: ∑ k, (if k' = k then 1 else 0) * cs k i = cs k' i.
    rw [Finset.sum_eq_single k']
    · simp
    · intro k _ hk
      rw [if_neg (Ne.symm hk)]; ring
    · intro h
      exact (h (Finset.mem_univ _)).elim

/-! ### Sub-target E2: codeword equality from triangle + min-dist -/

/-- For any bad seed `x` with witness `w`, the witness codeword `w.cw` equals
`G.combine x cstars`, provided `cstars` is the MDS-built witness array from
`xs : Fin ℓ → B` and `γ·(ℓ+1) < δ_C/n`. The proof uses triangle inequality
on the agreement sets `w.T ∩ ⋂ₖ w_xs_k.T` (size `> n - δ_C` from
`γ·(ℓ+1) < δ_C/n`) and `MinDistAtLeast.codewords_eq_of_agree`.

Specifically: on `w_xs_k.T`, `w_xs_k.cw = G.combine (xs k) us`. By
`exists_cstars_of_MDS`, `G.combine (xs k) cstars = w_xs_k.cw`. So on
`w_xs_k.T`, `G.combine (xs k) us = G.combine (xs k) cstars`. On
`⋂ₖ w_xs_k.T ∩ w.T`, `us = cstars` coordinatewise (sub-target D), so
`G.combine x us = G.combine x cstars` there too. Combined with
`w.cw = G.combine x us` on `w.T`: `w.cw = G.combine x cstars` on
`w.T ∩ ⋂ₖ w_xs_k.T`, of size `> n - δ_C`. Min-dist forces equality. -/
theorem bad_witness_cw_eq_combine_cstars
    [DecidableEq S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (_hℓ : 0 < ℓ)
    {c : Submodule F (Fin n → F)} {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_hi : γ * (ℓ + 1) < δ_C / n) (hn : 0 < n)
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (ws : ∀ k, MCABadWitness G c us γ (xs k))
    (cstars : Fin ℓ → (Fin n → F)) (h_cstars_mem : ∀ j, cstars j ∈ c)
    (h_cstars_eq : ∀ k, G.combine (xs k) cstars = (ws k).cw)
    {x : S} (w : MCABadWitness G c us γ x) :
    w.cw = G.combine x cstars := by
  classical
  -- Helper: if v ∈ c and δ_C > n, then v = 0 (since weight v ≤ n < δ_C).
  have h_zero_of_large : δ_C > n → ∀ v ∈ c, v = 0 := by
    intro hδ v hv
    by_contra hv_ne
    have hw : δ_C ≤ hammingWeight v := h_minDist v hv hv_ne
    have hw_le : hammingWeight v ≤ n := hammingWeight_le v
    omega
  -- G.combine x cstars ∈ c, since each cstars j ∈ c and combine is a linear comb.
  have h_combine_mem_top : G.combine x cstars ∈ c := by
    have h_eq : G.combine x cstars =
        ∑ j : Fin ℓ, (G x j) • cstars j := by
      ext i
      simp only [Generator.combine_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [h_eq]
    exact c.sum_mem (fun j _ => c.smul_mem _ (h_cstars_mem j))
  -- Handle the degenerate case δ_C > n separately.
  by_cases hδ_top : δ_C > n
  · have hcw_zero : w.cw = 0 := h_zero_of_large hδ_top _ w.cw_mem
    have hcomb_zero : G.combine x cstars = 0 :=
      h_zero_of_large hδ_top _ h_combine_mem_top
    rw [hcw_zero, hcomb_zero]
  push_neg at hδ_top
  -- From here on, δ_C ≤ n.
  set T : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter
      (fun i => i ∈ w.T ∧ ∀ k : Fin ℓ, i ∈ (ws k).T) with hT_def
  -- Membership characterisation in T.
  have hT_mem : ∀ i, i ∈ T ↔ i ∈ w.T ∧ ∀ k, i ∈ (ws k).T := by
    intro i
    simp [hT_def]
  -- G.combine x cstars ∈ c, since each cstars j ∈ c and combine is a linear comb.
  have h_combine_mem : G.combine x cstars ∈ c := by
    have h_eq : G.combine x cstars =
        ∑ j : Fin ℓ, (G x j) • cstars j := by
      ext i
      simp only [Generator.combine_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [h_eq]
    exact c.sum_mem (fun j _ => c.smul_mem _ (h_cstars_mem j))
  -- Cardinality of universe = n.
  have hT_sub_univ : T ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have h_univ_card : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- The complement of T inside univ.
  set Tc : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ T with hTc_def
  have hTc_card : Tc.card = n - T.card := by
    rw [hTc_def, Finset.card_sdiff_of_subset hT_sub_univ, h_univ_card]
  -- Bound Tc.card by sum of complement-cardinalities of w.T and (ws k).T.
  have hTc_le : Tc.card ≤
      ((Finset.univ : Finset (Fin n)) \ w.T).card +
      ∑ k : Fin ℓ, ((Finset.univ : Finset (Fin n)) \ (ws k).T).card := by
    set U : Finset (Fin n) :=
      ((Finset.univ : Finset (Fin n)) \ w.T) ∪
        (Finset.univ : Finset (Fin ℓ)).biUnion
          (fun k => (Finset.univ : Finset (Fin n)) \ (ws k).T) with hU_def
    have hTc_sub_U : Tc ⊆ U := by
      intro i hi
      rw [hTc_def, Finset.mem_sdiff] at hi
      obtain ⟨_, hi_notT⟩ := hi
      rw [hT_mem] at hi_notT
      push_neg at hi_notT
      rw [hU_def, Finset.mem_union]
      by_cases hwT : i ∈ w.T
      · right
        obtain ⟨k, hk⟩ := hi_notT hwT
        rw [Finset.mem_biUnion]
        refine ⟨k, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hk⟩
      · left
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hwT⟩
    have h_card_U : U.card ≤
        ((Finset.univ : Finset (Fin n)) \ w.T).card +
        ((Finset.univ : Finset (Fin ℓ)).biUnion
          (fun k => (Finset.univ : Finset (Fin n)) \ (ws k).T)).card := by
      rw [hU_def]
      exact Finset.card_union_le _ _
    have h_biUnion_le :
        ((Finset.univ : Finset (Fin ℓ)).biUnion
          (fun k => (Finset.univ : Finset (Fin n)) \ (ws k).T)).card ≤
        ∑ k : Fin ℓ, ((Finset.univ : Finset (Fin n)) \ (ws k).T).card :=
      Finset.card_biUnion_le
    calc Tc.card
        ≤ U.card := Finset.card_le_card hTc_sub_U
      _ ≤ _ := h_card_U
      _ ≤ _ := by linarith
  -- Bound the complement cardinalities by n*γ.
  have h_compl_w : ((((Finset.univ : Finset (Fin n)) \ w.T).card : ℚ)) ≤ n * γ := by
    have h_le : w.T.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ w.T)
      simpa [h_univ_card] using this
    have h_card_eq :
        (((Finset.univ : Finset (Fin n)) \ w.T).card : ℚ) =
          (n : ℚ) - (w.T.card : ℚ) := by
      have h1 : (((Finset.univ : Finset (Fin n)) \ w.T).card : ℕ) = n - w.T.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h_univ_card]
      rw [h1]
      exact Nat.cast_sub h_le
    rw [h_card_eq]
    have hsize := w.T_size
    linarith
  have h_compl_ws : ∀ k : Fin ℓ,
      ((((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ)) ≤ n * γ := by
    intro k
    have h_le : (ws k).T.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ (ws k).T)
      simpa [h_univ_card] using this
    have h_card_eq :
        (((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ) =
          (n : ℚ) - ((ws k).T.card : ℚ) := by
      have h1 : (((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℕ) = n - (ws k).T.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h_univ_card]
      rw [h1]
      exact Nat.cast_sub h_le
    rw [h_card_eq]
    have hsize := (ws k).T_size
    linarith
  -- Combine: (Tc.card : ℚ) ≤ n*γ + ℓ*(n*γ) = n*γ*(ℓ+1).
  have hTc_bound : (Tc.card : ℚ) ≤ n * γ * (ℓ + 1) := by
    have hcast : (Tc.card : ℚ) ≤
        ((((Finset.univ : Finset (Fin n)) \ w.T).card : ℚ)) +
          ∑ k : Fin ℓ, ((((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ)) := by
      have h_cast := (Nat.cast_le (α := ℚ)).mpr hTc_le
      push_cast at h_cast
      exact h_cast
    have h_sum_le : ∑ k : Fin ℓ,
        ((((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ)) ≤ ℓ * (n * γ) := by
      have hpt : ∀ k ∈ (Finset.univ : Finset (Fin ℓ)),
          ((((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ)) ≤ n * γ := by
        intro k _
        exact h_compl_ws k
      calc ∑ k : Fin ℓ,
              ((((Finset.univ : Finset (Fin n)) \ (ws k).T).card : ℚ))
          ≤ ∑ _ : Fin ℓ, n * γ := Finset.sum_le_sum hpt
        _ = ℓ * (n * γ) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              mul_comm, mul_assoc]
    nlinarith [h_compl_w, h_sum_le, hcast]
  -- Therefore (n - T.card : ℚ) ≤ n*γ*(ℓ+1).
  have hT_le_n : T.card ≤ n := by
    have := Finset.card_le_card hT_sub_univ
    simpa [h_univ_card] using this
  have h_n_sub_eq : ((n - T.card : ℕ) : ℚ) = (n : ℚ) - (T.card : ℚ) := by
    exact Nat.cast_sub hT_le_n
  have h_n_minus_T : ((n : ℚ) - (T.card : ℚ)) ≤ n * γ * (ℓ + 1) := by
    have h_eq : (Tc.card : ℚ) = (n : ℚ) - (T.card : ℚ) := by
      rw [hTc_card]; exact h_n_sub_eq
    rw [← h_eq]; exact hTc_bound
  -- Goal: T.card > n - δ_C.
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hγ_nonneg : 0 ≤ γ := by
    have hsize := w.T_size
    have h_le : (w.T.card : ℚ) ≤ n := by
      have h := Finset.card_le_card (Finset.subset_univ w.T)
      have h' : (w.T.card : ℚ) ≤ ((Finset.univ : Finset (Fin n)).card : ℚ) := by
        exact_mod_cast h
      simpa [h_univ_card] using h'
    have hng : (n : ℚ) * γ ≥ 0 := by linarith
    by_contra hγ_neg
    push_neg at hγ_neg
    have : (n : ℚ) * γ < 0 := mul_neg_of_pos_of_neg hn_pos hγ_neg
    linarith
  -- From γ * (ℓ+1) < δ_C / n, multiply by n: n*γ*(ℓ+1) < δ_C.
  have h_main : (n : ℚ) * γ * (ℓ + 1) < (δ_C : ℚ) := by
    have h := hγ_hi
    have hmul : γ * (↑ℓ + 1) * (n : ℚ) < (δ_C / n : ℚ) * n :=
      mul_lt_mul_of_pos_right h hn_pos
    have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
    rw [div_mul_cancel₀ _ hn_ne] at hmul
    nlinarith [hmul]
  -- So (n : ℚ) - T.card < δ_C, i.e. T.card > n - δ_C in ℕ.
  have h_TQ_gt : ((n : ℚ) - T.card : ℚ) < (δ_C : ℚ) := by
    linarith
  have hT_card_gt : T.card > n - δ_C := by
    have h_cast : ((n - δ_C : ℕ) : ℚ) = (n : ℚ) - (δ_C : ℚ) :=
      Nat.cast_sub hδ_top
    have hQ : (T.card : ℚ) > ((n - δ_C : ℕ) : ℚ) := by
      rw [h_cast]; linarith
    exact_mod_cast hQ
  -- Agreement on T: w.cw i = G.combine x cstars i for all i ∈ T.
  have h_agree_on_T : ∀ i ∈ T, w.cw i = G.combine x cstars i := by
    intro i hi
    rw [hT_mem] at hi
    obtain ⟨hi_w, hi_ws⟩ := hi
    -- Sub-target D pointwise: us j i = cstars j i for all j.
    have h_combine_eq_at_i : ∀ k : Fin ℓ,
        G.combine (xs k) us i = G.combine (xs k) cstars i := by
      intro k
      have h1 : (ws k).cw i = G.combine (xs k) us i :=
        (ws k).agree i (hi_ws k)
      have h2 : G.combine (xs k) cstars i = (ws k).cw i := by
        rw [h_cstars_eq k]
      rw [← h1, ← h2]
    have h_singleton_agree : ∀ j ∈ ({i} : Finset (Fin n)),
        ∀ k : Fin ℓ, G.combine (xs k) us j = G.combine (xs k) cstars j := by
      intro j hj k
      rw [Finset.mem_singleton] at hj
      subst hj
      exact h_combine_eq_at_i k
    have h_cad := isCADomain_of_combines_agree (G := G) hG_MDS
      (us := us) (cstars := cstars) h_cstars_mem xs h_distinct
      ({i} : Finset (Fin n)) h_singleton_agree
    have h_eq_at_i : ∀ j : Fin ℓ, cstars j i = us j i := by
      intro j
      exact h_cad.2 j i (Finset.mem_singleton_self i)
    have hwcw : w.cw i = G.combine x us i := w.agree i hi_w
    have h_combine_eq : G.combine x us i = G.combine x cstars i := by
      simp only [Generator.combine_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [h_eq_at_i j]
    rw [hwcw, h_combine_eq]
  -- Apply MinDistAtLeast.codewords_eq_of_agree.
  exact MinDistAtLeast.codewords_eq_of_agree h_minDist w.cw_mem h_combine_mem
    hT_card_gt h_agree_on_T

/-! ### Sub-target E6: `Ttilde ⊆ Bₓ` for each bad seed -/

/-- For any bad seed `x ∈ B` (with witness `w`) and the global `cstars`-
agreement set `Ttilde := {i : ∀ j, us j i = cstars j i}`, `Ttilde` is
contained in any max-agreement-domain extension `Bₓ` of `w.T`. The witness
is `G.combine x cstars`: it's a codeword (linear combinations preserve
codeword-ness in `c`), and it agrees with `G.combine x us` on `Ttilde`
coordinatewise. So `Ttilde` is an agreement domain for `G.combine x us`
with witness `G.combine x cstars`, contained in the maximal `Bₓ`. -/
theorem Ttilde_subset_maxAgreementDomain
    [DecidableEq S]
    {G : Generator F S ℓ}
    {c : Submodule F (Fin n → F)}
    (us cstars : Fin ℓ → (Fin n → F)) (h_cstars_mem : ∀ j, cstars j ∈ c)
    (Ttilde : Finset (Fin n))
    (h_Ttilde_def : ∀ i ∈ Ttilde, ∀ j, us j i = cstars j i)
    {x : S} {Bx : Finset (Fin n)}
    (hBx_max : IsMaxAgreementDomain c (G.combine x us) Bx)
    (h_combine_eq_on_Bx : ∀ i ∈ Bx, G.combine x us i = G.combine x cstars i) :
    Ttilde ⊆ Bx := by
  -- The witness codeword for the extended agreement domain `Ttilde ∪ Bx`
  -- is `c' := G.combine x cstars`. It is in `c` because each `cstars j ∈ c`.
  set c' : Fin n → F := G.combine x cstars with hc'_def
  have hc'_mem : c' ∈ c := by
    have hc'_eq : c' = ∑ j : Fin ℓ, G x j • cstars j := by
      ext i
      simp [hc'_def, Generator.combine_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_apply]
    rw [hc'_eq]
    exact Submodule.sum_mem c
      (fun j _ => Submodule.smul_mem c _ (h_cstars_mem j))
  -- `c'` agrees with `G.combine x us` on `Ttilde` coordinatewise.
  have h_agree_Ttilde : ∀ i ∈ Ttilde, G.combine x us i = c' i := by
    intro i hi
    simp only [hc'_def, Generator.combine_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_Ttilde_def i hi j]
  -- Argue by contradiction: if `Ttilde ⊄ Bx`, then `Bx ⊊ Ttilde ∪ Bx`,
  -- but `Ttilde ∪ Bx` is an agreement domain via witness `c'`,
  -- contradicting maximality of `Bx`.
  by_contra h_not_sub
  rw [Finset.subset_iff] at h_not_sub
  push_neg at h_not_sub
  obtain ⟨i₀, hi₀_T, hi₀_notBx⟩ := h_not_sub
  have h_ssub : Bx ⊂ Ttilde ∪ Bx := by
    refine ⟨Finset.subset_union_right, ?_⟩
    intro h_sup
    exact hi₀_notBx (h_sup (Finset.mem_union.mpr (Or.inl hi₀_T)))
  have h_AD : IsAgreementDomain c (G.combine x us) (Ttilde ∪ Bx) := by
    refine ⟨c', hc'_mem, ?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with hiT | hiB
    · exact (h_agree_Ttilde i hiT).symm
    · exact (h_combine_eq_on_Bx i hiB).symm
  exact hBx_max.2 (Ttilde ∪ Bx) h_ssub h_AD

/-! ### Sub-target E8: degree bound for strict_superset_count_bound -/

set_option linter.unusedVariables false in
/-- For each coord `j ∉ Ttilde`, at most `ℓ-1` distinct bad seeds `x` have
`j` in their max-agreement-domain extension `Bₓ`. Proof sketch: if `≥ ℓ`
such bad seeds existed, take any ℓ distinct of them `y_1,...,y_ℓ`. On each
`B_{y_k}`, `G.combine y_k us = G.combine y_k cstars` (both equal the unique
codeword witness, see E2). At coord `j ∈ ⋂_k B_{y_k}` (assumption), we get
ℓ equations `G.combine y_k us j = G.combine y_k cstars j`. Sub-target D
applied at this single coord forces `us j vec = cstars j vec` in `F^ℓ`,
contradicting `j ∉ Ttilde`. -/
theorem degree_bound_at_non_Ttilde
    [DecidableEq S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (_hℓ : 0 < ℓ)
    (us cstars : Fin ℓ → (Fin n → F))
    (Ttilde : Finset (Fin n))
    (h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i)
    {γ : ℚ}
    {B_set : Finset S}
    (Bx : ∀ x ∈ B_set, Finset (Fin n))
    (h_Bx_eq : ∀ x (hx : x ∈ B_set),
      ∀ i ∈ Bx x hx, G.combine x us i = G.combine x cstars i)
    (j : Fin n) (hj_notT : j ∉ Ttilde) :
    (B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx)).card ≤ ℓ - 1 := by
  classical
  -- Suppose for contradiction the filter has ≥ ℓ elements.
  by_contra h_card
  have h_card' : ℓ - 1 < (B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx)).card :=
    Nat.lt_of_not_le h_card
  set F_set := B_set.filter (fun x => ∃ hx : x ∈ B_set, j ∈ Bx x hx) with hF_def
  have hℓ_le : ℓ ≤ F_set.card := by omega
  -- Extract ℓ distinct seeds in F_set.
  obtain ⟨ys, ys_inj, ys_mem⟩ :=
    exists_distinct_seeds_in_finset (S := S) (ℓ := ℓ) F_set hℓ_le
  -- For each k, ys k ∈ B_set and j ∈ Bx (ys k) _.
  have ys_in_B : ∀ k, ys k ∈ B_set := by
    intro k
    have h := ys_mem k
    rw [hF_def, Finset.mem_filter] at h
    exact h.1
  have hj_in_Bx : ∀ k, j ∈ Bx (ys k) (ys_in_B k) := by
    intro k
    have h := ys_mem k
    rw [hF_def, Finset.mem_filter] at h
    obtain ⟨_, _, hjBx⟩ := h
    exact hjBx
  -- Apply sub-target D with c := ⊤ and Ttilde := {j}.
  have h_agree : ∀ i ∈ ({j} : Finset (Fin n)), ∀ k,
      G.combine (ys k) us i = G.combine (ys k) cstars i := by
    intro i hi k
    rw [Finset.mem_singleton] at hi
    rw [hi]
    exact h_Bx_eq (ys k) (ys_in_B k) j (hj_in_Bx k)
  have h_top_mem : ∀ k, cstars k ∈ (⊤ : Submodule F (Fin n → F)) :=
    fun _ => Submodule.mem_top
  obtain ⟨_, h_eq⟩ :=
    isCADomain_of_combines_agree (G := G) hG_MDS
      (c := (⊤ : Submodule F (Fin n → F)))
      us cstars h_top_mem ys ys_inj ({j} : Finset (Fin n)) h_agree
  -- Specialize at i := j to derive j ∈ Ttilde, contradicting hj_notT.
  have hj_in_T : j ∈ Ttilde := by
    rw [h_Ttilde_def]
    intro j'
    exact (h_eq j' j (Finset.mem_singleton.mpr rfl)).symm
  exact hj_notT hj_in_T

end LinearCodes
