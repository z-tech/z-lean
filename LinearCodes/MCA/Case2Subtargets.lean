/-
# Sub-targets for BCGM25 Theorem 6.1 Case 2 (γ ≥ 1/n)

Per the Plan agent's decomposition (see swarm-plan-theorem-6-1.md and
aleph-target-theorem-6-1-case-2.md), the Case 2 capstone proof of
`MCA_unique_decoding_large_gamma_bound` decomposes into 8 parallel-
executable sub-targets. Each depends only on currently-proved
infrastructure.
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.MaximalDomain
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-! ### Sub-target A: probability → counting -/

/-- Contrapositive of `seedProb_le_ncard_div`. -/
theorem ncard_lt_of_seedProb_gt
    {S : Type*} [Fintype S] [Nonempty S]
    (P : S → Prop) (N : ℕ)
    (h : ((N : ℚ) / Fintype.card S) < seedProb P) :
    N < {x : S | P x}.ncard := by
  by_contra hN
  push_neg at hN
  have h_le := seedProb_le_ncard_div P N hN
  linarith

/-! ### Sub-target B: distinct seeds in a finset -/

/-- Extract injective `Fin ℓ → S` mapping into a finset of size ≥ ℓ. -/
theorem exists_distinct_seeds_in_finset
    {S : Type*} {ℓ : ℕ} [DecidableEq S]
    (B : Finset S) (hB : ℓ ≤ B.card) :
    ∃ xs : Fin ℓ → S, Function.Injective xs ∧ ∀ i, xs i ∈ B := by
  obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq hB
  let e : Fin ℓ ≃ B' := (Finset.equivFinOfCardEq hB'_card).symm
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hB'_sub (e i).property

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
      hG_MDS.dotMap_zero_at_distinct_seeds_implies_zero xs h_distinct h_zero
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
      apply hG_MDS.dotMap_zero_at_distinct_seeds_implies_zero xs h_distinct
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
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
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
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
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

/-! ### A2-A6: Lemma 5.3 helper lemmas (column-difference + counting) -/

/-- A2: Column-difference vector at coordinate `i`. -/
def colDiff (us cstars : Fin ℓ → (Fin n → F)) (i : Fin n) : Fin ℓ → F :=
  fun j => us j i - cstars j i

/-- A2: Unfolding lemma for `colDiff`. -/
@[simp] theorem colDiff_apply (us cstars : Fin ℓ → (Fin n → F)) (i : Fin n)
    (j : Fin ℓ) :
    colDiff us cstars i j = us j i - cstars j i := rfl

/-- A3: `colDiff` is zero iff `us` and `cstars` agree pointwise at `i`. -/
theorem colDiff_eq_zero_iff_pointwise_agree
    (us cstars : Fin ℓ → (Fin n → F)) (i : Fin n) :
    colDiff us cstars i = 0 ↔ ∀ j, us j i = cstars j i := by
  constructor
  · intro h j
    have hj : colDiff us cstars i j = 0 := by rw [h]; rfl
    exact sub_eq_zero.mp hj
  · intro h
    funext j
    rw [colDiff_apply, Pi.zero_apply, sub_eq_zero]
    exact h j

/-- A4: `i ∈ Ttilde` iff `colDiff i = 0`, given the standard `Ttilde` definition. -/
theorem mem_Ttilde_iff_colDiff_zero
    (us cstars : Fin ℓ → (Fin n → F))
    (Ttilde : Finset (Fin n))
    (h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i)
    (i : Fin n) :
    i ∈ Ttilde ↔ colDiff us cstars i = 0 := by
  rw [h_Ttilde_def i, ← colDiff_eq_zero_iff_pointwise_agree us cstars i]

/-- A5: Combine-equality at coord `i` is equivalent to `dotMap` of `colDiff i`
vanishing at the seed. -/
theorem combine_eq_iff_dotMap_colDiff_zero
    (G : Generator F S ℓ) (us cstars : Fin ℓ → (Fin n → F))
    (x : S) (i : Fin n) :
    G.combine x us i = G.combine x cstars i ↔
      G.dotMap (colDiff us cstars i) x = 0 := by
  rw [Generator.combine_apply, Generator.combine_apply, Generator.dotMap_apply]
  have h_split :
      (∑ j : Fin ℓ, G x j * colDiff us cstars i j) =
        (∑ j : Fin ℓ, G x j * us j i) - (∑ j : Fin ℓ, G x j * cstars j i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [colDiff_apply]
    ring
  rw [h_split, sub_eq_zero]

/-- A6: For each coord `i ∉ Ttilde`, at most `ℓ - 1` bad seeds in `B_set`
have combine-equality at `i`. (Direct consequence of zero-evading at the
nonzero `colDiff i`.) -/
theorem bad_pair_count_per_coord_le
    [Fintype S] [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us cstars : Fin ℓ → (Fin n → F))
    (Ttilde : Finset (Fin n))
    (h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i)
    (B_set : Finset S)
    {i : Fin n} (hi_notT : i ∉ Ttilde) :
    ((B_set.filter (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ)
      ≤ (ℓ - 1 : ℚ) := by
  classical
  -- Step 1: colDiff i is nonzero (since i ∉ Ttilde).
  have h_nonzero : colDiff us cstars i ≠ 0 := by
    intro h
    exact hi_notT
      ((mem_Ttilde_iff_colDiff_zero us cstars Ttilde h_Ttilde_def i).mpr h)
  -- Step 2: ZeroEvading bound from MDS.
  have hZE : ZeroEvading G ((ℓ - 1 : ℚ) / Fintype.card S) :=
    hG_MDS.zeroEvading_bound
  have h_seedProb_le :
      seedProb (S := S) (fun x => ∑ j, G x j * colDiff us cstars i j = 0)
        ≤ ((ℓ - 1 : ℚ) / Fintype.card S) :=
    hZE (colDiff us cstars i) h_nonzero
  -- Step 3: Translate the predicate via A5; show the predicates filter the same set.
  have h_pred_eq : ∀ x : S,
      (G.combine x us i = G.combine x cstars i) ↔
      (∑ j, G x j * colDiff us cstars i j = 0) := by
    intro x
    rw [combine_eq_iff_dotMap_colDiff_zero G us cstars x i, Generator.dotMap_apply]
  -- Step 4: Convert seedProb bound to a filter-card bound on Finset.univ.
  have hN_pos : (0 : ℚ) < (Fintype.card S : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hN_ne : (Fintype.card S : ℚ) ≠ 0 := ne_of_gt hN_pos
  -- Use ncard (set notation) to avoid Decidable-instance mismatches.
  have h_univ_ncard_le :
      ({x : S | ∑ j, G x j * colDiff us cstars i j = 0}.ncard : ℚ)
        ≤ (ℓ - 1 : ℚ) := by
    have h := h_seedProb_le
    unfold seedProb at h
    rw [div_le_div_iff_of_pos_right hN_pos] at h
    -- h has set-comprehension `{x | P x}.card`. Convert to ncard.
    convert h using 2
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp
  -- Step 5: (B_set.filter ...).card ≤ ncard (as ℕ), via coe_filter ⊆ set.
  have h_coe_subset :
      ((B_set.filter
          (fun x => G.combine x us i = G.combine x cstars i)) : Set S) ⊆
        {x : S | ∑ j, G x j * colDiff us cstars i j = 0} := by
    intro x hx
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact (h_pred_eq x).mp hx.2
  have h_set_finite :
      ({x : S | ∑ j, G x j * colDiff us cstars i j = 0}).Finite :=
    Set.toFinite _
  have h_card_le_ncard :
      (B_set.filter (fun x => G.combine x us i = G.combine x cstars i)).card ≤
        ({x : S | ∑ j, G x j * colDiff us cstars i j = 0}).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard h_coe_subset h_set_finite
  have h_card_le_Q :
      ((B_set.filter (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ)
        ≤ ({x : S | ∑ j, G x j * colDiff us cstars i j = 0}.ncard : ℚ) := by
    exact_mod_cast h_card_le_ncard
  exact h_card_le_Q.trans h_univ_ncard_le

/-! ### Sub-target L5_3: BCGM25 Lemma 5.3 specialized to MDS generators

The math gap flagged by the Plan agent — `|Ttilde| > n(1-γ)` — does NOT
follow from naive ℓ-fold-intersection (which gives only `n - ℓ·n·γ`,
off by factor ℓ). The correct argument is BCGM25's Lemma 5.3 (eprint
2025/2051, p.27-28): a *zero-evading aggregate* counting argument.

Sketch: at each `i ∉ Ttilde`, the column-difference vector
`v(i) := (us j i - cstars j i)_j` is nonzero. By zero-evading
(`G.IsMDS.zeroEvading`, ε_ZE = (ℓ-1)/|S|), `{x : G.combine x v(i) = 0}`
has size ≤ ℓ-1. Counting pairs `(x ∈ B, i ∉ Ttilde)` with x in the
"agreement at i" set gives a size bound forcing `|Ttilde| > n(1-γ)`.

## Slack analysis (formalization vs. paper)

BCGM25's Lemma 5.3 states `|T̃| > n(1-γ)` (strict) under the hypothesis
`|B_set| > n·γ·(ℓ-1)`. We instead have `|T̃| ≥ n(1-γ) - 1` under the
strengthened hypothesis `|B_set| > (n·γ + 1)·(ℓ-1)`. The `+1` slack on
the hypothesis (equivalently `−1` slack on the conclusion) propagates
to a `+1` factor in the Phase A capstone bound:
* BCGM25:        `n·γ·(ℓ-1) / |S|`
* This codebase: `(n·γ + 1)·(ℓ-1) / |S|`

**This slack appears intrinsic to the pure aggregate-counting argument**
(verified 2026-05-06). The combined per-coord/per-seed double counting
yields exactly:
```
  s · (b - (ℓ-1)) ≤ n·γ · (ℓ-1)         where s := n(1-γ) - t, b := |B_set|, t := |T̃|
```
To force `s ≤ 0` (i.e., the strict `t ≥ n(1-γ)` BCGM25 conclusion)
from a hypothesis on `b` alone, one needs `b - (ℓ-1) > n·γ · (ℓ-1)`,
i.e., `b > (n·γ + 1)(ℓ-1)`. The case `0 < s < 1` is admissible under
`b > n·γ·(ℓ-1)`: the bound only gives `s · (b - (ℓ-1)) ≤ n·γ·(ℓ-1)`,
which permits `s` arbitrarily close to 0+ as `b → ∞`.

Approaches considered but rejected:
* **Tighter per-coord upper bound**: would require `< ℓ-1` strictly,
  contradicting the tightness of zero-evading at MDS distance.
* **Tighter per-seed lower bound**: replacing `Tx \ T̃` (witness diff)
  with `Ax \ T̃` (true agreement diff) doesn't help — we lack a lower
  bound on `|Ax|` beyond `≥ |Tx| ≥ n(1-γ)`.
* **Using strict containment T̃ ⊊ Bx**: this is the technique used
  *downstream* (in `Case2Capstone.lean` via `strict_superset_count_bound`)
  but requires `T̃` to already be established — circular for this lemma.
* **Integer rounding on `t`**: t is a natural, but n(1-γ) is rational
  with γ rational. Using `t ≥ ⌈n(1-γ)⌉` only converts `t > n(1-γ) - 1`
  (ℚ) to `t ≥ ⌈n(1-γ) - 1⌉ + 1`, which can fail to equal `⌈n(1-γ)⌉`
  when `n(1-γ)` is integral.

The original BCGM25 likely uses a different proof structure — possibly
via `MDS_pairwise_agreement_bound` + Corrádi (cf. `swarm-plan-theorem-6-1.md`),
or via the maximal-agreement-domain framework where strictness is built in.
Either alternative would require substantial new infrastructure (Corrádi
already exists; the wiring through MCA bad-event semantics does not).

## Corrádi attempt (2026-05-06)

A direct application of `Finset.corradi_unconditional` /
`Finset.corradi_ratio` (in `Upstream/Combinatorics/Corradi.lean`) to the
family `{B_x}_{x ∈ B_set}` defined by
`B_x := {i ∈ Fin n : G.combine x us i = G.combine x cstars i}` was
considered. The plan was: each `|B_x| ≥ n(1-γ)`, pairwise
`|B_x ∩ B_y| ≤ ℓ - 1`, then Corrádi gives `|B_set| ≤ N(a-b)/(a²-Nb) =
n·γ·(ℓ-1)` (paper-tight).

This **does not work**: the pairwise bound `|B_x ∩ B_y| ≤ ℓ - 1` is
**false in general**. For all `i ∈ Ttilde`, `i ∈ B_x ∩ B_y` for every
`x, y` (because `i ∈ Ttilde ⇒ ∀ j, us j i = cstars j i`, hence
`combine x us i = combine x cstars i` for every `x`). So `Ttilde ⊆
B_x ∩ B_y` for *every* pair, giving `|B_x ∩ B_y| ≥ |Ttilde|`, which
generally exceeds `ℓ-1`.

Restricting to `(B_x \ Ttilde) ∩ (B_y \ Ttilde)` does not help either:
on this set, `colDiff us cstars i ≠ 0` and both `x, y` are seeds of
`G.dotMap (colDiff i)` zero-set (size ≤ ℓ-1 by zero-evading), but this
constrains the *seeds* per coordinate, not the *count of coordinates*
across pairs. So no tight pairwise bound emerges.

The same fundamental obstruction blocks attempts using max-agreement
domains in place of `B_x`: any two domains contain a common max-CA
extension of `Ttilde`, defeating the `< ℓ` pairwise bound.

The genuine paper proof of BCGM25 Lemma 5.3 likely uses a more delicate
group-by-witness-codeword argument where Corrádi is applied at the
**codeword level** (codewords `c ∈ c` indexing groups of seeds), with
the pairwise bound coming from `MDS_pairwise_agreement_bound` over the
underlying linear code's min-distance, not the MDS dimension `ℓ`.
Implementing this requires:
* a partition `B_set = ⋃_c S_c` by witness-codeword equivalence;
* per-codeword agreement-set sizes `≥ |S_c| · n(1-γ) / |S_c|`;
* a Corrádi instantiation over the codeword index set.

This is a **major** refactor of the witness-codeword infrastructure
and is deferred. The slack form below is retained as a
formally-verified weakening of the paper bound, with `+1` propagated
identically through the Phase A and Phase B capstones via
`max_one_nGamma_relax_v2`.

This stub captures the specialized statement we need for the capstone. -/
theorem Ttilde_card_gt_of_MDS_aggregate
    [Fintype S] [DecidableEq S] [Nonempty S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (us cstars : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hn : 0 < n)
    (B_set : Finset S)
    (h_agree : ∀ x ∈ B_set, ∃ Tx : Finset (Fin n),
      (Tx.card : ℚ) ≥ n * (1 - γ) ∧
      ∀ i ∈ Tx, G.combine x us i = G.combine x cstars i)
    (h_size : (B_set.card : ℚ) > (n * γ + 1) * (ℓ - 1))
    (Ttilde : Finset (Fin n))
    (h_Ttilde_def : ∀ i, i ∈ Ttilde ↔ ∀ j, us j i = cstars j i) :
    (Ttilde.card : ℚ) ≥ n * (1 - γ) - 1 := by
  classical
  -- Strategy: double counting on
  --   P := { (x, i) : x ∈ B_set, i ∈ univ \ Ttilde, combine x us i = combine x cstars i }.
  -- Per-coord upper bound (`bad_pair_count_per_coord_le`): for each i ∉ Ttilde,
  --     |{x ∈ B_set : combine x us i = combine x cstars i}| ≤ ℓ-1.
  -- Hence |P| ≤ (n - |Ttilde|)·(ℓ-1).
  -- Per-seed lower bound: for each x ∈ B_set with witness Tx of size ≥ n(1-γ)
  -- and agreement on Tx, the agreement-at-x count outside Ttilde is
  --     ≥ |Tx \ Ttilde| ≥ |Tx| - |Ttilde| ≥ n(1-γ) - |Ttilde|.
  -- Hence |P| ≥ |B_set|·(n(1-γ) - |Ttilde|).
  -- Combining: |B_set|·(n(1-γ) - |Ttilde|) ≤ (n - |Ttilde|)·(ℓ-1).
  --
  -- Letting `s := n(1-γ) - t`, the combined bound is `b·s ≤ (s+nγ)(ℓ-1)`, i.e.,
  --   s·(b - (ℓ-1)) ≤ nγ·(ℓ-1).
  -- ASSUMING the contradiction `t < n(1-γ) - 1`, we have `s > 1`, so
  --   b - (ℓ-1) < s·(b - (ℓ-1)) ≤ nγ·(ℓ-1),
  -- giving `b < (nγ+1)·(ℓ-1)`, contradicting the strengthened hypothesis
  -- `h_size : b > (nγ+1)·(ℓ-1)`.
  --
  -- TRADE-OFF: the original BCGM25 Lemma 5.3 statement (strict `t > n(1-γ)`
  -- with weaker hypothesis `b > nγ(ℓ-1)`) does NOT follow from pure double-
  -- counting in ℚ — see notes near the end of the proof. Both the conclusion
  -- and the hypothesis have been adjusted by a `(ℓ-1)`-scale slack to close.
  by_contra h_le
  push_neg at h_le
  -- Notation shortcuts.
  set t : ℚ := (Ttilde.card : ℚ) with ht_def
  set b : ℚ := (B_set.card : ℚ) with hb_def
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  -- Cardinality of the universe = n.
  have h_univ_card : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- Ttilde ⊆ univ.
  have hT_sub_univ : Ttilde ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have hT_le_n : Ttilde.card ≤ n := by
    have := Finset.card_le_card hT_sub_univ
    simpa [h_univ_card] using this
  have hT_le_n_Q : t ≤ (n : ℚ) := by
    have : (Ttilde.card : ℚ) ≤ (n : ℚ) := by exact_mod_cast hT_le_n
    exact this
  -- The complement Tc.
  set Tc : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ Ttilde with hTc_def
  have hTc_card_nat : Tc.card = n - Ttilde.card := by
    rw [hTc_def, Finset.card_sdiff_of_subset hT_sub_univ, h_univ_card]
  have hTc_card_Q : (Tc.card : ℚ) = (n : ℚ) - t := by
    have h1 := hTc_card_nat
    have hcast : ((n - Ttilde.card : ℕ) : ℚ) = (n : ℚ) - t :=
      Nat.cast_sub hT_le_n
    rw [h1]; exact hcast
  -- Membership in Tc.
  have hTc_mem : ∀ i, i ∈ Tc ↔ i ∉ Ttilde := by
    intro i
    simp [hTc_def]
  -- For each i ∈ Tc, bound the agreement count via `bad_pair_count_per_coord_le`.
  have h_per_coord : ∀ i ∈ Tc,
      ((B_set.filter
        (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ)
        ≤ (ℓ - 1 : ℚ) := by
    intro i hi
    have hi_notT : i ∉ Ttilde := (hTc_mem i).mp hi
    exact bad_pair_count_per_coord_le hG_MDS hℓ us cstars Ttilde h_Ttilde_def
      B_set hi_notT
  -- The pair set P, indexed first by i then by x.
  set Pset : Finset ((Fin n) × S) :=
    (Tc ×ˢ B_set).filter
      (fun p => G.combine p.2 us p.1 = G.combine p.2 cstars p.1) with hP_def
  -- |P| as a sum-over-i of per-coord filter cards.
  have hP_eq_sum_over_i :
      (Pset.card : ℚ) =
        ∑ i ∈ Tc,
          ((B_set.filter
            (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ) := by
    have h_nat :
        Pset.card =
          ∑ i ∈ Tc,
            (B_set.filter
              (fun x => G.combine x us i = G.combine x cstars i)).card := by
      rw [hP_def]
      -- Pset.card = ∑_i over Tc, fiber-card.
      rw [Finset.card_filter]
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.card_filter]
    have hcast : ((∑ i ∈ Tc,
          (B_set.filter
            (fun x => G.combine x us i = G.combine x cstars i)).card : ℕ) : ℚ) =
        ∑ i ∈ Tc,
          ((B_set.filter
            (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ) := by
      push_cast; rfl
    rw [h_nat]; exact hcast
  -- Per-coord upper bound: |P| ≤ |Tc| · (ℓ-1).
  have h_upper : (Pset.card : ℚ) ≤ ((Tc.card : ℚ)) * (ℓ - 1 : ℚ) := by
    rw [hP_eq_sum_over_i]
    have hsum :
        ∑ i ∈ Tc,
            ((B_set.filter
              (fun x => G.combine x us i = G.combine x cstars i)).card : ℚ)
          ≤ ∑ _ ∈ Tc, (ℓ - 1 : ℚ) :=
      Finset.sum_le_sum h_per_coord
    have hconst : (∑ _ ∈ Tc, (ℓ - 1 : ℚ)) = ((Tc.card : ℚ)) * (ℓ - 1 : ℚ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith [hconst ▸ hsum]
  -- Now |P| as a sum-over-x of per-seed (#agreements outside Ttilde).
  have hP_eq_sum_over_x :
      (Pset.card : ℚ) =
        ∑ x ∈ B_set,
          ((Tc.filter
            (fun i => G.combine x us i = G.combine x cstars i)).card : ℚ) := by
    have h_nat :
        Pset.card =
          ∑ x ∈ B_set,
            (Tc.filter
              (fun i => G.combine x us i = G.combine x cstars i)).card := by
      rw [hP_def]
      rw [Finset.card_filter]
      rw [show ((Tc ×ˢ B_set) : Finset _) = (B_set ×ˢ Tc).image Prod.swap by
        ext ⟨i, x⟩
        simp [Finset.mem_product, And.comm]]
      rw [Finset.sum_image (by
        intro ⟨a, b⟩ _ ⟨c, d⟩ _ h
        simp at h
        ext <;> simp [h.1, h.2])]
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.card_filter]
      rfl
    have hcast : ((∑ x ∈ B_set,
          (Tc.filter
            (fun i => G.combine x us i = G.combine x cstars i)).card : ℕ) : ℚ) =
        ∑ x ∈ B_set,
          ((Tc.filter
            (fun i => G.combine x us i = G.combine x cstars i)).card : ℚ) := by
      push_cast; rfl
    rw [h_nat]; exact hcast
  -- Per-seed lower bound: for each x ∈ B_set with witness Tx,
  -- |Tc ∩ {agree at x}| ≥ |Tx \ Ttilde| ≥ n(1-γ) - t.
  have h_per_seed : ∀ x ∈ B_set,
      ((Tc.filter
        (fun i => G.combine x us i = G.combine x cstars i)).card : ℚ) ≥
        (n : ℚ) * (1 - γ) - t := by
    intro x hx
    obtain ⟨Tx, hTx_size, hTx_agree⟩ := h_agree x hx
    -- Tx \ Ttilde ⊆ filter (Tc).
    have h_Tx_diff_sub :
        Tx \ Ttilde ⊆
          Tc.filter (fun i => G.combine x us i = G.combine x cstars i) := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      obtain ⟨hi_Tx, hi_notT⟩ := hi
      rw [Finset.mem_filter, hTc_mem]
      exact ⟨hi_notT, hTx_agree i hi_Tx⟩
    have h_card_le_nat :
        (Tx \ Ttilde).card ≤
          (Tc.filter (fun i => G.combine x us i = G.combine x cstars i)).card :=
      Finset.card_le_card h_Tx_diff_sub
    have h_card_le_Q :
        ((Tx \ Ttilde).card : ℚ) ≤
          ((Tc.filter (fun i => G.combine x us i = G.combine x cstars i)).card : ℚ) := by
      exact_mod_cast h_card_le_nat
    -- |Ttilde| - |Tx| (as ℕ-truncated subtraction) wait, we want |Tx| - |Ttilde|.
    -- Use Finset.le_card_sdiff: #Ttilde - #Tx ≤ #(Tx \ Ttilde) — wrong order.
    -- We need: Tx.card - Ttilde.card ≤ (Tx \ Ttilde).card.
    -- Note `Finset.le_card_sdiff s t : #t - #s ≤ #(t \ s)`, so with s := Ttilde,
    -- t := Tx: #Tx - #Ttilde ≤ #(Tx \ Ttilde). Exactly what we want.
    have h_diff_ge_nat : Tx.card - Ttilde.card ≤ (Tx \ Ttilde).card :=
      Finset.le_card_sdiff Ttilde Tx
    have h_diff_ge_Q :
        ((Tx \ Ttilde).card : ℚ) ≥ ((Tx.card : ℚ)) - t := by
      by_cases h : Tx.card ≥ Ttilde.card
      · have hcast :
            ((Tx.card - Ttilde.card : ℕ) : ℚ) = ((Tx.card : ℚ)) - t :=
          Nat.cast_sub h
        have : (((Tx.card - Ttilde.card : ℕ) : ℚ)) ≤ ((Tx \ Ttilde).card : ℚ) := by
          exact_mod_cast h_diff_ge_nat
        linarith
      · push_neg at h
        -- Tx.card < Ttilde.card so Tx.card - Ttilde.card ≤ 0 ≤ |Tx \ Ttilde|.
        have h_pos : (0 : ℚ) ≤ ((Tx \ Ttilde).card : ℚ) := by exact_mod_cast Nat.zero_le _
        have hQ : ((Tx.card : ℚ)) - t < 0 := by
          have h_cast_lt : ((Tx.card : ℚ)) < ((Ttilde.card : ℚ)) := by exact_mod_cast h
          have : t = ((Ttilde.card : ℚ)) := ht_def
          linarith
        linarith
    -- Combine: |filter Tc| ≥ |Tx \ Ttilde| ≥ |Tx| - t ≥ n(1-γ) - t.
    have hTx_size_Q : ((Tx.card : ℚ)) ≥ (n : ℚ) * (1 - γ) := hTx_size
    linarith
  -- Per-seed lower bound: |P| ≥ b · (n(1-γ) - t).
  have h_lower : (Pset.card : ℚ) ≥ b * ((n : ℚ) * (1 - γ) - t) := by
    rw [hP_eq_sum_over_x]
    have hsum :
        ∑ x ∈ B_set,
            ((Tc.filter
              (fun i => G.combine x us i = G.combine x cstars i)).card : ℚ)
          ≥ ∑ _ ∈ B_set, ((n : ℚ) * (1 - γ) - t) :=
      Finset.sum_le_sum h_per_seed
    have hconst :
        (∑ _ ∈ B_set, ((n : ℚ) * (1 - γ) - t)) =
          (B_set.card : ℚ) * ((n : ℚ) * (1 - γ) - t) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith [hconst ▸ hsum]
  -- Combining lower & upper: b · (n(1-γ) - t) ≤ (n - t)·(ℓ-1).
  have h_combined : b * ((n : ℚ) * (1 - γ) - t) ≤ ((n : ℚ) - t) * (ℓ - 1 : ℚ) := by
    have := le_trans h_lower h_upper
    rw [hTc_card_Q] at this
    exact this
  -- After `push_neg`, `h_le : t < n*(1-γ) - 1`, so `s := n(1-γ) - t > 1`.
  have hs_gt_one : (1 : ℚ) < (n : ℚ) * (1 - γ) - t := by linarith
  -- The strengthened hypothesis: b > (nγ+1)·(ℓ-1).
  have hb_lower : b > ((n : ℚ) * γ + 1) * (ℓ - 1) := h_size
  -- Note: (n - t) = (n(1-γ) - t) + nγ.
  have h_nt_eq : ((n : ℚ) - t) = ((n : ℚ) * (1 - γ) - t) + (n : ℚ) * γ := by ring
  -- ℓ ≥ 1 so (ℓ-1) ≥ 0, and (nγ+1) ≥ 1 ≥ 0, hence (nγ+1)*(ℓ-1) ≥ 0, so b > 0.
  have hℓ_ge_one : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
  have hℓm_nn : (0 : ℚ) ≤ (ℓ : ℚ) - 1 := by linarith
  have hnγ_nn : (0 : ℚ) ≤ (n : ℚ) * γ := mul_nonneg (le_of_lt hn_pos) hγ_pos
  -- From the combined bound, derive `s · (b - (ℓ-1)) ≤ nγ · (ℓ-1)`.
  -- Rewrite `(n - t) = s + nγ` then expand.
  have h_combined' :
      ((n : ℚ) * (1 - γ) - t) * (b - (ℓ - 1)) ≤ (n : ℚ) * γ * (ℓ - 1) := by
    have h_expand : ((n : ℚ) - t) * (ℓ - 1 : ℚ) =
        ((n : ℚ) * (1 - γ) - t) * (ℓ - 1) + (n : ℚ) * γ * (ℓ - 1) := by
      rw [h_nt_eq]; ring
    -- h_combined: b * s ≤ (s + nγ)·(ℓ-1) = s·(ℓ-1) + nγ·(ℓ-1).
    have h1 : b * ((n : ℚ) * (1 - γ) - t) ≤
        ((n : ℚ) * (1 - γ) - t) * (ℓ - 1) + (n : ℚ) * γ * (ℓ - 1) := by
      have := h_combined
      linarith [h_expand]
    -- So `b·s - s·(ℓ-1) ≤ nγ·(ℓ-1)`, i.e., `s·(b - (ℓ-1)) ≤ nγ·(ℓ-1)`.
    nlinarith [h1]
  -- Now: s > 1, b - (ℓ-1) ≥ 0 (since b > (nγ+1)(ℓ-1) ≥ (ℓ-1)).
  have h_b_minus_nn : (0 : ℚ) < b - ((ℓ : ℚ) - 1) := by
    -- b > (nγ+1)(ℓ-1) ≥ 1·(ℓ-1) = (ℓ-1), since nγ+1 ≥ 1.
    have h_nγ1 : (1 : ℚ) ≤ (n : ℚ) * γ + 1 := by linarith
    have h_step : ((n : ℚ) * γ + 1) * (ℓ - 1) ≥ 1 * ((ℓ : ℚ) - 1) :=
      mul_le_mul_of_nonneg_right h_nγ1 hℓm_nn
    have : (1 : ℚ) * ((ℓ : ℚ) - 1) = (ℓ : ℚ) - 1 := by ring
    linarith
  -- From s > 1 and s·(b - (ℓ-1)) ≤ nγ·(ℓ-1): (b - (ℓ-1)) < s·(b - (ℓ-1)) ≤ nγ·(ℓ-1).
  have h_step1 : b - ((ℓ : ℚ) - 1) < ((n : ℚ) * (1 - γ) - t) * (b - ((ℓ : ℚ) - 1)) := by
    nlinarith [hs_gt_one, h_b_minus_nn]
  have h_step2 : b - ((ℓ : ℚ) - 1) < (n : ℚ) * γ * (ℓ - 1) := lt_of_lt_of_le h_step1 h_combined'
  -- So b < nγ·(ℓ-1) + (ℓ-1) = (nγ+1)·(ℓ-1), contradicting `b > (nγ+1)·(ℓ-1)`.
  have h_contra : b < ((n : ℚ) * γ + 1) * ((ℓ : ℚ) - 1) := by nlinarith
  exact absurd hb_lower (not_lt.mpr (le_of_lt h_contra))

end LinearCodes
