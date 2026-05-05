/-
# Unique-decoding regime — Theorem 6.1 setup

Phase 1 of the swarm plan for BCGM25 Theorem 6.1: extract the
*witness codeword* and *witness set* from each "bad" seed in the
MCA bad event, and prove their basic properties.

In the MCA bad event at γ for `(G, c, us)`:
```
∃ T : Finset (Fin n), (T.card : ℚ) ≥ n*(1−γ) ∧
  InRestrictedCode c T (G.combine x us) ∧
  ∃ j, ¬ InRestrictedCode c T (us j)
```
the existential `InRestrictedCode c T (G.combine x us) := ∃ v ∈ c, ...`
provides a witness codeword. We extract it via classical choice.
-/

import LinearCodes.MCA.Definitions
import LinearCodes.MCA.SeedProbLemmas
import LinearCodes.MCA.InducedCode
import LinearCodes.MCA.Properties
import LinearCodes.Algebraic.Code

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-- Bundled witness data for a seed `x` in the MCA bad event at `γ`:
the agreement set `T`, the witness codeword `cw ∈ c`, agreement on `T`,
and a row index `j` whose restriction is not in `c|T`. -/
structure MCABadWitness (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (γ : ℚ) (x : S) where
  T : Finset (Fin n)
  cw : Fin n → F
  T_size : (T.card : ℚ) ≥ n * (1 - γ)
  cw_mem : cw ∈ c
  agree : ∀ i ∈ T, cw i = G.combine x us i
  bad_row : ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)

/-- Extract a structured witness from membership in the MCA bad event.
Uses classical choice. -/
noncomputable def mkMCABadWitness
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (γ : ℚ) (x : S)
    (h_bad : ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) :
    MCABadWitness G c us γ x :=
  let T := h_bad.choose
  let hT_full := h_bad.choose_spec
  let h_inRest := hT_full.2.1
  let cw := h_inRest.choose
  let hcw_full := h_inRest.choose_spec
  { T := T
    cw := cw
    T_size := hT_full.1
    cw_mem := hcw_full.1
    agree := hcw_full.2
    bad_row := hT_full.2.2 }

/-! ### Uniqueness of the witness codeword in the unique-decoding regime -/

/-- In the unique-decoding regime (tight γ), the witness codeword for a
given seed is determined by the agreement set: if `cw, cw'` are both
codewords agreeing with `G.combine x us` on a set `T` of size `≥ k`,
then `cw = cw'`. Direct from `agreement_implies_eq_of_MDS`. -/
theorem witness_codeword_unique_of_MDS
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    (u : Fin n → F) {T : Finset (Fin n)} (hT : k ≤ T.card)
    {cw cw' : Fin n → F}
    (hcw : cw ∈ c) (hcw' : cw' ∈ c)
    (h_agree : ∀ i ∈ T, cw i = u i) (h_agree' : ∀ i ∈ T, cw' i = u i) :
    cw = cw' := by
  apply agreement_implies_eq_of_MDS h_MDS hcw hcw' hT
  intros i hi
  rw [h_agree i hi, ← h_agree' i hi]

/-! ### Distinct bad seeds give distinct witness sets -/

/-- For two bad seeds `x, x'` whose witness sets `T, T'` overlap on
≥ `k` coordinates and whose linear combinations `G.combine x us` and
`G.combine x' us` agree on the overlap, the witness codewords are
equal. (Setup for the pairwise-intersection bound.) -/
theorem witness_codewords_eq_of_overlap_MDS
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    (G : Generator F S ℓ) (us : Fin ℓ → (Fin n → F))
    {x x' : S}
    {T T' : Finset (Fin n)} (h_overlap : k ≤ (T ∩ T').card)
    {cw cw' : Fin n → F}
    (hcw : cw ∈ c) (hcw' : cw' ∈ c)
    (h_agree : ∀ i ∈ T, cw i = G.combine x us i)
    (h_agree' : ∀ i ∈ T', cw' i = G.combine x' us i)
    (h_combine_eq : ∀ i ∈ T ∩ T', G.combine x us i = G.combine x' us i) :
    cw = cw' := by
  apply agreement_implies_eq_of_MDS h_MDS hcw hcw' h_overlap
  intros i hi
  rw [Finset.mem_inter] at hi
  calc cw i = G.combine x us i := h_agree i hi.1
    _ = G.combine x' us i := h_combine_eq i (Finset.mem_inter.mpr hi)
    _ = cw' i := (h_agree' i hi.2).symm

/-! ### Phase 2: Pairwise structural bounds for witness sets -/

/-- The witness set `T` is contained in the agreement set of the witness
codeword `cw` and the linear combination `G.combine x us`. Direct from
the `agree` field of `MCABadWitness`. -/
theorem witness_T_subset_agreementSet
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    {us : Fin ℓ → (Fin n → F)} {γ : ℚ} {x : S}
    (w : MCABadWitness G c us γ x) :
    w.T ⊆ agreementSet w.cw (G.combine x us) := by
  intro i hi
  rw [mem_agreementSet]
  exact w.agree i hi

/-- The intersection of two witness sets is contained in the intersection
of their respective agreement-with-combine sets. -/
theorem witness_pairwise_T_inter_subset
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    {us : Fin ℓ → (Fin n → F)} {γ : ℚ}
    {x x' : S}
    (w : MCABadWitness G c us γ x) (w' : MCABadWitness G c us γ x') :
    w.T ∩ w'.T ⊆
      agreementSet w.cw (G.combine x us) ∩ agreementSet w'.cw (G.combine x' us) := by
  intros i hi
  rw [Finset.mem_inter] at hi ⊢
  exact ⟨witness_T_subset_agreementSet w hi.1, witness_T_subset_agreementSet w' hi.2⟩

/-- **Phase 2 key bound.** If two witnesses have distinct codewords,
their witness sets intersect in fewer than `k` positions (the MDS
dimension). The proof chains through the agreement-set inclusion plus
`MDS_distinct_codewords_disagree`. -/
theorem witness_pairwise_intersection_lt_k_of_distinct_codewords
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    {G : Generator F S ℓ} {us : Fin ℓ → (Fin n → F)} {γ : ℚ}
    {x x' : S}
    (w : MCABadWitness G c us γ x) (w' : MCABadWitness G c us γ x')
    (h_distinct : w.cw ≠ w'.cw) :
    (∀ i ∈ w.T ∩ w'.T, G.combine x us i = G.combine x' us i) →
    (w.T ∩ w'.T).card < k := by
  intro h_combine_eq
  have h_subset : w.T ∩ w'.T ⊆ agreementSet w.cw w'.cw := by
    intro i hi
    rw [Finset.mem_inter] at hi
    rw [mem_agreementSet]
    have h1 : w.cw i = G.combine x us i := w.agree i hi.1
    have h2 : G.combine x us i = G.combine x' us i :=
      h_combine_eq i (Finset.mem_inter.mpr hi)
    have h3 : w'.cw i = G.combine x' us i := w'.agree i hi.2
    rw [h1, h2, ← h3]
  have h_card_le : (w.T ∩ w'.T).card ≤ (agreementSet w.cw w'.cw).card :=
    Finset.card_le_card h_subset
  have h_lt : (agreementSet w.cw w'.cw).card < k :=
    MDS_distinct_codewords_disagree h_MDS w.cw_mem w'.cw_mem h_distinct
  exact lt_of_le_of_lt h_card_le h_lt

/-! ### Generator MDS predicate -/

/-- A generator `G` is **MDS** if its induced code `C_G` is MDS — i.e.
the dot-map is injective (giving dim `C_G` = `ℓ`) and `C_G` has minimum
distance `|S| − ℓ + 1` (the Singleton bound). -/
def Generator.IsMDS [Fintype S]
    (G : Generator F S ℓ) : Prop :=
  Function.Injective G.dotMap ∧
  Generator.fnMinDistAtLeast G.inducedCode (Fintype.card S - ℓ + 1)

/-- The dot-map of an MDS generator is injective. -/
theorem Generator.IsMDS.dotMap_injective [Fintype S] {G : Generator F S ℓ}
    (h : G.IsMDS) : Function.Injective G.dotMap :=
  h.1

/-- The induced code of an MDS generator has the Singleton-bound min distance. -/
theorem Generator.IsMDS.inducedCode_minDist [Fintype S] {G : Generator F S ℓ}
    (h : G.IsMDS) :
    Generator.fnMinDistAtLeast G.inducedCode (Fintype.card S - ℓ + 1) :=
  h.2

/-- Specialised zero-evading bound for MDS generators: ε_ZE ≤ (ℓ-1)/|S|. -/
theorem Generator.IsMDS.zeroEvading_bound [Fintype S] [Nonempty S]
    {G : Generator F S ℓ} (h : G.IsMDS) :
    ZeroEvading G ((ℓ - 1 : ℚ) / Fintype.card S) := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ_pos
  · -- ℓ = 0: ZeroEvading is vacuously true (no nonzero v : Fin 0 → F)
    subst hℓ0
    intro v hv
    exfalso
    apply hv
    funext i
    exact i.elim0
  · -- ℓ ≥ 1: apply the induced-code lemma and relax via mono
    have h_inj := h.dotMap_injective
    have h_dist := h.inducedCode_minDist
    have hbound := ZeroEvading_from_inducedCode_min_dist G
      (Fintype.card S - ℓ + 1) h_dist h_inj
    apply ZeroEvading.mono _ hbound
    have hN_pos : (0 : ℚ) < Fintype.card S := by
      exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff_of_pos_right hN_pos]
    set N := Fintype.card S with hN_def
    by_cases hℓN : ℓ ≤ N
    · have hcast : ((N - ℓ + 1 : ℕ) : ℚ) = (N : ℚ) - ℓ + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hℓN, Nat.cast_one]
      rw [hcast]; linarith
    · push_neg at hℓN
      have h1 : (N - ℓ + 1 : ℕ) = 1 := by omega
      rw [show ((N - ℓ + 1 : ℕ) : ℚ) = (1 : ℚ) from by exact_mod_cast h1]
      have hNℓ : (N : ℚ) ≤ ℓ := by exact_mod_cast hℓN.le
      linarith

/-- **Matrix-invertibility form for MDS generators.** If `dotMap G v` vanishes at
`ℓ` distinct seeds, then `v = 0`. Equivalently, the matrix
`(G(xs i) j)_{i,j}` is invertible whenever `xs : Fin ℓ → S` is injective.
This is the algebraic backbone of BCGM25 Theorem 6.1's case `γ < 1/n`. -/
theorem Generator.IsMDS.dotMap_zero_at_distinct_seeds_implies_zero
    [Fintype S] [DecidableEq S]
    {G : Generator F S ℓ} (hG : G.IsMDS)
    {v : Fin ℓ → F} (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (h_zero : ∀ i, G.dotMap v (xs i) = 0) :
    v = 0 := by
  by_contra hv
  have h_inj := hG.dotMap_injective
  have h_dist := hG.inducedCode_minDist
  have hw_ne : G.dotMap v ≠ 0 := by
    intro hw_eq
    apply hv
    apply h_inj
    rw [hw_eq, Generator.dotMap_zero]
  have hw_mem : G.dotMap v ∈ G.inducedCode := by
    rw [Generator.mem_inducedCode_iff]
    exact ⟨v, fun _ => rfl⟩
  have h_lo : Fintype.card S - ℓ + 1 ≤ Generator.fnHammingWeight (G.dotMap v) :=
    h_dist (G.dotMap v) hw_mem hw_ne
  have h_zeros : ℓ ≤ (Finset.univ.filter fun s : S => G.dotMap v s = 0).card := by
    have h_image_card : (Finset.univ.image xs).card = ℓ := by
      rw [Finset.card_image_of_injective _ h_distinct]
      simp
    have h_image_subset :
        Finset.univ.image xs ⊆ Finset.univ.filter (fun s : S => G.dotMap v s = 0) := by
      intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨i, _, rfl⟩ := hs
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact h_zero i
    calc ℓ = (Finset.univ.image xs).card := h_image_card.symm
      _ ≤ (Finset.univ.filter fun s : S => G.dotMap v s = 0).card :=
          Finset.card_le_card h_image_subset
  have h_zero_eq :
      (Finset.univ.filter (fun s : S => G.dotMap v s = 0)).card =
        Fintype.card S - Generator.fnHammingWeight (G.dotMap v) :=
    fnZeroCount_eq_card_sub_fnHammingWeight (G.dotMap v)
  have h_w_le : Generator.fnHammingWeight (G.dotMap v) ≤ Fintype.card S :=
    fnHammingWeight_le_card (G.dotMap v)
  omega

/-! ### Phase 3 (target): Lemma 6.6 — strict-superset counting

Pure combinatorics: given subsets `Bᵢ ⊊ [n]` containing a fixed `A ⊊ [n]`
and pairwise (`ℓ`-fold) intersection equal to `A`, the count `t` is
bounded by `(ℓ−1) · (n − |A|)`. The cleanly-stateable form below
uses the simpler hypothesis that for *any* `j ∉ A`, the number of `Bᵢ`
containing `j` is at most `ℓ−1`. (BCGM25 §6 derives this from the
ℓ-fold intersection assumption via Lemma 6.5.)

This is a clean target for a math-expert agent. -/

/-- Counting bound: if subsets `Bᵢ ⊋ A` and each `j ∈ Bᵢ \ A` belongs
to at most `ℓ − 1` of the `Bᵢ`'s, then `t ≤ (ℓ − 1) · (n − |A|)`. -/
theorem strict_superset_count_bound {α : Type*} [Fintype α] [DecidableEq α]
    {ℓ t : ℕ} (hℓ : 1 ≤ ℓ)
    (A : Finset α) (Bs : Fin t → Finset α)
    (h_strict : ∀ i, A ⊂ Bs i)
    (h_degree : ∀ j ∉ A, (Finset.univ.filter fun i => j ∈ Bs i).card ≤ ℓ - 1) :
    t ≤ (ℓ - 1) * (Fintype.card α - A.card) := by
  have h_subset_A : A ⊆ (Finset.univ : Finset α) := Finset.subset_univ A
  have h_compl_card :
      ((Finset.univ : Finset α) \ A).card = Fintype.card α - A.card := by
    rw [Finset.card_sdiff_of_subset h_subset_A, Finset.card_univ]
  have h_lhs_card : ∀ j : α,
      (Finset.univ.filter fun i : Fin t => j ∈ Bs i).card =
        ∑ i : Fin t, (if j ∈ Bs i then 1 else 0 : ℕ) := by
    intro j
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h_rhs_card : ∀ i : Fin t,
      (Bs i \ A).card =
        ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (if j ∈ Bs i then 1 else 0 : ℕ) := by
    intro i
    rw [show (Bs i \ A) = ((Finset.univ : Finset α) \ A).filter (fun j => j ∈ Bs i) from ?_,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have h_double :
      ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (Finset.univ.filter fun i : Fin t => j ∈ Bs i).card =
        ∑ i : Fin t, (Bs i \ A).card := by
    simp_rw [h_lhs_card, h_rhs_card]
    rw [Finset.sum_comm]
  have h_bound_top :
      ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (Finset.univ.filter fun i : Fin t => j ∈ Bs i).card ≤
        (ℓ - 1) * (Fintype.card α - A.card) := by
    calc ∑ j ∈ ((Finset.univ : Finset α) \ A),
            (Finset.univ.filter fun i : Fin t => j ∈ Bs i).card
        ≤ ∑ _j ∈ ((Finset.univ : Finset α) \ A), (ℓ - 1) := by
            apply Finset.sum_le_sum
            intros j hj
            rw [Finset.mem_sdiff] at hj
            exact h_degree j hj.2
      _ = ((Finset.univ : Finset α) \ A).card * (ℓ - 1) := by
            rw [Finset.sum_const]; rfl
      _ = (Fintype.card α - A.card) * (ℓ - 1) := by rw [h_compl_card]
      _ = (ℓ - 1) * (Fintype.card α - A.card) := Nat.mul_comm _ _
  have h_bound_bot : t ≤ ∑ i : Fin t, (Bs i \ A).card := by
    have h1 : ∀ i : Fin t, 1 ≤ (Bs i \ A).card := by
      intro i
      obtain ⟨j, hj_in, hj_not⟩ := Finset.exists_of_ssubset (h_strict i)
      exact Finset.Nonempty.card_pos
        ⟨j, Finset.mem_sdiff.mpr ⟨hj_in, hj_not⟩⟩
    calc t = ∑ _i : Fin t, (1 : ℕ) := by simp
      _ ≤ ∑ i : Fin t, (Bs i \ A).card :=
            Finset.sum_le_sum (fun i _ => h1 i)
  calc t ≤ ∑ i : Fin t, (Bs i \ A).card := h_bound_bot
    _ = ∑ j ∈ ((Finset.univ : Finset α) \ A),
          (Finset.univ.filter fun i : Fin t => j ∈ Bs i).card :=
        h_double.symm
    _ ≤ (ℓ - 1) * (Fintype.card α - A.card) := h_bound_top

/-! ### §6.1 Case 1 (γ < 1/n): bound the bad set by ℓ − 1 -/

theorem linearMap_apply_combine_eq_dotMap (f : (Fin n → F) →ₗ[F] F) (G : Generator F S ℓ) (x : S) (us : Fin ℓ → (Fin n → F)) :
    f (G.combine x us) = G.dotMap (fun j => f (us j)) x := by
  have hsum : G.combine x us = ∑ j : Fin ℓ, G x j • us j := by
    ext i
    rw [Generator.combine, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum, map_sum]
  simp only [LinearMap.map_smul, Generator.dotMap_apply, smul_eq_mul]

theorem all_us_mem_of_combine_at_distinct_seeds [Fintype S] [DecidableEq S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F))
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (h_combines : ∀ i, G.combine (xs i) us ∈ c) :
    ∀ j, us j ∈ c := by
  intro j₀
  by_contra hu0
  obtain ⟨f, hf_nonzero, hc_ker⟩ := Submodule.exists_le_ker_of_notMem hu0
  let v : Fin ℓ → F := fun j => f (us j)
  have h_zero : ∀ i, G.dotMap v (xs i) = 0 := by
    intro i
    have hmem : G.combine (xs i) us ∈ LinearMap.ker f := hc_ker (h_combines i)
    have hf_zero : f (G.combine (xs i) us) = 0 := by
      exact (LinearMap.mem_ker).1 hmem
    simpa [v] using (linearMap_apply_combine_eq_dotMap f G (xs i) us).symm.trans hf_zero
  have hv : v = 0 := hG_MDS.dotMap_zero_at_distinct_seeds_implies_zero xs h_distinct h_zero
  exact hf_nonzero (by simpa [v] using congrFun hv j₀)


/-- **§6.1 Case 1 bound.** In the unique-decoding regime where `γ < 1/n`,
the MCA bad set has at most `ℓ − 1` elements (when at least one row
`us j` is outside `c`). Stated using `Set.ncard` to avoid imposing
`DecidablePred (· ∈ c)`. -/
theorem MCA_zero_bad_set_card_le_ell_minus_one
    [Fintype S] [DecidableEq S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F))
    (h_us_not_all : ∃ j, us j ∉ c) :
    {x : S | G.combine x us ∈ c}.ncard ≤ ℓ - 1 := by
  classical
  by_contra h_ge
  push_neg at h_ge
  have h_card_ge : ℓ ≤ {x : S | G.combine x us ∈ c}.ncard := by omega
  set bad : Finset S := Finset.univ.filter fun x => G.combine x us ∈ c with hbad_def
  have hbad_card : bad.card = {x : S | G.combine x us ∈ c}.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [hbad_def]
  have h_bad_ge : ℓ ≤ bad.card := hbad_card.symm ▸ h_card_ge
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_bad_ge
  let e : Fin ℓ ≃ T := (Finset.equivFinOfCardEq hT_card).symm
  let xs : Fin ℓ → S := fun i => (e i : S)
  have hxs_inj : Function.Injective xs := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have h_combines : ∀ i, G.combine (xs i) us ∈ c := by
    intro i
    have hxi_T : (e i : S) ∈ T := (e i).property
    have hxi_bad : (e i : S) ∈ bad := hT_sub hxi_T
    exact (Finset.mem_filter.mp hxi_bad).2
  have h_all_in : ∀ j, us j ∈ c :=
    all_us_mem_of_combine_at_distinct_seeds G hG_MDS c us xs hxs_inj h_combines
  obtain ⟨j, hj⟩ := h_us_not_all
  exact hj (h_all_in j)

/-- For `γ < 1/n` (with `n ≥ 1` and `γ ≥ 0`), the MCA bad event reduces
to plain code membership: `T` must be all of `[n]`. Hence the bad event
becomes `G.combine x us ∈ c ∧ ∃ j, us j ∉ c`, the same as at `γ = 0`. -/
theorem MCA_bad_event_at_small_gamma_eq_zero_event
    {γ : ℚ} (hγ_lt : (n : ℚ) * γ < 1) (hγ_pos : 0 ≤ γ) (hn : 0 < n)
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (x : S) :
    (∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ↔ (G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) := by
  constructor
  · rintro ⟨T, hT_size, hCombine, j, hj⟩
    have h_card_gt : ((T.card : ℕ) : ℚ) > (n : ℚ) - 1 := by
      have heq : (n : ℚ) * (1 - γ) = (n : ℚ) - n * γ := by ring
      have hge : ((T.card : ℕ) : ℚ) ≥ (n : ℚ) - n * γ := by rw [← heq]; exact hT_size
      linarith
    have hT_card_ge_n : n ≤ T.card := by
      by_contra h_lt
      push_neg at h_lt
      have hsub : T.card ≤ n - 1 := by omega
      have hcast : ((T.card : ℕ) : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hsub
      have hcast2 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        rw [Nat.cast_sub hn, Nat.cast_one]
      rw [hcast2] at hcast
      linarith
    have hT_le_univ : T ⊆ Finset.univ := Finset.subset_univ T
    have hT_eq_univ : T = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le hT_le_univ
      rw [Finset.card_univ, Fintype.card_fin]
      exact hT_card_ge_n
    rw [hT_eq_univ] at hCombine hj
    rw [inRestrictedCode_univ_iff] at hCombine
    refine ⟨hCombine, j, ?_⟩
    intro h_in_c
    apply hj
    rw [inRestrictedCode_univ_iff]
    exact h_in_c
  · rintro ⟨hCombine, j, hj⟩
    refine ⟨Finset.univ, ?_, ?_, j, ?_⟩
    · rw [Finset.card_univ, Fintype.card_fin]
      have hn_nn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
      have hnγ : 0 ≤ (n : ℚ) * γ := mul_nonneg hn_nn hγ_pos
      have heq : (n : ℚ) * (1 - γ) = (n : ℚ) - n * γ := by ring
      rw [heq]; linarith
    · rw [inRestrictedCode_univ_iff]; exact hCombine
    · intro h
      rw [inRestrictedCode_univ_iff] at h
      exact hj h

/-! ### §6.1 Case 1 capstone: MCA bound for γ < 1/n -/

/-- **§6.1 Case 1 MCA bound.** When the generator is MDS and `γ ∈ [0, 1/n)`,
the MCA bad-event probability is bounded by `(ℓ - 1) / |S|`. This is the
small-γ branch of BCGM25 Theorem 6.1's MCA error formula
(`max{n·γ, 1} · (ℓ-1)/|S|` simplifies to `(ℓ-1)/|S|` when `n·γ < 1`).
Requires `0 < ℓ` since otherwise the right-hand side is negative. -/
theorem MCA_unique_decoding_small_gamma_bound
    [Fintype S] [DecidableEq S] [Nonempty S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_lt : (n : ℚ) * γ < 1) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ (ℓ - 1 : ℚ) / Fintype.card S := by
  by_cases h_us : ∃ j, us j ∉ c
  · have hequiv : ∀ x,
      (∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
      ↔ (G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) :=
      fun x => MCA_bad_event_at_small_gamma_eq_zero_event hγ_lt hγ_pos hn G c us x
    rw [seedProb_congr hequiv]
    have hequiv2 : ∀ x,
      (G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) ↔ G.combine x us ∈ c :=
      fun x => ⟨fun h => h.1, fun h => ⟨h, h_us⟩⟩
    rw [seedProb_congr hequiv2]
    have h_ncard : {x : S | G.combine x us ∈ c}.ncard ≤ ℓ - 1 :=
      MCA_zero_bad_set_card_le_ell_minus_one G hG_MDS c us h_us
    have h_le := seedProb_le_ncard_div (fun x => G.combine x us ∈ c) (ℓ - 1) h_ncard
    have hcast : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := by
      rw [Nat.cast_sub hℓ, Nat.cast_one]
    rw [hcast] at h_le
    exact h_le
  · push_neg at h_us
    have hequiv_false : ∀ x,
      (∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
      ↔ False := by
      intro x
      constructor
      · rintro ⟨T, _, _, j, hnj⟩
        exact hnj (inRestrictedCode_of_mem c T (h_us j))
      · intro h; exact h.elim
    rw [seedProb_congr hequiv_false]
    rw [seedProb_const_false]
    apply div_nonneg
    · have h1 : (1 : ℚ) ≤ ℓ := by exact_mod_cast hℓ
      linarith
    · exact_mod_cast Nat.zero_le _

/-! ### MDS dimension exactness -/

/-- For an MDS generator, the induced code has dimension exactly `ℓ`. -/
theorem Generator.IsMDS.inducedCode_finrank_eq
    [Fintype S] {G : Generator F S ℓ} (h : G.IsMDS) :
    Module.finrank F G.inducedCode = ℓ := by
  simpa [Generator.inducedCode, Module.finrank_fin_fun] using
    LinearMap.finrank_range_of_inj (f := G.dotMap) h.dotMap_injective

/-- An MDS generator's `dotMap` is a linear equivalence onto its image
(the induced code), with the source domain `Fin ℓ → F` having full
dimension `ℓ`. -/
theorem Generator.IsMDS.dotMap_range_eq_inducedCode
    [Fintype S] {G : Generator F S ℓ} (h : G.IsMDS) :
    LinearMap.range G.dotMap = G.inducedCode := rfl

end LinearCodes
