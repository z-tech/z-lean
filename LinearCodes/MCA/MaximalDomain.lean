/-
# Maximal agreement / CA domains (BCGM25 §5–§6.1 setup)

For BCGM25 Theorem 6.1 Case 2 (γ ≥ 1/n), we need:

* **Agreement domain** between `u` and `c`: a coordinate set `T` on which
  `u` agrees with some codeword of `c`. Equivalent to `InRestrictedCode c T u`.
* **CA domain** between `(uⱼ)ⱼ` and `c`: a coordinate set `T` on which
  *each* `uⱼ` agrees with some codeword (correlated agreement).
* **Maximal agreement / CA domains**: maximal under inclusion.

This file defines these predicates and stages BCGM25 Lemmas 6.4 and 6.5.
Lemma 6.6 (`strict_superset_count_bound`) is already proved in
`LinearCodes/MCA/UniqueDecoding.lean`.
-/

import LinearCodes.MCA.UniqueDecoding

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ : ℕ}

/-! ### Agreement / CA domain definitions -/

/-- `T` is an *agreement domain* between `u` and `c` if `u|T ∈ c|T`, i.e.
some codeword of `c` agrees with `u` on every coordinate of `T`.

This is just a rename of `InRestrictedCode` for clarity. -/
def IsAgreementDomain (c : Submodule F (Fin n → F)) (u : Fin n → F)
    (T : Finset (Fin n)) : Prop :=
  InRestrictedCode c T u

/-- `T` is a *maximal agreement domain* between `u` and `c` if it is
maximal under inclusion among agreement domains. -/
def IsMaxAgreementDomain (c : Submodule F (Fin n → F)) (u : Fin n → F)
    (T : Finset (Fin n)) : Prop :=
  IsAgreementDomain c u T ∧ ∀ T' : Finset (Fin n), T ⊂ T' → ¬ IsAgreementDomain c u T'

/-- `T` is a *CA domain* between `(uⱼ)ⱼ : Fin ℓ → (Fin n → F)` and `c`
if every `uⱼ|T` lies in `c|T`. -/
def IsCADomain (c : Submodule F (Fin n → F)) (us : Fin ℓ → (Fin n → F))
    (T : Finset (Fin n)) : Prop :=
  ∀ j : Fin ℓ, InRestrictedCode c T (us j)

/-- `T` is a *maximal CA domain* if it is maximal under inclusion among
CA domains. -/
def IsMaxCADomain (c : Submodule F (Fin n → F)) (us : Fin ℓ → (Fin n → F))
    (T : Finset (Fin n)) : Prop :=
  IsCADomain c us T ∧ ∀ T' : Finset (Fin n), T ⊂ T' → ¬ IsCADomain c us T'

/-! ### Basic properties -/

/-- A maximal agreement domain is in particular an agreement domain. -/
theorem IsMaxAgreementDomain.isAgreementDomain
    {c : Submodule F (Fin n → F)} {u : Fin n → F} {T : Finset (Fin n)}
    (h : IsMaxAgreementDomain c u T) :
    IsAgreementDomain c u T := h.1

/-- A maximal CA domain is in particular a CA domain. -/
theorem IsMaxCADomain.isCADomain
    {c : Submodule F (Fin n → F)} {us : Fin ℓ → (Fin n → F)} {T : Finset (Fin n)}
    (h : IsMaxCADomain c us T) :
    IsCADomain c us T := h.1

/-! ### BCGM25 Lemma 6.4: intersection of max agreement → max CA -/

/-- **BCGM25 Lemma 6.4.** Let `G` be an MDS generator. Suppose for `ℓ`
distinct seeds `xs : Fin ℓ → S` and rows `us : Fin ℓ → (Fin n → F)`,
each `Aⱼ` is a maximal agreement domain between `G.combine (xs j) us`
and `c`. If `T` equals the `ℓ`-fold intersection (i.e., `T ⊆ each Aⱼ`
and `T` is maximal under that condition) and has size strictly greater
than `n - δ_C`, then `T` is a maximal CA domain. -/
theorem maxAgreement_intersection_isMaxCA
    [DecidableEq S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)} {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (As : Fin ℓ → Finset (Fin n))
    (h_max_agree : ∀ j, IsMaxAgreementDomain c (G.combine (xs j) us) (As j))
    (T : Finset (Fin n)) (h_T_inter : ∀ j, T ⊆ As j)
    (h_T_max_inter : ∀ T₀ : Finset (Fin n), (∀ j, T₀ ⊆ As j) → T₀ ⊆ T)
    (h_T_size : T.card > n - δ_C) :
    IsMaxCADomain c us T := by
  have h_agree_T : ∀ j, IsAgreementDomain c (G.combine (xs j) us) T := fun j =>
    inRestrictedCode_mono (h_T_inter j) (h_max_agree j).isAgreementDomain
  have h_uniq : ∀ {u v : Fin n → F}, u ∈ c → v ∈ c →
      ∀ {U : Finset (Fin n)}, U.card > n - δ_C →
      (∀ i ∈ U, u i = v i) → u = v := by
    intro u v hu hv U hU h_agree
    by_contra h_ne
    have h_sub_mem : u - v ∈ c := c.sub_mem hu hv
    have h_sub_ne : u - v ≠ 0 := sub_ne_zero.mpr h_ne
    have h_lo := h_minDist (u - v) h_sub_mem h_sub_ne
    have h_eq := hammingDistance_eq_hammingWeight_sub u v
    have h_hi := hammingDistance_le_of_agree_on h_agree
    rw [← h_eq] at h_lo
    have hU_le_n : U.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ U)
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have : δ_C ≤ n - U.card := h_lo.trans h_hi
    omega
  refine ⟨?_, ?_⟩
  · -- T is a CA domain (algebraic core — matrix inversion).
    sorry
  · intro T' hTT' hT'_CA
    obtain ⟨hTsub, hTne⟩ := hTT'
    have h_T'_agree : ∀ j, IsAgreementDomain c (G.combine (xs j) us) T' := by
      intro j
      choose v hv_mem hv_agree using
        fun k => (hT'_CA k : InRestrictedCode c T' (us k))
      refine ⟨∑ k, G (xs j) k • v k, ?_, ?_⟩
      · exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hv_mem k))
      · intro i hi
        rw [Generator.combine_apply]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [hv_agree k i hi]
    choose cw' hcw'_mem hcw'_agree using
      fun j => (h_T'_agree j : InRestrictedCode c T' (G.combine (xs j) us))
    choose caw hcaw_mem hcaw_agree using
      fun j => ((h_max_agree j).isAgreementDomain :
        InRestrictedCode c (As j) (G.combine (xs j) us))
    have h_eq_witnesses : ∀ j, cw' j = caw j := by
      intro j
      apply h_uniq (hcw'_mem j) (hcaw_mem j) h_T_size
      intro i hi
      have hi_T' : i ∈ T' := hTsub hi
      have hi_Aj : i ∈ As j := h_T_inter j hi
      rw [hcw'_agree j i hi_T', ← hcaw_agree j i hi_Aj]
    have h_union_agree : ∀ j,
        IsAgreementDomain c (G.combine (xs j) us) (As j ∪ T') := by
      intro j
      refine ⟨caw j, hcaw_mem j, ?_⟩
      intro i hi
      rw [Finset.mem_union] at hi
      rcases hi with hAj | hT'
      · exact hcaw_agree j i hAj
      · rw [← h_eq_witnesses j]; exact hcw'_agree j i hT'
    have h_T'_sub_As : ∀ j, T' ⊆ As j := by
      intro j
      by_contra hnot
      have h_strict : As j ⊂ As j ∪ T' := by
        refine ⟨Finset.subset_union_left, ?_⟩
        intro h_eq_sup
        apply hnot
        intro i hi_T'
        have : i ∈ As j ∪ T' := Finset.mem_union_right _ hi_T'
        exact h_eq_sup this
      exact (h_max_agree j).2 _ h_strict (h_union_agree j)
    have h_T'_sub_T : T' ⊆ T := h_T_max_inter T' h_T'_sub_As
    exact hTne h_T'_sub_T

/-! ### BCGM25 Lemma 6.5: ℓ-fold intersection equals the maximal CA domain -/

/-- **BCGM25 Lemma 6.5.** Let `A` be a maximal CA domain of size `> n - δ_C`.
If `B₁,…,Bₜ` are maximal agreement domains all containing `A`, then any
`ℓ` distinct of them have intersection equal to `A`. Stated using a
witness `T` for the intersection of any ℓ chosen Bᵢs. -/
theorem maxAgreement_inter_eq_maxCA
    [DecidableEq S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)} {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {A : Finset (Fin n)} (hA_max : IsMaxCADomain c us A)
    (hA_size : A.card > n - δ_C)
    {t : ℕ} (xs : Fin t → S) (h_distinct : Function.Injective xs)
    (Bs : Fin t → Finset (Fin n))
    (h_max : ∀ i, IsMaxAgreementDomain c (G.combine (xs i) us) (Bs i))
    (h_super : ∀ i, A ⊆ Bs i)
    (is : Fin ℓ → Fin t) (h_inj_is : Function.Injective is)
    (T : Finset (Fin n)) (h_T_inter : ∀ j, T ⊆ Bs (is j))
    (h_T_max : ∀ T' : Finset (Fin n), (∀ j, T' ⊆ Bs (is j)) → T' ⊆ T) :
    T = A := by
  have hA_sub_T : A ⊆ T := h_T_max A (fun j => h_super (is j))
  have hT_size : T.card > n - δ_C :=
    lt_of_lt_of_le hA_size (Finset.card_le_card hA_sub_T)
  have hT_isMaxCA : IsMaxCADomain c us T :=
    maxAgreement_intersection_isMaxCA G hG_MDS h_minDist us
      (fun j => xs (is j)) (h_distinct.comp h_inj_is)
      (fun j => Bs (is j)) (fun j => h_max (is j))
      T h_T_inter h_T_max hT_size
  by_contra h_ne
  have hA_ssub_T : A ⊂ T := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hA_sub_T, fun h_eq => h_ne h_eq.symm⟩
  exact hA_max.2 T hA_ssub_T hT_isMaxCA.isCADomain

/-! ### Existence and uniqueness of maximal CA domain -/

/-- Every CA domain is contained in a maximal CA domain. -/
theorem exists_max_CA_domain_extending
    {c : Submodule F (Fin n → F)} {us : Fin ℓ → (Fin n → F)}
    {T₀ : Finset (Fin n)} (h₀ : IsCADomain c us T₀) :
    ∃ T : Finset (Fin n), T₀ ⊆ T ∧ IsMaxCADomain c us T := by
  classical
  let goodSets : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T₀ ⊆ T ∧ IsCADomain c us T)
  have h_nonempty : goodSets.Nonempty := by
    refine ⟨T₀, ?_⟩
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨subset_refl _, h₀⟩
  obtain ⟨T, hT_mem, hT_max⟩ :=
    goodSets.exists_max_image (fun T => T.card) h_nonempty
  have hT_props : T₀ ⊆ T ∧ IsCADomain c us T := by
    have := hT_mem
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  refine ⟨T, hT_props.1, hT_props.2, ?_⟩
  intro T' hT'_ssub hT'_CA
  have hT'_good : T' ∈ goodSets := by
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hT_props.1.trans hT'_ssub.subset, hT'_CA⟩
  have h_card_lt : T.card < T'.card := Finset.card_lt_card hT'_ssub
  have h_card_le : T'.card ≤ T.card := hT_max T' hT'_good
  omega

/-- The empty set is always a CA domain (trivially: for any T = ∅,
the agreement condition is vacuous, take any codeword e.g. 0). -/
theorem isCADomain_empty (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) :
    IsCADomain c us ∅ := by
  intro j
  exact inRestrictedCode_empty c (us j)

/-- A CA domain is also an agreement domain for each row. -/
theorem IsCADomain.isAgreementDomain
    {c : Submodule F (Fin n → F)} {us : Fin ℓ → (Fin n → F)} {T : Finset (Fin n)}
    (h : IsCADomain c us T) (j : Fin ℓ) :
    IsAgreementDomain c (us j) T := h j

/-- Witness codeword for an agreement domain. -/
theorem IsAgreementDomain.witness
    {c : Submodule F (Fin n → F)} {u : Fin n → F} {T : Finset (Fin n)}
    (h : IsAgreementDomain c u T) :
    ∃ v ∈ c, ∀ i ∈ T, v i = u i := h

/-- A maximal agreement domain has a witness codeword. -/
theorem IsMaxAgreementDomain.witness
    {c : Submodule F (Fin n → F)} {u : Fin n → F} {T : Finset (Fin n)}
    (h : IsMaxAgreementDomain c u T) :
    ∃ v ∈ c, ∀ i ∈ T, v i = u i := h.1

/-! ### §6.1 Case 2: γ ≥ 1/n MCA bound -/

/-- **§6.1 Case 2 MCA bound.** For an MDS generator and γ ∈ [1/n, δ_C/(ℓ+1)),
the MCA bad-event probability is bounded by `n·γ·(ℓ-1)/|S|`. The proof
uses Lemmas 6.4-6.6 to bound the bad seed count via Corrádi.

This is the large-γ branch of BCGM25 Theorem 6.1's MCA error formula. -/
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
    ≤ n * γ * (ℓ - 1 : ℚ) / Fintype.card S := by
  sorry

/-! ### BCGM25 Theorem 6.1 unified bound (unique-decoding regime) -/

/-- **BCGM25 Theorem 6.1 (unique-decoding regime).** For an MDS generator
and `γ < δ_C/(n·(ℓ+1))`, the MCA bad-event probability is bounded by
`max{n·γ, 1} · (ℓ-1) / |S|`. The proof case-splits on `γ < 1/n` (Case 1,
proved as `MCA_unique_decoding_small_gamma_bound`) vs `γ ≥ 1/n` (Case 2,
proved as `MCA_unique_decoding_large_gamma_bound`). -/
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
    ≤ max ((n : ℚ) * γ) 1 * (ℓ - 1) / Fintype.card S := by
  sorry

end LinearCodes
