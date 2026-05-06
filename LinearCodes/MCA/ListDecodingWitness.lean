/-
# List-decoding bad witness for BCGM25 §6.2

Group A of §6.2 decomposition: the list-version of `MCABadWitness`.
For each bad seed `x`, instead of one witness codeword `cw`, there can
be up to `L` candidate codewords agreeing on the witness set `T`.
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.ListDecoding
import LinearCodes.MCA.Case2Subtargets

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ L : ℕ}

/-! ### A1: List bad-witness structure -/

/-- A1: List-decoding analog of `MCABadWitness`. The agreement set `T` may
admit several codewords (up to `L`) all agreeing with `G.combine x us` on `T`. -/
structure MCAListBadWitness (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (γ : ℚ) (L : ℕ) (x : S) where
  T       : Finset (Fin n)
  cws     : Fin L → (Fin n → F)
  T_size  : (T.card : ℚ) ≥ n * (1 - γ)
  cws_mem : ∀ ℓ_idx, cws ℓ_idx ∈ c
  agree   : ∀ ℓ_idx, ∀ i ∈ T, cws ℓ_idx i = G.combine x us i
  bad_row : ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)

/-! ### A2: Extractor from list-decodable bad event -/

/-- A2: Extract a list witness from the list-decodable bad event hypothesis. -/
noncomputable def mkMCAListBadWitness
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (γ : ℚ) (L : ℕ) [Fintype F] (x : S)
    (h_bad : ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) :
    MCAListBadWitness G c us γ L x := by
  sorry

/-! ### A3: Extension to maximal agreement (per list element) -/

/-- A3: Each list element's agreement set extends to a maximal agreement domain. -/
theorem MCAListBadWitness.exists_maxAgreement_extending
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    {us : Fin ℓ → (Fin n → F)} {γ : ℚ} {L : ℕ} {x : S}
    (w : MCAListBadWitness G c us γ L x) (k : Fin L) :
    ∃ T : Finset (Fin n), w.T ⊆ T ∧
      IsMaxAgreementDomain c (G.combine x us) T := by
  classical
  have h₀ : IsAgreementDomain c (G.combine x us) w.T :=
    ⟨w.cws k, w.cws_mem k, w.agree k⟩
  let goodSets : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => w.T ⊆ T ∧ IsAgreementDomain c (G.combine x us) T)
  have h_nonempty : goodSets.Nonempty := by
    refine ⟨w.T, ?_⟩
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨subset_refl _, h₀⟩
  obtain ⟨T, hT_mem, hT_max⟩ :=
    goodSets.exists_max_image (fun T => T.card) h_nonempty
  have hT_props : w.T ⊆ T ∧ IsAgreementDomain c (G.combine x us) T := by
    have := hT_mem
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  refine ⟨T, hT_props.1, hT_props.2, ?_⟩
  intro T' hT'_ssub hT'_AD
  have hT'_good : T' ∈ goodSets := by
    simp only [goodSets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hT_props.1.trans hT'_ssub.subset, hT'_AD⟩
  have h_card_lt : T.card < T'.card := Finset.card_lt_card hT'_ssub
  have h_card_le : T'.card ≤ T.card := hT_max T' hT'_good
  omega

/-! ### F4: Distinct-seed extraction (list version) -/

/-- F4: Extract ℓ distinct bad seeds, each carrying a list witness. -/
theorem extract_list_bad_witnesses_at_distinct_seeds
    [DecidableEq S] [Fintype F]
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) (γ : ℚ) (L : ℕ)
    (B_set : Finset S) (hB_card : ℓ ≤ B_set.card)
    (h_bad : ∀ x ∈ B_set, ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) :
    ∃ xs : Fin ℓ → S,
      Function.Injective xs ∧
      (∀ k, xs k ∈ B_set) ∧
      ∃ ws : ∀ k, MCAListBadWitness G c us γ L (xs k), True := by
  classical
  obtain ⟨xs, h_inj, h_in⟩ := exists_distinct_seeds_in_finset B_set hB_card
  refine ⟨xs, h_inj, h_in, ?_, trivial⟩
  exact fun k => mkMCAListBadWitness G c us γ L (xs k) (h_bad (xs k) (h_in k))

end LinearCodes
