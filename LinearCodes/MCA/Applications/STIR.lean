/-
# BCGM25 §9 application: STIR (univariate-powers generator)

Specialization of the abstract MCA bounds to STIR's `univariatePowers F d`
generator.
-/

import LinearCodes.MCA.MaximalDomain
import LinearCodes.MCA.ConcreteMDS
import LinearCodes.MCA.ListDecoding

set_option linter.unusedSectionVars false

namespace LinearCodes

/-! ### A1: STIR MCA unique-decoding bound -/

/-- A1: Specializes `MCA_unique_decoding_bound` to `univariatePowers F d`. -/
theorem STIR_MCA_unique_decoding_bound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d n : ℕ} (hd : d + 1 ≤ Fintype.card F) (hd_pos : 0 < d + 1)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin (d + 1) → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (d + 2) < δ_C / n) :
    seedProb (S := F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T ((Generator.univariatePowers F d).combine x us) ∧
        ∃ j : Fin (d + 1), ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * d / Fintype.card F := by
  have hG_MDS : (Generator.univariatePowers F d).IsMDS := Generator.univariatePowers_IsMDS hd
  have hγ_hi' : γ * ((d + 1 : ℕ) + 1) < δ_C / n := by exact_mod_cast hγ_hi
  have h_main := MCA_unique_decoding_bound (Generator.univariatePowers F d) hG_MDS hd_pos
    c hn h_minDist us hγ_pos hγ_hi'
  have h_ell_cast : (((d + 1 : ℕ) : ℚ) - 1) = (d : ℚ) := by push_cast; ring
  rw [h_ell_cast] at h_main
  exact h_main

/-! ### A2: STIR MCA predicate -/

/-- A2: Wraps A1 into the `MutualCorrelatedAgreement` predicate. -/
theorem STIR_MutualCorrelatedAgreement
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {d n : ℕ}
    (hd : d + 1 ≤ Fintype.card F) (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C) :
    MutualCorrelatedAgreement (Generator.univariatePowers F d) c
      (fun γ => if γ * (d + 2) < δ_C / n
                then (max ((n : ℚ) * γ) 1 + 1) * d / Fintype.card F
                else 1) := by
  intro us γ hγ_pos hγ_le_one
  by_cases h_case : γ * (d + 2) < δ_C / n
  · simp only [h_case, ↓reduceIte]
    have hd_pos : 0 < d + 1 := Nat.succ_pos d
    exact STIR_MCA_unique_decoding_bound hd hd_pos c hn h_minDist us hγ_pos h_case
  · simp only [h_case, ↓reduceIte]
    exact seedProb_le_one _

/-! ### A3: STIR zero-evading bound -/

/-- A3: Direct zero-evading bound for `univariatePowers F d`. -/
theorem STIR_zeroEvading
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : d + 1 ≤ Fintype.card F) :
    ZeroEvading (Generator.univariatePowers F d) ((d : ℚ) / Fintype.card F) := by
  have hG := Generator.univariatePowers_IsMDS hd
  have hZE := hG.zeroEvading_bound
  -- hZE : ZeroEvading (univariatePowers F d) ((↑(d + 1) - 1 : ℚ) / Fintype.card F)
  have h_simp : (((d + 1 : ℕ) : ℚ) - 1) = (d : ℚ) := by push_cast; ring
  rw [h_simp] at hZE
  exact hZE

/-! ### A6: STIR unique-decoding via half-distance -/

/-- A6: Half-distance unique decoding for STIR-MDS. -/
theorem STIR_uniqueDecoding_via_MCA
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n d : ℕ}
    (c : Submodule F (Fin n → F)) {k : ℕ} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_τ : 2 * τ < n - k + 1) :
    IsListDecodable c τ 1 := by
  exact IsListDecodable_of_minDist_unique h_MDS.2 h_τ

end LinearCodes
