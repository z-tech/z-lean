/-
# Capstone API examples

Concrete `example`s exercising the BCGM25 capstone theorems with specific
fields and parameters. These serve as smoke tests catching API regressions.
-/

import LinearCodes.MCA.Case2Capstone
import LinearCodes.MCA.ListDecodingMCA
import LinearCodes.MCA.JohnsonBound
import LinearCodes.MCA.Applications.STIR
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

namespace LinearCodes

section Capstones

-- Provide Fact-of-primality instances at the section level so the type
-- annotations on the examples below (which use ZMod p as a Field) elaborate
-- before the tactic blocks open.
attribute [local instance] Fact.mk

instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by decide⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by decide⟩
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by decide⟩

/-! ### STIR over ZMod 7, degree 3 -/

example : (Generator.univariatePowers (ZMod 7) 3).IsMDS :=
  Generator.univariatePowers_IsMDS (by decide : 3 + 1 ≤ Fintype.card (ZMod 7))

/-! ### STIR-style MCA bound at concrete parameters -/

example {n : ℕ} (hn : 0 < n)
    (c : Submodule (ZMod 7) (Fin n → ZMod 7))
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin 4 → (Fin n → ZMod 7))  -- 4 = d + 1 = 3 + 1
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (3 + 2) < δ_C / n) :
    seedProb (S := ZMod 7) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T ((Generator.univariatePowers (ZMod 7) 3).combine x us) ∧
        ∃ j : Fin 4, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * 3 / Fintype.card (ZMod 7) := by
  have hd : 3 + 1 ≤ Fintype.card (ZMod 7) := by decide
  exact STIR_MCA_unique_decoding_bound hd (by omega) c hn h_minDist us hγ_pos hγ_hi

/-! ### List-decodable via min-distance unique-decoding -/

example {n : ℕ} {c : Submodule (ZMod 11) (Fin n → ZMod 11)}
    {d : ℕ} (h_minDist : MinDistAtLeast c d)
    {τ : ℕ} (h_τ : 2 * τ < d) :
    IsListDecodable c τ 1 :=
  IsListDecodable_of_minDist_unique h_minDist h_τ

/-! ### affineLine MDS over ZMod 5 -/

example : (Generator.affineLine (ZMod 5)).IsMDS :=
  Generator.affineLine_IsMDS (by decide : 2 ≤ Fintype.card (ZMod 5))

end Capstones

end LinearCodes
