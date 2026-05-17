import LinearCodes.ReedSolomon
import LinearCodes.MCA.RS.MCABound

/-!
# Reed-Solomon: soundness of the `LinearCode` typeclass output

The `LinearCode` typeclass exposes `mcaProximityGapError` as a free
`ℚ`-valued field plus a typeclass-level `_in_unit_interval` range
obligation. This file pins the **soundness** of the
`ReedSolomonCode`-instance value: it is a valid upper bound on the
actual MCA seed-probability for the canonical
`Generator.univariatePowers F l` setup.

This is the link a security profiler needs when chaining
`mcaProximityGapError` through a per-protocol soundness formula:
calling `LinearCode.mcaProximityGapError rs .proven (l+1) δ q` and
multiplying by per-round factors is *justified* by this theorem (plus
the proximity-gap conjecture for `.conjectured`, which is intentionally
not yet machine-checked).

## Why this lives outside the typeclass

A generic typeclass-level soundness obligation would require
`LinearCode.lean` to import the MCA framework (`Submodule`,
`Generator`, `seedProb`, …), tightly coupling the typeclass to the
BCGM25 development. Instead the typeclass carries only the range
obligation; per-instance soundness lives next to the instance, where
it can reference the instance-specific proven theorem (here
`rs_MCA_list_decoding_bound`).
-/

namespace LinearCodes

/-- The canonical RS-MCA bad event used by the soundness theorem
below. Lifted to a `def` so the soundness statement can refer to it
without ambiguous placeholders. -/
def reedSolomonMCABadEvent
    {F : Type*} [Field F] [DecidableEq F]
    (rs : ReedSolomonCode F)
    {l : ℕ} (us : Fin (l + 1) → (Fin rs.config.codeLength → F))
    (δ : ℕ) : F → Prop :=
  fun α =>
    ∃ T : Finset (Fin rs.config.codeLength),
      (T.card : ℚ) ≥ rs.config.codeLength *
        (1 - (δ : ℚ) / rs.config.codeLength) ∧
      InRestrictedCode (reedSolomonSubmodule rs.config) T
        ((Generator.univariatePowers F l).combine α us) ∧
      ∃ j : Fin (l + 1),
        ¬ InRestrictedCode (reedSolomonSubmodule rs.config) T (us j)

/-- **RS instance soundness.** For an `ReedSolomonCode F` and the
canonical BCGM25 setup (univariate-powers generator
`Generator.univariatePowers F l`, agreement-slack `γ := δ / n`,
Johnson list-decoding radius `τ`), the seed-probability of the MCA
bad event is bounded by
`LinearCode.mcaProximityGapError rs .proven (l+1) δ (Fintype.card F)`.

The typeclass batch parameter corresponds to BCGM25's `ℓ` (total
number of rows in the generator) — i.e. `ℓ = l + 1` where `l` is the
degree parameter of `Generator.univariatePowers F l`. The typeclass
`δ` matches the BCGM25 `n·γ` (agreement-slack as a Hamming distance). -/
theorem ReedSolomonCode.mcaProximityGapError_proven_sound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (rs : ReedSolomonCode F)
    (h_dom : rs.config.domain.size = rs.config.codeLength)
    (h_distinct : ∀ i j : Fin rs.config.domain.size, i ≠ j →
        rs.config.domain.getD i.val 0 ≠ rs.config.domain.getD j.val 0)
    (hn : 0 < rs.config.codeLength)
    {l : ℕ} (h_field : l + 1 ≤ Fintype.card F)
    (us : Fin (l + 1) → (Fin rs.config.codeLength → F))
    {τ : ℕ} (h_johnson_τ :
        (rs.config.codeLength - τ) * (rs.config.codeLength - τ) >
        rs.config.codeLength * rs.config.messageLength)
    {δ : ℕ}
    (hγ_hi : ((δ : ℚ) / rs.config.codeLength) * (l + 2) <
             ((rs.config.codeLength - rs.config.messageLength + 1 : ℕ) : ℚ) /
               rs.config.codeLength)
    (h_radius :
        (rs.config.codeLength : ℚ) * ((δ : ℚ) / rs.config.codeLength) ≤ (τ : ℚ)) :
    seedProb (S := F) (reedSolomonMCABadEvent rs us δ) ≤
      LinearCode.mcaProximityGapError (F := F) rs ProximityRegime.proven
        (l + 1) δ (Fintype.card F) := by
  classical
  set γ : ℚ := (δ : ℚ) / rs.config.codeLength
  have hγ_pos : 0 ≤ γ := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact_mod_cast Nat.zero_le _
  have h_bound :=
    rs_MCA_list_decoding_bound rs.config h_dom h_distinct hn
      (Nat.succ_pos l) h_field us h_johnson_τ hγ_pos hγ_hi h_radius
  have hn_q_ne : (rs.config.codeLength : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (rs.config.codeLength : ℚ) := by exact_mod_cast hn
    exact ne_of_gt this
  have h_nγ_eq_δ : (rs.config.codeLength : ℚ) * γ = (δ : ℚ) := by
    show (rs.config.codeLength : ℚ) * ((δ : ℚ) / rs.config.codeLength) = (δ : ℚ)
    rw [mul_comm, div_mul_cancel₀ _ hn_q_ne]
  have hq_pos : 0 < Fintype.card F := lt_of_lt_of_le (Nat.succ_pos l) h_field
  have hq_ne_zero : Fintype.card F ≠ 0 := Nat.pos_iff_ne_zero.mp hq_pos
  -- seedProb of the named bad event is bounded by raw form (after n·γ = δ).
  have h_seed_le_raw :
      seedProb (S := F) (reedSolomonMCABadEvent rs us δ) ≤
        (rs.config.codeLength : ℚ) ^ 2 * (max (δ : ℚ) 1 + 1) *
          ((l + 1 : ℕ) - 1 : ℚ) / Fintype.card F := by
    have := h_bound
    rw [h_nγ_eq_δ] at this
    exact this
  have h_seed_le_one :
      seedProb (S := F) (reedSolomonMCABadEvent rs us δ) ≤ 1 :=
    seedProb_le_one _
  have h_lq_eq : (if l + 1 = 0 then (0 : ℚ) else ((l + 1 - 1 : ℕ) : ℚ))
      = ((l + 1 : ℕ) - 1 : ℚ) := by
    rw [if_neg (Nat.succ_ne_zero l)]
    push_cast; ring
  have h_typeclass_eq :
      LinearCode.mcaProximityGapError (F := F) rs ProximityRegime.proven
        (l + 1) δ (Fintype.card F) =
        min ((rs.config.codeLength : ℚ) ^ 2 * (max (δ : ℚ) 1 + 1) *
              ((l + 1 : ℕ) - 1 : ℚ) / Fintype.card F) 1 := by
    show rsMCAProximityGapError rs ProximityRegime.proven (l + 1) δ (Fintype.card F) = _
    unfold rsMCAProximityGapError
    rw [if_neg hq_ne_zero]
    simp only
    congr 1
    rw [h_lq_eq]
  rw [h_typeclass_eq]
  exact le_min h_seed_le_raw h_seed_le_one

end LinearCodes
