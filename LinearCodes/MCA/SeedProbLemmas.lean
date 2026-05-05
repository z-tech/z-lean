/-
# `seedProb` algebra

Building blocks for reasoning about seed-probabilities. The key
ingredient is monotonicity: if `P ⇒ Q` pointwise, then
`seedProb P ≤ seedProb Q`. Most BCGM25 §3 monotonicity lemmas (e.g.
Lemma 3.16) decompose to this.
-/

import LinearCodes.MCA.Definitions

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {S : Type*} [Fintype S]

/-- Pointwise implication of predicates implies inequality of
seed-probabilities. -/
theorem seedProb_mono {P Q : S → Prop} (h : ∀ x, P x → Q x) :
    seedProb P ≤ seedProb Q := by
  unfold seedProb
  letI : DecidablePred P := Classical.decPred P
  letI : DecidablePred Q := Classical.decPred Q
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast Nat.zero_le _)
  exact_mod_cast Finset.card_le_card
    (Finset.monotone_filter_right Finset.univ (fun x _ hx => h x hx))

/-- Equivalent predicates have equal seed-probabilities. -/
theorem seedProb_congr {P Q : S → Prop} (h : ∀ x, P x ↔ Q x) :
    seedProb P = seedProb Q :=
  le_antisymm
    (seedProb_mono fun x hx => (h x).mp hx)
    (seedProb_mono fun x hx => (h x).mpr hx)

/-- Seed-probability of the predicate `P ∨ Q` is at most the sum. -/
theorem seedProb_or_le [DecidableEq S] {P Q : S → Prop} :
    seedProb (fun x => P x ∨ Q x) ≤ seedProb P + seedProb Q := by
  unfold seedProb
  letI : DecidablePred P := Classical.decPred P
  letI : DecidablePred Q := Classical.decPred Q
  letI : DecidablePred (fun x => P x ∨ Q x) := Classical.decPred _
  have h_union : (Finset.univ.filter (fun x : S => P x ∨ Q x)).card
               ≤ (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
    rw [show (Finset.univ.filter fun x : S => P x ∨ Q x) =
          (Finset.univ.filter P) ∪ (Finset.univ.filter Q) from ?_]
    · exact Finset.card_union_le _ _
    · ext x; simp [Finset.mem_filter, Finset.mem_union]
  by_cases hN : Fintype.card S = 0
  · simp [hN]
  · have hN_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [← add_div, div_le_div_iff_of_pos_right hN_pos]
    exact_mod_cast h_union

/-- Seed-probability is monotone under predicate strengthening from the
right (taking the contrapositive form for use with bad-event arguments). -/
theorem seedProb_le_of_subset_filter {P Q : S → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : (Finset.univ : Finset S).filter P ⊆ Finset.univ.filter Q) :
    seedProb P ≤ seedProb Q :=
  seedProb_mono (fun x hPx => by
    have : x ∈ (Finset.univ : Finset S).filter Q :=
      h (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hPx⟩)
    exact (Finset.mem_filter.mp this).2)

/-! ### MCA bad-event monotonicity in γ -/

/-- The MCA bad-event probability is monotone in `γ`: relaxing the agreement-set
size requirement (smaller `γ` to larger `γ'`) cannot decrease the probability. -/
theorem MCA_bad_event_mono_in_γ {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (us : Fin ℓ → (Fin n → F)) {γ γ' : ℚ} (h : γ ≤ γ') :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ') ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) := by
  apply seedProb_mono
  intro x ⟨T, hT_size, hT_in, j, hj⟩
  refine ⟨T, ?_, hT_in, j, hj⟩
  have h1 : (1 : ℚ) - γ' ≤ 1 - γ := by linarith
  have hn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le _
  have h2 : (n : ℚ) * (1 - γ') ≤ (n : ℚ) * (1 - γ) :=
    mul_le_mul_of_nonneg_left h1 hn
  linarith

end LinearCodes
