import SumcheckProtocol.Properties.Probability.Universe

-- probOverChallenges is just probEvent
-- kept as alias for backwards compatibility during migration
noncomputable abbrev probOverChallenges
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  (E : (Fin n → 𝔽) → Prop) : ℚ :=
  probEvent E

-- monotonicity: if E implies F then Pr[E] ≤ Pr[F]
lemma prob_over_challenges_mono
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  {E F : (Fin n → 𝔽) → Prop}
  (h : ∀ r, E r → F r) :
  probEvent (C := 𝔽) (n := n) E ≤ probEvent (C := 𝔽) (n := n) F := by
  classical
  let Ω : Finset (Fin n → 𝔽) := allChallenges 𝔽 n
  have hsub : Ω.filter E ⊆ Ω.filter F := by
    intro r hr
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hr).1, h r (Finset.mem_filter.1 hr).2⟩
  have hcard : ((Ω.filter E).card : ℚ) ≤ ((Ω.filter F).card : ℚ) := by
    exact_mod_cast (Finset.card_le_card hsub)
  have hΩnonneg : (0 : ℚ) ≤ (Ω.card : ℚ) := by
    exact_mod_cast (Nat.zero_le Ω.card)
  have hdiv := div_le_div_of_nonneg_right hcard hΩnonneg
  simpa [probEvent, Ω] using hdiv

-- union bound: Pr[∃ i, E i] ≤ ∑ i, Pr[E i]
lemma prob_over_challenges_exists_le_sum
  {𝔽 : Type _} {n : ℕ} [Fintype 𝔽]
  (E : Fin n → (Fin n → 𝔽) → Prop) :
  probEvent (C := 𝔽) (n := n) (fun r => ∃ i : Fin n, E i r)
    ≤
  ∑ i : Fin n, probEvent (C := 𝔽) (n := n) (fun r => E i r) := by
  classical
  letI : DecidablePred (fun r : (Fin n → 𝔽) => ∃ i : Fin n, E i r) :=
    Classical.decPred _
  letI (i : Fin n) : DecidablePred (fun r : (Fin n → 𝔽) => E i r) :=
    Classical.decPred _
  let Ω : Finset (Fin n → 𝔽) := allChallenges 𝔽 n
  have hsubset :
      Ω.filter (fun r => ∃ i : Fin n, E i r)
        ⊆
      (Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r)) := by
    intro r hr
    rcases (Finset.mem_filter.1 hr).2 with ⟨i, hi⟩
    exact Finset.mem_biUnion.2 ⟨i, by simp, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hr).1, hi⟩⟩
  have h1_nat := Finset.card_le_card hsubset
  have h2_nat : ((Finset.univ : Finset (Fin n)).biUnion (fun i => Ω.filter (fun r => E i r))).card
      ≤ ∑ i : Fin n, (Ω.filter (fun r => E i r)).card := by
    simpa using Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
      (t := fun i => Ω.filter (fun r => E i r))
  have hcard : ((Ω.filter (fun r => ∃ i : Fin n, E i r)).card : ℚ)
      ≤ ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) := by
    exact_mod_cast le_trans h1_nat h2_nat
  have hΩnonneg : (0 : ℚ) ≤ (Ω.card : ℚ) := by
    exact_mod_cast (Nat.zero_le Ω.card)
  have hdiv := div_le_div_of_nonneg_right hcard hΩnonneg
  have hsum : (∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ)) / (Ω.card : ℚ)
      = ∑ i : Fin n, ((Ω.filter (fun r => E i r)).card : ℚ) / (Ω.card : ℚ) := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  simpa [probEvent, Ω] using le_trans hdiv (le_of_eq hsum)
