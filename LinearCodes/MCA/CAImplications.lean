/- The prover determined this theorem is likely FALSE:
-- -- Counterexample to the false statement `MCA_implies_CA`.
-- --
-- -- Take:
-- -- * `F = ℚ`
-- -- * `S = PUnit` (one seed)
-- -- * `n = 2`
-- -- * `ℓ = 0`
-- -- * `c = ⊥ : Submodule ℚ (Fin 2 → ℚ)`
-- -- * `εMCA := fun _ => 0`
-- -- * `G : Generator ℚ PUnit 0` the unique generator
-- --
-- -- Why MCA holds:
-- -- * For any `us : Fin 0 → (Fin 2 → ℚ)` and any `γ`, the MCA bad event is
-- --   `∃ T : Finset (Fin 2), ... ∧ ∃ j : Fin 0, ¬ InRestrictedCode c T (us j)`.
-- -- * But `Fin 0` has no elements, so `∃ j : Fin 0, ...` is impossible.
-- -- * Hence the bad event is false for every seed `x`, so its seed-probability is `0`.
-- -- * Therefore `MutualCorrelatedAgreement G c εMCA` holds, since `0 ≤ εMCA γ = 0`.
-- --
-- -- Why CA fails:
-- -- * Choose `e = 2` and `t = 1`. Then `1 ≤ t`, `t < e`, and `e ≤ n` all hold.
-- -- * The CA premise
-- --   `∀ i : Fin 0, ∀ codeword ∈ c, e ≤ hammingDistance (us i) codeword`
-- --   is vacuous because there is no `i : Fin 0`.
-- -- * For any seed `x`, `G.combine x us = 0`, because the defining sum is over `Fin 0`.
-- -- * Since `0 ∈ c`, taking `codeword = 0` shows
-- --   `hammingDistance (G.combine x us) codeword = hammingDistance 0 0 = 0 ≤ e - t = 1`.
-- -- * So the CA event is true for every seed, hence its seed-probability is `1`.
-- -- * But the claimed bound is
-- --   `εMCA ((e - 1 : ℚ) / n) = εMCA (1 / 2) = 0`.
-- -- * Thus the conclusion
-- --   `CorrelatedAgreement G c (fun e _ => εMCA ((e - 1 : ℚ) / n))` fails.
-- --
-- -- Conclusion: the theorem needs an extra assumption such as `0 < ℓ`;
-- -- without it, the statement is false.
-/
/-
# MCA implies CA (BCGM25 Lemma 3.22)

The MCA predicate is strictly stronger than CA: the existence of a
*shared* agreement set `T` for all rows simultaneously (MCA) implies
the weaker statement that the linear combination is close to the code
on average (CA). This file states and proves the reduction.

The BCGM25 quantitative form: if `G` has MCA for `c` with error `εMCA`,
then `G` has CA for `c` with error `εCA(e, t) = εMCA((e − 1) / n)` for
`1 ≤ t < e ≤ n`.
-/

import LinearCodes.MCA.Definitions
import LinearCodes.MCA.SeedProbLemmas

set_option linter.unusedSectionVars false

namespace LinearCodes

theorem CA_seed_event_implies_MCA_bad_event {F : Type*} [Field F] [DecidableEq F] {S : Type*} [Fintype S] {n ℓ : ℕ} (hℓ : 0 < ℓ) (G : Generator F S ℓ) (c : Submodule F (Fin n → F)) (e t : ℕ) (ht1 : 1 ≤ t) (hte : t < e) (hen : e ≤ n) (us : Fin ℓ → (Fin n → F)) (hus : ∀ i : Fin ℓ, ∀ codeword ∈ c, e ≤ hammingDistance (us i) codeword) (x : S) : (∃ codeword ∈ c, hammingDistance (G.combine x us) codeword ≤ e - t) → ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - ((e - 1 : ℚ) / n)) ∧ InRestrictedCode c T (G.combine x us) ∧ ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j) := by
  intro hCA
  rcases hCA with ⟨cw, hcw, hdist⟩
  let T : Finset (Fin n) := agreementSet (G.combine x us) cw
  let j0 : Fin ℓ := ⟨0, hℓ⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · have hdist' : hammingDistance (G.combine x us) cw ≤ e - 1 := by
      omega
    have hcard_nat : n - (e - 1) ≤ T.card := by
      dsimp [T]
      have hEq := hammingDistance_eq_n_sub_agreementSet (G.combine x us) cw
      omega
    have hnne : (n : ℚ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hcard_rat : (n : ℚ) - ((e : ℚ) - 1) ≤ T.card := by
      have htmp : ((n - (e - 1) : ℕ) : ℚ) ≤ T.card := by
        exact_mod_cast hcard_nat
      have hsuble : e - 1 ≤ n := by
        omega
      have he1 : ((e - 1 : ℕ) : ℚ) = (e : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ e)]
        norm_num
      rw [Nat.cast_sub hsuble, he1] at htmp
      simpa using htmp
    have hrw : (n : ℚ) * (1 - ((e - 1 : ℚ) / n)) = n - ((e : ℚ) - 1) := by
      field_simp [hnne]
    rw [hrw]
    exact hcard_rat
  · refine ⟨cw, hcw, ?_⟩
    intro i hi
    have hmem : i ∈ agreementSet (G.combine x us) cw := by
      simpa [T] using hi
    have hagree := mem_agreementSet.mp hmem
    simpa using hagree.symm
  · refine ⟨j0, ?_⟩
    intro hj0
    rcases hj0 with ⟨w, hwc, hwT⟩
    have hle : hammingDistance (us j0) w ≤ n - T.card := by
      apply hammingDistance_le_of_agree_on
      intro i hi
      exact (hwT i hi).symm
    have hcard_nat : n - (e - 1) ≤ T.card := by
      dsimp [T]
      have hdist' : hammingDistance (G.combine x us) cw ≤ e - 1 := by
        omega
      have hEq := hammingDistance_eq_n_sub_agreementSet (G.combine x us) cw
      omega
    have hwlt : hammingDistance (us j0) w ≤ e - 1 := by
      omega
    have hge : e ≤ hammingDistance (us j0) w := hus j0 w hwc
    omega

theorem MCA_implies_CA {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    CorrelatedAgreement G c (fun e _ => εMCA ((e - 1 : ℚ) / n)) := by
  unfold CorrelatedAgreement
  intro e t ht1 hte hen us hus
  let γ : ℚ := ((e - 1 : ℚ) / n)
  have hn0_nat : 0 < n := by
    omega
  have hn0 : (0 : ℚ) < n := by
    exact_mod_cast hn0_nat
  have h1e_nat : 1 ≤ e := by
    omega
  have h1e : (1 : ℚ) ≤ e := by
    exact_mod_cast h1e_nat
  have he_le_n : (e : ℚ) ≤ n := by
    exact_mod_cast hen
  have hnum0 : (0 : ℚ) ≤ e - 1 := by
    linarith
  have hγ0 : 0 ≤ γ := by
    dsimp [γ]
    exact div_nonneg hnum0 (le_of_lt hn0)
  have hnum_le : (e : ℚ) - 1 ≤ n := by
    linarith
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]
    exact div_le_one_of_le₀ hnum_le (le_of_lt hn0)
  refine le_trans ?_ (hMCA us γ hγ0 hγ1)
  apply seedProb_mono
  intro x hx
  exact CA_seed_event_implies_MCA_bad_event hℓ G c e t ht1 hte hen us hus x hx


theorem MutualCorrelatedAgreement_zero_simplify {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA)
    (us : Fin ℓ → (Fin n → F)) :
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c)
      ≤ εMCA 0 := by
  have hmono :
      seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) ≤
        seedProb (S := S) (fun x =>
          ∃ T : Finset (Fin n),
            (T.card : ℚ) ≥ n * (1 - 0) ∧
            InRestrictedCode c T (G.combine x us) ∧
            ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) := by
    apply seedProb_mono
    intro x hx
    rcases hx with ⟨hcomb, j, hj⟩
    refine ⟨Finset.univ, ?_, ?_, j, ?_⟩
    · norm_num
    · exact (inRestrictedCode_univ_iff c).2 hcomb
    · intro hu
      exact hj ((inRestrictedCode_univ_iff c).1 hu)
  calc
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c) ≤
        seedProb (S := S) (fun x =>
          ∃ T : Finset (Fin n),
            (T.card : ℚ) ≥ n * (1 - 0) ∧
            InRestrictedCode c T (G.combine x us) ∧
            ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j)) := hmono
    _ ≤ εMCA 0 := hMCA us 0 (by norm_num) (by norm_num)


end LinearCodes
