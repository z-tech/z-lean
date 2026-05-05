/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Corrádi intersection lemma

Corrádi's lemma (Corrádi 1969) bounds the number of subsets of a fixed
ground set when those subsets all share a common density and have
bounded pairwise intersection density.

Concretely: if `A₁, …, Aₘ ⊆ A` each have size `a` and pairwise
intersections of size at most `b`, then
`m · (a² − b · |A|) ≤ |A| · (a − b)`,
which yields `m ≤ (a − b) / (a² − b·|A|)` as a corollary when
`a² > b · |A|`.

The lemma is the key counting tool used in the BCGM25 mutual-correlated-
agreement framework (Bordage–Chiesa–Guan–Manzur 2026, Lemma 3.23). It
appears in Jukna's *Extremal Combinatorics* (Lemma 5.5) and is a
standard double-counting + Cauchy–Schwarz argument.

This file is staged for upstreaming to
`Mathlib/Combinatorics/SetFamily/Corradi.lean` — the file structure
mirrors Mathlib's tree so it can be lifted verbatim later.

## Main statements

* `Finset.corradi_unconditional` — the multiplicative inequality
  `m² · a² + m · N · b ≤ m · N · a + m² · N · b`, valid for all `m ≥ 0`.
* `Finset.corradi_div` — the standard ratio bound under `a² > b · N`.

## Proof sketch

Let `f : α → ℕ` count how many `Aᵢ` contain a given point. Then
`Σ f = m · a` and `Σ f² = Σ_{i,j} |Aᵢ ∩ Aⱼ| ≤ m · a + m(m−1) · b`.
Cauchy–Schwarz on the constant 1 vs `f` over `A` gives
`(m · a)² ≤ |A| · Σ f²`, and rearranging produces the conclusion.
-/

import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace Finset

variable {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The number of indices `i` such that `x ∈ As i`. -/
def coverCount (As : ι → Finset α) (x : α) : ℕ :=
  (Finset.univ.filter fun i => x ∈ As i).card

/-! ### Step 1: sum of `coverCount` over `A` equals `m · a` -/

/-- **Sum-of-degrees identity (double-counting).** Summing the cover-count
over the ground set `A` equals the total size of the family. -/
theorem sum_coverCount_eq_sum_card
    {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, coverCount As x = ∑ i, (As i).card := by
  have h₁ : ∀ x, coverCount As x = ∑ i, (if x ∈ As i then 1 else 0 : ℕ) := by
    intro x
    rw [coverCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h₂ : ∀ i, (As i).card = ∑ x ∈ A, (if x ∈ As i then 1 else 0 : ℕ) := by
    intro i
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h_sub i h, h⟩, fun h => h.2⟩
  simp_rw [h₁, h₂]
  exact Finset.sum_comm

/-- Specialised form: when every subset has size `a`. -/
theorem sum_coverCount_eq_card_mul
    {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A)
    {a : ℕ} (h_size : ∀ i, (As i).card = a) :
    ∑ x ∈ A, coverCount As x = Fintype.card ι * a := by
  rw [sum_coverCount_eq_sum_card As h_sub]
  rw [Finset.sum_congr rfl (fun i _ => h_size i)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ### Step 2: sum of `coverCount²` equals total pairwise intersection -/

/-- **Sum-of-squares-of-degrees identity.** The sum of squared cover-counts
over `A` equals the total cardinality of the pairwise intersection family
(including the diagonal `i = j`). -/
theorem sum_coverCount_sq_eq_sum_inter_card
    {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A) :
    ∑ x ∈ A, (coverCount As x)^2 = ∑ p : ι × ι, ((As p.1) ∩ (As p.2)).card := by
  have h_pow : ∀ x, (coverCount As x)^2
      = ∑ p : ι × ι, (if x ∈ As p.1 ∧ x ∈ As p.2 then 1 else 0 : ℕ) := by
    intro x
    simp only [coverCount]
    rw [sq, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_mul_sum,
        ← Finset.sum_product', Finset.univ_product_univ]
    apply Finset.sum_congr rfl
    intros p _
    by_cases h₁ : x ∈ As p.1 <;> by_cases h₂ : x ∈ As p.2 <;> simp [h₁, h₂]
  have h_inter : ∀ (i j : ι), ((As i) ∩ (As j)).card
      = ∑ x ∈ A, (if x ∈ As i ∧ x ∈ As j then 1 else 0 : ℕ) := by
    intros i j
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    congr 1
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h_sub i h₁, h₁, h₂⟩, fun ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩⟩
  simp_rw [h_pow, h_inter]
  exact Finset.sum_comm

/-! ### Step 3: bound the pairwise-intersection sum -/

theorem sum_inter_card_le
    (As : ι → Finset α)
    {a b : ℕ}
    (h_size : ∀ i, (As i).card = a)
    (h_pairwise : ∀ i j, i ≠ j → ((As i) ∩ (As j)).card ≤ b) :
    ∑ p : ι × ι, ((As p.1) ∩ (As p.2)).card ≤
      Fintype.card ι * a + Fintype.card ι * (Fintype.card ι - 1) * b := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have h_inner : ∀ i : ι, ∑ j, ((As i) ∩ (As j)).card ≤ a + (Fintype.card ι - 1) * b := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have h_diag : ((As i) ∩ (As i)).card = a := by
      rw [Finset.inter_self]; exact h_size i
    rw [h_diag]
    have h_off : ∑ j ∈ Finset.univ.erase i, ((As i) ∩ (As j)).card
        ≤ (Fintype.card ι - 1) * b := by
      calc ∑ j ∈ Finset.univ.erase i, ((As i) ∩ (As j)).card
          ≤ ∑ j ∈ Finset.univ.erase i, b := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_erase] at hj
            exact h_pairwise i j (Ne.symm hj.1)
        _ = (Finset.univ.erase i).card * b := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = (Fintype.card ι - 1) * b := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    exact Nat.add_le_add_left h_off a
  calc ∑ i, ∑ j, ((As i) ∩ (As j)).card
      ≤ ∑ _i : ι, (a + (Fintype.card ι - 1) * b) :=
        Finset.sum_le_sum (fun i _ => h_inner i)
    _ = Fintype.card ι * (a + (Fintype.card ι - 1) * b) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = Fintype.card ι * a + Fintype.card ι * (Fintype.card ι - 1) * b := by
        rw [Nat.mul_add, ← Nat.mul_assoc]

/-! ### Step 4: Cauchy–Schwarz reduction -/

/-- Cauchy–Schwarz applied to the constant function 1 against `coverCount`. -/
theorem coverCount_cauchy_schwarz
    {A : Finset α} (As : ι → Finset α) :
    (∑ x ∈ A, coverCount As x)^2 ≤ A.card * ∑ x ∈ A, (coverCount As x)^2 := by
  -- (Σ 1 · f)² ≤ (Σ 1²) · (Σ f²) = |A| · Σ f². Specialise the standard
  -- Cauchy-Schwarz lemma from Mathlib.Algebra.Order.Chebyshev.
  exact sq_sum_le_card_mul_sum_sq

/-! ### Main theorem -/

/-- **Corrádi's lemma (unconditional, integer form).**

Suppose `A₁, …, Aₘ ⊆ A` each have size exactly `a`, and pairwise
intersections of size at most `b`. Then
`m² · a² + m · |A| · b ≤ m · |A| · a + m² · |A| · b`,
or equivalently (for `m ≥ 1`)
`m · a² + |A| · b ≤ |A| · a + m · |A| · b`,
i.e. `m · (a² − b·|A|) ≤ |A| · (a − b)`. -/
theorem corradi_unconditional
    {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A)
    {a b : ℕ}
    (h_size : ∀ i, (As i).card = a)
    (h_pairwise : ∀ i j, i ≠ j → ((As i) ∩ (As j)).card ≤ b) :
    let m := Fintype.card ι
    let N := A.card
    m^2 * a^2 + m * N * b ≤ m * N * a + m^2 * N * b := by
  intro m N
  have h_cs : (∑ x ∈ A, coverCount As x)^2 ≤ A.card * ∑ x ∈ A, (coverCount As x)^2 :=
    coverCount_cauchy_schwarz As
  have h_sum : ∑ x ∈ A, coverCount As x = m * a :=
    sum_coverCount_eq_card_mul As h_sub h_size
  have h_sq : ∑ x ∈ A, (coverCount As x)^2 = ∑ p : ι × ι, ((As p.1) ∩ (As p.2)).card :=
    sum_coverCount_sq_eq_sum_inter_card As h_sub
  have h_bd : ∑ p : ι × ι, ((As p.1) ∩ (As p.2)).card ≤ m * a + m * (m - 1) * b :=
    sum_inter_card_le As h_size h_pairwise
  have h_main : (m * a)^2 ≤ N * (m * a + m * (m - 1) * b) := by
    calc (m * a)^2
        = (∑ x ∈ A, coverCount As x)^2 := by rw [h_sum]
      _ ≤ A.card * ∑ x ∈ A, (coverCount As x)^2 := h_cs
      _ = N * ∑ p : ι × ι, ((As p.1) ∩ (As p.2)).card := by rw [h_sq]
      _ ≤ N * (m * a + m * (m - 1) * b) := Nat.mul_le_mul_left N h_bd
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · rw [hm0]; simp
  · have hkey : m * (m - 1) + m = m^2 := by
      have h : m - 1 + 1 = m := Nat.sub_add_cancel hm1
      calc m * (m - 1) + m
          = m * ((m - 1) + 1) := by ring
        _ = m * m := by rw [h]
        _ = m^2 := by ring
    have h2 : m^2 * a^2 ≤ N * m * a + N * m * (m - 1) * b := by
      nlinarith [h_main]
    have hb : N * m * (m - 1) * b + m * N * b = m^2 * N * b := by
      have heq : N * m * (m - 1) * b + m * N * b = N * b * (m * (m - 1) + m) := by ring
      rw [heq, hkey]; ring
    linarith [h2, hb]

/-- **Corrádi's lemma, ratio form.** Under the strict hypothesis
`a² > b · |A|`, the family size is bounded by
`m ≤ (a − b) / (a² − b·|A|)` — stated as an integer inequality after
clearing denominators. -/
theorem corradi_ratio
    {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A)
    {a b : ℕ}
    (h_size : ∀ i, (As i).card = a)
    (h_pairwise : ∀ i j, i ≠ j → ((As i) ∩ (As j)).card ≤ b)
    (h_strict : a^2 > b * A.card)
    (h_ba : b ≤ a) :
    Fintype.card ι * (a^2 - b * A.card) ≤ A.card * (a - b) := by
  have key : (Fintype.card ι)^2 * a^2 + Fintype.card ι * A.card * b ≤
      Fintype.card ι * A.card * a + (Fintype.card ι)^2 * A.card * b :=
    corradi_unconditional As h_sub h_size h_pairwise
  set m := Fintype.card ι with hm_def
  set N := A.card with hN_def
  have h1 : b * N ≤ a^2 := le_of_lt h_strict
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [hm0]
  · have ha2 : a^2 - b * N + b * N = a^2 := Nat.sub_add_cancel h1
    have hab : a - b + b = a := Nat.sub_add_cancel h_ba
    have e1 : m^2 * (a^2 - b * N) + m^2 * (b * N) = m^2 * a^2 := by
      rw [← Nat.mul_add, ha2]
    have e2 : m * N * (a - b) + m * N * b = m * N * a := by
      rw [← Nat.mul_add, hab]
    have step1 : m^2 * (a^2 - b * N) ≤ m * N * (a - b) := by
      nlinarith [key, e1, e2]
    have step2 : m * (m * (a^2 - b * N)) ≤ m * (N * (a - b)) := by
      calc m * (m * (a^2 - b * N))
          = m^2 * (a^2 - b * N) := by ring
        _ ≤ m * N * (a - b) := step1
        _ = m * (N * (a - b)) := by ring
    exact Nat.le_of_mul_le_mul_left step2 hmpos

end Finset
