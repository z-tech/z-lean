/-
# Concrete generator IsMDS proofs

Wires the `Generator.IsMDS` predicate (from `UniqueDecoding.lean`) to the
concrete generators defined in `Examples.lean`. Kept in a separate file
because `Generator.IsMDS` is downstream of `Examples`.
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.Examples
import LinearCodes.MCA.InducedCode
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option linter.unusedSectionVars false

namespace LinearCodes
namespace Generator

/-! ### MDS structure of concrete generators -/

/-- The `affineLine` generator's dot-map is injective over any field with
at least 2 elements. The dot-map sends `v = (a, b)` to the polynomial-
evaluation function `x ↦ a + b·x`, which is identically zero only when
`a = b = 0` (provided `|F| ≥ 2`). -/
theorem affineLine_dotMap_injective {F : Type*} [Field F] [DecidableEq F]
    [Fintype F] (h_card : 2 ≤ Fintype.card F) :
    Function.Injective (Generator.affineLine F).dotMap := by
  intro u v huv
  have h_eq : ∀ x : F, u 0 + x * u 1 = v 0 + x * v 1 := by
    intro x
    have hx := congr_fun huv x
    simp [Generator.dotMap_apply, affineLine, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hx
    linear_combination hx
  have h0 : u 0 = v 0 := by
    have h := h_eq 0
    simpa using h
  have hNontriv : Nontrivial F := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx_ne⟩ : ∃ x : F, x ≠ 0 := exists_ne 0
  have h1 : u 1 = v 1 := by
    have hx := h_eq x
    have hxmul : x * u 1 = x * v 1 := by linear_combination hx - h0
    exact mul_left_cancel₀ hx_ne hxmul
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The induced code of `affineLine` has minimum distance at least `|F| − 1`. -/
theorem affineLine_inducedCode_minDist {F : Type*} [Field F] [DecidableEq F]
    [Fintype F] (h_card : 2 ≤ Fintype.card F) :
    Generator.fnMinDistAtLeast (Generator.affineLine F).inducedCode
      (Fintype.card F - 1) := by
  intro w hw_mem hw_ne
  obtain ⟨v, hv⟩ := (Generator.mem_inducedCode_iff (affineLine F) w).mp hw_mem
  have hw_eq : ∀ x : F, w x = v 0 + x * v 1 := by
    intro x
    rw [hv x]
    simp [affineLine, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  have hv_ne : v ≠ 0 := by
    intro hv_eq
    apply hw_ne
    funext x
    rw [hw_eq x, hv_eq]
    simp
  by_cases hv1 : v 1 = 0
  · have hv0_ne : v 0 ≠ 0 := by
      intro h0
      apply hv_ne
      funext i
      fin_cases i
      · simpa using h0
      · simpa using hv1
    have hw_const : ∀ x : F, w x = v 0 := by
      intro x
      rw [hw_eq x, hv1, mul_zero, add_zero]
    have h_filter_eq : (Finset.univ.filter fun x : F => w x ≠ 0) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ x, ?_⟩
      rw [hw_const x]
      exact hv0_ne
    unfold Generator.fnHammingWeight
    rw [h_filter_eq, Finset.card_univ]
    omega
  · have h_zero_subset : (Finset.univ.filter fun x : F => w x = 0) ⊆ {-v 0 / v 1} := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [hw_eq x] at hx
      have hx2 : v 0 + x * v 1 = 0 := hx.2
      have hxv1 : x * v 1 = -v 0 := by linear_combination hx2
      have hx_eq : x = -v 0 / v 1 := by
        rw [eq_div_iff hv1]
        linear_combination hxv1
      rw [Finset.mem_singleton]
      exact hx_eq
    have h_zero_card_le : (Finset.univ.filter fun x : F => w x = 0).card ≤ 1 := by
      have h := Finset.card_le_card h_zero_subset
      simpa using h
    have h_partition :
        (Finset.univ.filter fun x : F => w x ≠ 0).card +
        (Finset.univ.filter fun x : F => w x = 0).card = Fintype.card F := by
      simpa only [not_not, Finset.card_univ] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
          (p := fun x : F => w x ≠ 0))
    unfold Generator.fnHammingWeight
    omega

/-- The `univariatePowers` generator's dot-map is injective over fields with
sufficiently many elements (`d + 1 ≤ |F|`). The dot-map sends a coefficient
vector `v ∈ F^(d+1)` to the polynomial-evaluation function
`x ↦ ∑ᵢ vᵢ · x^i`. A polynomial of degree ≤ d that vanishes on more than
d points must be zero. -/
theorem univariatePowers_dotMap_injective {F : Type*} [Field F] [DecidableEq F]
    [Fintype F] {d : ℕ} (h_card : d + 1 ≤ Fintype.card F) :
    Function.Injective (Generator.univariatePowers F d).dotMap := by
  intro u v huv
  have hp_deg :
      Polynomial.natDegree (∑ i : Fin (d + 1), Polynomial.monomial i.val (u i - v i)) ≤ d :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.isLt))
  have hp_eval : ∀ x : F,
      Polynomial.eval x (∑ i : Fin (d + 1), Polynomial.monomial i.val (u i - v i)) = 0 := by
    intro x
    have hx := congr_fun huv x
    simp only [Generator.dotMap_apply, Generator.univariatePowers_apply] at hx
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    calc (∑ i : Fin (d + 1), (u i - v i) * x ^ i.val)
        = (∑ i : Fin (d + 1), x ^ i.val * u i)
            - (∑ i : Fin (d + 1), x ^ i.val * v i) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intros j _; ring
      _ = 0 := by rw [hx, sub_self]
  have hp_zero :
      (∑ i : Fin (d + 1), Polynomial.monomial i.val (u i - v i)) = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      _ Function.injective_id hp_eval
      (lt_of_le_of_lt hp_deg (by omega))
  funext i
  have hcoeff :
      Polynomial.coeff (∑ i : Fin (d + 1), Polynomial.monomial i.val (u i - v i)) i.val
        = u i - v i := by
    simp only [Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i]
    · simp [Polynomial.coeff_monomial]
    · intros j _ hji
      rw [Polynomial.coeff_monomial, if_neg (fun h => hji (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ i) h
  have huv_i : u i - v i = 0 := by
    rw [← hcoeff, hp_zero, Polynomial.coeff_zero]
  exact sub_eq_zero.mp huv_i

/-! ### E3: dotMap injectivity for `affineSpace` -/

/-- E3: The `affineSpace F s` generator's `dotMap` is injective over fields
with at least 2 elements. -/
theorem affineSpace_dotMap_injective
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {s : ℕ}
    (h_card : 2 ≤ Fintype.card F) :
    Function.Injective (Generator.affineSpace F s).dotMap := by
  intro u v huv
  -- The seed type is `Fin s → F`. For each seed `x`, expand `dotMap` via
  -- `Fin.sum_univ_succ` and the definition of `affineSpace`.
  have h_eq : ∀ x : Fin s → F,
      u 0 + ∑ j : Fin s, x j * u j.succ = v 0 + ∑ j : Fin s, x j * v j.succ := by
    intro x
    have hx := congr_fun huv x
    simp only [Generator.dotMap_apply, affineSpace, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, one_mul] at hx
    exact hx
  -- Specialize to `x = 0`: the sums vanish, leaving `u 0 = v 0`.
  have h0 : u 0 = v 0 := by
    have h := h_eq 0
    simp at h
    exact h
  -- For each `k : Fin s`, specialize to `x = Pi.single k 1`: only the `k`-th
  -- term in the sum survives, yielding `u k.succ = v k.succ`.
  have hk : ∀ k : Fin s, u k.succ = v k.succ := by
    intro k
    have h := h_eq (Pi.single k 1)
    have hsum_u : ∑ j : Fin s, (Pi.single k 1 : Fin s → F) j * u j.succ = u k.succ := by
      rw [Finset.sum_eq_single k]
      · simp [Pi.single_eq_same]
      · intros j _ hjk
        rw [Pi.single_eq_of_ne hjk, zero_mul]
      · intro hk_mem; exact absurd (Finset.mem_univ k) hk_mem
    have hsum_v : ∑ j : Fin s, (Pi.single k 1 : Fin s → F) j * v j.succ = v k.succ := by
      rw [Finset.sum_eq_single k]
      · simp [Pi.single_eq_same]
      · intros j _ hjk
        rw [Pi.single_eq_of_ne hjk, zero_mul]
      · intro hk_mem; exact absurd (Finset.mem_univ k) hk_mem
    rw [hsum_u, hsum_v] at h
    -- h : u 0 + u k.succ = v 0 + v k.succ
    linear_combination h - h0
  -- Combine: every coordinate of `u` equals the corresponding coordinate of `v`.
  funext i
  refine Fin.cases ?_ ?_ i
  · exact h0
  · intro k; exact hk k

/-! ### affineLine -/

/-- E1: The `affineLine` generator is MDS over fields with at least 2 elements.
Combines `affineLine_dotMap_injective` with `affineLine_inducedCode_minDist`. -/
theorem affineLine_IsMDS {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (h_card : 2 ≤ Fintype.card F) :
    (Generator.affineLine F).IsMDS := by
  refine ⟨affineLine_dotMap_injective h_card, ?_⟩
  have h := affineLine_inducedCode_minDist h_card
  -- `Fintype.card F - 2 + 1 = Fintype.card F - 1` since `2 ≤ Fintype.card F`.
  have heq : Fintype.card F - 2 + 1 = Fintype.card F - 1 := by omega
  simpa [heq] using h

/-! ### univariatePowers -/

/-- The induced code of `univariatePowers F d` has minimum distance at least
`|F| − d`. A nonzero codeword is the evaluation of a nonzero polynomial of
degree ≤ d, which has at most `d` roots in `F`, so at least `|F| − d`
nonzero values. -/
theorem univariatePowers_inducedCode_minDist {F : Type*} [Field F] [DecidableEq F]
    [Fintype F] {d : ℕ} (h_card : d + 1 ≤ Fintype.card F) :
    Generator.fnMinDistAtLeast (Generator.univariatePowers F d).inducedCode
      (Fintype.card F - d) := by
  intro w hw_mem hw_ne
  obtain ⟨v, hv⟩ :=
    (Generator.mem_inducedCode_iff (Generator.univariatePowers F d) w).mp hw_mem
  -- Define the polynomial p(X) = ∑ i, monomial i.val (v i)
  set p : Polynomial F := ∑ i : Fin (d + 1), Polynomial.monomial i.val (v i) with hp_def
  have hp_deg : Polynomial.natDegree p ≤ d :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.isLt))
  -- Pointwise: w x = p.eval x
  have hw_eq : ∀ x : F, w x = Polynomial.eval x p := by
    intro x
    rw [hv x, hp_def]
    simp only [Generator.univariatePowers_apply, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    apply Finset.sum_congr rfl
    intros i _; ring
  -- p ≠ 0: if p = 0 then w x = 0 for all x, contradicting hw_ne.
  have hp_ne : p ≠ 0 := by
    intro hp_zero
    apply hw_ne
    funext x
    rw [hw_eq x, hp_zero, Polynomial.eval_zero, Pi.zero_apply]
  -- The zero set of w (as a Finset) embeds into p.roots
  have h_zero_subset :
      (Finset.univ.filter fun x : F => w x = 0).val ⊆ Polynomial.roots p := by
    intro x hx
    have hx' : x ∈ Finset.univ.filter (fun y : F => w y = 0) := hx
    rw [Finset.mem_filter] at hx'
    refine (Polynomial.mem_roots hp_ne).2 ?_
    show Polynomial.IsRoot p x
    rw [Polynomial.IsRoot, ← hw_eq x]
    exact hx'.2
  have h_zero_card_le : (Finset.univ.filter fun x : F => w x = 0).card ≤ d := by
    have hcard : (Finset.univ.filter fun x : F => w x = 0).card ≤ Polynomial.natDegree p :=
      Polynomial.card_le_degree_of_subset_roots h_zero_subset
    exact hcard.trans hp_deg
  -- Combine with |zeros| + |nonzeros| = |F|.
  have h_partition :
      (Finset.univ.filter fun x : F => w x ≠ 0).card +
      (Finset.univ.filter fun x : F => w x = 0).card = Fintype.card F := by
    simpa only [not_not, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
        (p := fun x : F => w x ≠ 0))
  unfold Generator.fnHammingWeight
  omega

/-- E2: The `univariatePowers F d` generator is MDS over fields with at
least `d + 1` elements. Combines `univariatePowers_dotMap_injective`
with `univariatePowers_inducedCode_minDist`. -/
theorem univariatePowers_IsMDS {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (h_card : d + 1 ≤ Fintype.card F) :
    (Generator.univariatePowers F d).IsMDS := by
  refine ⟨univariatePowers_dotMap_injective h_card, ?_⟩
  have h := univariatePowers_inducedCode_minDist h_card
  -- `Fintype.card F - (d + 1) + 1 = Fintype.card F - d` since `d + 1 ≤ Fintype.card F`.
  have heq : Fintype.card F - (d + 1) + 1 = Fintype.card F - d := by omega
  -- The induced-code's index type for `univariatePowers F d` is `F`.
  show Generator.fnMinDistAtLeast (Generator.univariatePowers F d).inducedCode
    (Fintype.card F - (d + 1) + 1)
  rw [heq]
  exact h

/-! ### affineSpace

**TODO (deferred): `affineSpace_IsMDS`.**

The `affineSpace F s` generator is **not generally MDS** in the strong
Singleton-bound sense over arbitrary fields with `s ≥ 2`.

The induced code has codewords `w : (Fin s → F) → F` of the form
`w x = v 0 + ∑ i, x i * v (i+1)`, i.e. arbitrary affine functions on
`F^s`. The seed type has size `|S| = |F|^s` and the dimension is
`ℓ = s + 1`, so the Singleton bound demands min distance
`|F|^s - (s+1) + 1 = |F|^s - s`.

A nonzero affine function with at least one non-constant term has zero
set equal to an affine hyperplane in `F^s`, which has size `|F|^(s-1)`.
So the actual minimum Hamming weight is `|F|^s - |F|^(s-1) =
|F|^(s-1) · (|F| - 1)`.

For the Singleton bound `|F|^(s-1) · (|F| - 1) ≥ |F|^s - s` to hold we
need `s ≥ |F|^(s-1)`, which fails as soon as `s ≥ 2` and `|F| ≥ 3`
(e.g. `s = 2`, `|F| = 3`: `2 ≥ 3` is false).

So `affineSpace F s` is *only* MDS in the cases `s = 0`, `s = 1`, or
`s = 2 ∧ |F| = 2`. The general statement does not hold. We therefore
defer this — `affineSpace_dotMap_injective` (above) provides the
injectivity half, but the min-distance half cannot be expressed as a
single uniform `IsMDS` claim.

Possible refinements (future work):
* Prove `affineSpace_IsMDS` only under the precondition
  `s ≥ |F|^(s-1)` (equivalently `s ≤ 1` over arbitrary fields, or
  `s ≤ 2` over GF(2)).
* Replace the Singleton bound by the actual bound
  `|F|^(s-1) · (|F| - 1)` and prove a custom `affineSpace_minDist`
  lemma without going through `IsMDS`.
-/

end Generator
end LinearCodes
