/-
# Linear-code basics

A linear code is an `F`-linear subspace of `Fⁿ`. Throughout the
BCGM25 formalization, codes are represented as predicates on
`Submodule F (Fin n → F)` rather than wrapped records — lighter and
fully expressive for our needs.

Definitions in this file:
* `hammingWeight v` — the count of nonzero coordinates.
* `MinDistAtLeast c d` — every nonzero element of `c` has weight ≥ `d`.
* `IsMDS c k` — `c` has dimension `k` and meets the Singleton bound.

Theorems:
* `hammingWeight_zero` — the zero vector has weight zero.
* `hammingWeight_eq_zero_iff` — characterisation of weight-zero vectors.
* `hammingDistance_eq_hammingWeight_sub` — bridge between distance and
  weight via the F-module structure.
* `hammingWeight_le` — every weight is bounded by `n`.
-/

import LinearCodes.Algebraic.Agreement
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Submodule.Basic

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] {n : ℕ}

/-- The Hamming weight of a vector: the number of coordinates where it
is nonzero. -/
def hammingWeight [DecidableEq F] (v : Fin n → F) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-- A submodule has minimum distance at least `d` if every nonzero element
has Hamming weight at least `d`. -/
def MinDistAtLeast [DecidableEq F] (c : Submodule F (Fin n → F)) (d : ℕ) : Prop :=
  ∀ v ∈ c, v ≠ 0 → d ≤ hammingWeight v

/-- A linear code is **maximum-distance separable** (MDS) iff its dimension
is `k` and its minimum distance is at least `n − k + 1` (the Singleton
bound, achieved with equality). -/
def IsMDS [DecidableEq F] (c : Submodule F (Fin n → F)) (k : ℕ) : Prop :=
  Module.finrank F c = k ∧ MinDistAtLeast c (n - k + 1)

/-- Accessor: an MDS submodule's min-distance bound. -/
theorem IsMDS.minDistAtLeast {n k : ℕ} {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {c : Submodule F (Fin n → F)} (h : IsMDS c k) :
    MinDistAtLeast c (n - k + 1) := h.2

/-- Accessor: an MDS submodule's dimension. -/
theorem IsMDS.finrank_eq {n k : ℕ} {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {c : Submodule F (Fin n → F)} (h : IsMDS c k) :
    Module.finrank F c = k := h.1

/-! ### Basic identities for `hammingWeight` -/

/-- The zero vector has weight zero. -/
theorem hammingWeight_zero [DecidableEq F] : hammingWeight (0 : Fin n → F) = 0 := by
  simp [hammingWeight]

/-- A vector has weight zero iff it is the zero vector. -/
theorem hammingWeight_eq_zero_iff [DecidableEq F] {v : Fin n → F} :
    hammingWeight v = 0 ↔ v = 0 := by
  unfold hammingWeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    have := h (Finset.mem_univ i)
    exact not_not.mp this
  · intro h i _
    simp [h]

/-- Hamming distance equals the weight of the difference. -/
theorem hammingDistance_eq_hammingWeight_sub [DecidableEq F]
    (u v : Fin n → F) :
    hammingDistance u v = hammingWeight (u - v) := by
  unfold hammingDistance hammingWeight
  congr 1
  ext i
  simp [Pi.sub_apply, sub_ne_zero]

/-- Every Hamming weight is at most `n`. -/
theorem hammingWeight_le [DecidableEq F] (v : Fin n → F) :
    hammingWeight v ≤ n := by
  unfold hammingWeight
  calc (Finset.univ.filter fun i => v i ≠ 0).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-! ### Hamming distance algebra -/

/-- A vector has zero distance to itself. -/
theorem hammingDistance_self [DecidableEq F] (u : Fin n → F) :
    hammingDistance u u = 0 := by
  simp [hammingDistance]

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm [DecidableEq F] (u v : Fin n → F) :
    hammingDistance u v = hammingDistance v u := by
  unfold hammingDistance
  congr 1
  ext i
  simp [ne_comm]

/-- Two vectors are equal iff their Hamming distance is zero. -/
theorem hammingDistance_eq_zero_iff [DecidableEq F] {u v : Fin n → F} :
    hammingDistance u v = 0 ↔ u = v := by
  unfold hammingDistance
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    have := h (Finset.mem_univ i)
    exact not_not.mp this
  · intro h i _
    simp [h]

/-- Hamming distance is bounded by the codeword length. -/
theorem hammingDistance_le [DecidableEq F] (u v : Fin n → F) :
    hammingDistance u v ≤ n := by
  unfold hammingDistance
  calc (Finset.univ.filter fun i => u i ≠ v i).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-- Triangle inequality for Hamming distance. -/
theorem hammingDistance_triangle [DecidableEq F] (u v w : Fin n → F) :
    hammingDistance u w ≤ hammingDistance u v + hammingDistance v w := by
  unfold hammingDistance
  calc (Finset.univ.filter fun i => u i ≠ w i).card
      ≤ ((Finset.univ.filter fun i => u i ≠ v i) ∪
         (Finset.univ.filter fun i => v i ≠ w i)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at *
        by_contra h_neg
        push_neg at h_neg
        apply hi
        rw [h_neg.1, h_neg.2]
    _ ≤ _ := Finset.card_union_le _ _

/-- Hamming weight equals distance from zero. -/
theorem hammingWeight_eq_hammingDistance_zero [DecidableEq F] (v : Fin n → F) :
    hammingWeight v = hammingDistance v 0 := by
  simp [hammingWeight, hammingDistance]

/-- Hamming weight is invariant under negation. -/
theorem hammingWeight_neg [DecidableEq F] (v : Fin n → F) :
    hammingWeight (-v) = hammingWeight v := by
  unfold hammingWeight
  congr 1
  ext i
  simp [Pi.neg_apply]

/-- Multiplying by a nonzero scalar preserves Hamming weight. -/
theorem hammingWeight_smul [DecidableEq F] {α : F} (hα : α ≠ 0) (v : Fin n → F) :
    hammingWeight (α • v) = hammingWeight v := by
  unfold hammingWeight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply,
    smul_eq_mul, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨hα, h⟩⟩

/-- Subadditivity of Hamming weight under vector addition. -/
theorem hammingWeight_add_le [DecidableEq F] (u v : Fin n → F) :
    hammingWeight (u + v) ≤ hammingWeight u + hammingWeight v := by
  unfold hammingWeight
  calc (Finset.univ.filter fun i => (u + v) i ≠ 0).card
      ≤ ((Finset.univ.filter fun i => u i ≠ 0) ∪
         (Finset.univ.filter fun i => v i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                   Pi.add_apply] at *
        by_contra h_neg
        push_neg at h_neg
        apply hi
        rw [h_neg.1, h_neg.2, add_zero]
    _ ≤ _ := Finset.card_union_le _ _

/-- Hamming distance equals `n` minus the agreement-set size. -/
theorem hammingDistance_eq_n_sub_agreementSet [DecidableEq F] (u v : Fin n → F) :
    hammingDistance u v = n - (agreementSet u v).card := by
  have h := agreementSet_card_add_hammingDistance u v
  omega

/-! ### MinDist properties -/

/-- Every code has minimum distance at least zero (vacuous). -/
theorem MinDistAtLeast_zero [DecidableEq F] (c : Submodule F (Fin n → F)) :
    MinDistAtLeast c 0 := by
  intro v _ _
  exact Nat.zero_le _

/-- A weaker minimum-distance bound is implied by a stronger one. -/
theorem MinDistAtLeast_mono [DecidableEq F] {c : Submodule F (Fin n → F)}
    {d d' : ℕ} (h : d ≤ d') (hd' : MinDistAtLeast c d') :
    MinDistAtLeast c d := by
  intro v hv hne
  exact h.trans (hd' v hv hne)

/-- Unfold-form for `MinDistAtLeast`. -/
theorem MinDistAtLeast_iff [DecidableEq F] (c : Submodule F (Fin n → F)) (d : ℕ) :
    MinDistAtLeast c d ↔ ∀ v ∈ c, v ≠ 0 → d ≤ hammingWeight v := Iff.rfl

/-! ### More distance/weight identities -/

/-- Hamming distance is translation-invariant: `d(u + w, v + w) = d(u, v)`. -/
theorem hammingDistance_translate [DecidableEq F] (u v w : Fin n → F) :
    hammingDistance (u + w) (v + w) = hammingDistance u v := by
  unfold hammingDistance
  congr 1
  ext i
  simp [Pi.add_apply, add_left_inj]

/-- A vector has full weight (`n`) iff it has no zero coordinate. -/
theorem hammingWeight_eq_n_iff [DecidableEq F] {v : Fin n → F} :
    hammingWeight v = n ↔ ∀ i, v i ≠ 0 := by
  unfold hammingWeight
  constructor
  · intro h i hzero
    have hssub : (Finset.univ.filter fun j => v j ≠ 0) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro h_eq
      have hi : i ∈ (Finset.univ : Finset (Fin n)).filter (fun j => v j ≠ 0) := by
        rw [h_eq]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2 hzero
    have hlt := Finset.card_lt_card hssub
    rw [Finset.card_univ, Fintype.card_fin] at hlt
    omega
  · intro h
    rw [show (Finset.univ.filter fun i => v i ≠ 0) = Finset.univ from
      Finset.filter_true_of_mem (fun i _ => h i)]
    rw [Finset.card_univ, Fintype.card_fin]

/-- Hamming distance equals `0` iff the vectors are equal — alias of
`hammingDistance_eq_zero_iff` packaged for `simp`. -/
@[simp] theorem hammingDistance_eq_zero [DecidableEq F] {u v : Fin n → F} :
    hammingDistance u v = 0 ↔ u = v :=
  hammingDistance_eq_zero_iff

/-! ### Hamming distance bounded by complement of agreement -/

/-- If `u` and `v` agree on every coordinate of `T`, the Hamming distance is
bounded by the number of coordinates outside `T`. -/
theorem hammingDistance_le_of_agree_on [DecidableEq F]
    {u v : Fin n → F} {T : Finset (Fin n)}
    (h_agree : ∀ i ∈ T, u i = v i) :
    hammingDistance u v ≤ n - T.card := by
  unfold hammingDistance
  calc (Finset.univ.filter fun i => u i ≠ v i).card
      ≤ (Finset.univ \ T).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hT
        exact hi.2 (h_agree i hT)
    _ = n - T.card := by
        rw [Finset.card_univ_diff, Fintype.card_fin]

/-! ### MDS rigidity: codewords agreeing on `≥ k` positions are equal -/

/-- **Key lemma for §6.1.** In an MDS code with dimension `k`, two codewords
that agree on a set `T` of size at least `k` must be equal. This is the
algebraic backbone of BCGM25 Theorem 6.1's polynomial argument. -/
theorem agreement_implies_eq_of_MDS [DecidableEq F]
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    {u v : Fin n → F} (hu : u ∈ c) (hv : v ∈ c)
    {T : Finset (Fin n)} (h_size : k ≤ T.card)
    (h_agree : ∀ i ∈ T, u i = v i) :
    u = v := by
  by_contra h_ne
  obtain ⟨_h_dim, h_mindist⟩ := h_MDS
  have h_sub_mem : u - v ∈ c := c.sub_mem hu hv
  have h_sub_ne : u - v ≠ 0 := sub_ne_zero.mpr h_ne
  have h_lo := h_mindist (u - v) h_sub_mem h_sub_ne
  have h_eq := hammingDistance_eq_hammingWeight_sub u v
  have h_hi := hammingDistance_le_of_agree_on h_agree
  have h_chain : n - k + 1 ≤ n - T.card := by
    rw [← h_eq] at h_lo
    exact h_lo.trans h_hi
  omega

/-! ### MDS corollaries for §6.1 capstone -/

/-- **Contrapositive of MDS rigidity.** In an MDS code with dimension `k`,
two distinct codewords agree on strictly fewer than `k` positions. -/
theorem MDS_distinct_codewords_disagree [DecidableEq F]
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    {u v : Fin n → F} (hu : u ∈ c) (hv : v ∈ c) (h_ne : u ≠ v) :
    (agreementSet u v).card < k := by
  by_contra h_size_ge
  push_neg at h_size_ge
  apply h_ne
  apply agreement_implies_eq_of_MDS h_MDS hu hv h_size_ge
  intros i hi
  exact mem_agreementSet.mp hi

/-- **Pairwise agreement bound for §6.1.** Given a fixed vector `u` and two
distinct codewords `c₁, c₂` in a dimension-`k` MDS code, the intersection
of their agreement sets with `u` has size strictly less than `k`. This
is the bound that plugs into Corrádi to count "bad" seeds in BCGM25
Theorem 6.1's proof. -/
theorem MDS_pairwise_agreement_bound [DecidableEq F]
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    (u : Fin n → F)
    {c₁ c₂ : Fin n → F} (hc₁ : c₁ ∈ c) (hc₂ : c₂ ∈ c) (h_ne : c₁ ≠ c₂) :
    (agreementSet u c₁ ∩ agreementSet u c₂).card < k := by
  have h_subset : agreementSet u c₁ ∩ agreementSet u c₂ ⊆ agreementSet c₁ c₂ := by
    intro i hi
    simp only [Finset.mem_inter, mem_agreementSet] at hi
    simp only [mem_agreementSet]
    rw [← hi.1, hi.2]
  have h_card_le : (agreementSet u c₁ ∩ agreementSet u c₂).card ≤ (agreementSet c₁ c₂).card :=
    Finset.card_le_card h_subset
  have h_lt : (agreementSet c₁ c₂).card < k :=
    MDS_distinct_codewords_disagree h_MDS hc₁ hc₂ h_ne
  exact lt_of_le_of_lt h_card_le h_lt

/-- **Classical unique-decoding bound.** In a dimension-`k` MDS code, if
two codewords are each at distance ≤ `(n−k)/2` from a fixed vector `u`,
they must be equal. -/
theorem MDS_unique_decoding [DecidableEq F]
    {k : ℕ} {c : Submodule F (Fin n → F)}
    (h_MDS : IsMDS c k)
    (u : Fin n → F)
    {c₁ c₂ : Fin n → F} (hc₁ : c₁ ∈ c) (hc₂ : c₂ ∈ c)
    (h₁ : 2 * hammingDistance u c₁ ≤ n - k)
    (h₂ : 2 * hammingDistance u c₂ ≤ n - k) :
    c₁ = c₂ := by
  by_contra h_ne
  have h_tri : hammingDistance c₁ c₂ ≤ hammingDistance c₁ u + hammingDistance u c₂ :=
    hammingDistance_triangle c₁ u c₂
  rw [hammingDistance_comm c₁ u] at h_tri
  have h_sub_mem : c₁ - c₂ ∈ c := c.sub_mem hc₁ hc₂
  have h_sub_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  obtain ⟨_h_dim, h_mindist⟩ := h_MDS
  have h_lo : n - k + 1 ≤ hammingWeight (c₁ - c₂) := h_mindist (c₁ - c₂) h_sub_mem h_sub_ne
  rw [← hammingDistance_eq_hammingWeight_sub] at h_lo
  omega

/-! ### MinDistAtLeast strengthening of MDS rigidity -/

/-- **MinDist version of MDS rigidity.** In a code with minimum distance
at least `d`, two codewords agreeing on more than `n − d` positions are
equal. This generalizes `agreement_implies_eq_of_MDS` to the
`MinDistAtLeast` predicate (without requiring `IsMDS`). -/
theorem MinDistAtLeast.codewords_eq_of_agree [DecidableEq F]
    {d : ℕ} {c : Submodule F (Fin n → F)} (h_minDist : MinDistAtLeast c d)
    {u v : Fin n → F} (hu : u ∈ c) (hv : v ∈ c)
    {T : Finset (Fin n)} (hT : T.card > n - d)
    (h_agree : ∀ i ∈ T, u i = v i) :
    u = v := by
  by_contra h_ne
  have h_sub_mem : u - v ∈ c := c.sub_mem hu hv
  have h_sub_ne : u - v ≠ 0 := sub_ne_zero.mpr h_ne
  have h_lo := h_minDist (u - v) h_sub_mem h_sub_ne
  have h_eq := hammingDistance_eq_hammingWeight_sub u v
  have h_hi := hammingDistance_le_of_agree_on h_agree
  rw [← h_eq] at h_lo
  have hT_le_n : T.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ T)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have : d ≤ n - T.card := h_lo.trans h_hi
  omega

/-- Contrapositive of `MinDistAtLeast.codewords_eq_of_agree`: distinct codewords
disagree on a substantial fraction of coordinates. If `u, v ∈ c` are distinct
codewords agreeing on a set `T`, then `T` has cardinality at most `n - d`. -/
theorem MinDistAtLeast.disagree_count_of_ne [DecidableEq F]
    {d : ℕ} {c : Submodule F (Fin n → F)} (h_minDist : MinDistAtLeast c d)
    {u v : Fin n → F} (hu : u ∈ c) (hv : v ∈ c) (h_ne : u ≠ v)
    (T : Finset (Fin n)) (h_agree : ∀ i ∈ T, u i = v i) :
    T.card ≤ n - d := by
  by_contra h
  push_neg at h
  exact h_ne (h_minDist.codewords_eq_of_agree hu hv h h_agree)

end LinearCodes
