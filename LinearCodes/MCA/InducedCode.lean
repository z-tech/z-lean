/-
# Generator-induced codes

For a generator `G : S → F^ℓ`, BCGM25 Definition 3.12 introduces the
*generator-induced code* `C_G ⊆ F^|S|`: the `F`-linear span of vectors
of the form `(G(x) · v)_{x∈S}` for `v ∈ F^ℓ`. Equivalently, the range
of the linear map `v ↦ (x ↦ ∑ⱼ G(x)ⱼ · vⱼ)`.

`C_G` is a key abstraction:
* BCGM25 Lemma 3.13 connects MDS structure of `C_G` to zero-evading
  error of `G`.
* The `dim` and `min distance` of `C_G` parameterize many proximity-
  test bounds.
-/

import LinearCodes.MCA.Definitions

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

namespace LinearCodes
namespace Generator

variable {F : Type*} [Field F] {S : Type*} {ℓ : ℕ}

/-- The linear map `v ↦ (x ↦ ∑ⱼ G(x)ⱼ · vⱼ)` from `F^ℓ` to `S → F`. The
generator-induced code is its range. -/
def dotMap (G : Generator F S ℓ) : (Fin ℓ → F) →ₗ[F] (S → F) where
  toFun := fun v x => ∑ j : Fin ℓ, G x j * v j
  map_add' u v := by
    ext x
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros j _
    ring
  map_smul' a v := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _
    ring

/-- Pointwise unfold of `dotMap`. -/
@[simp] theorem dotMap_apply (G : Generator F S ℓ) (v : Fin ℓ → F) (x : S) :
    G.dotMap v x = ∑ j, G x j * v j := rfl

/-- The generator-induced code `C_G`: the linear span of `(G(x) · v)` over
all `v ∈ F^ℓ`. Defined as the range of `dotMap`. -/
def inducedCode (G : Generator F S ℓ) : Submodule F (S → F) :=
  LinearMap.range G.dotMap

/-- `dotMap` sends zero to zero. -/
theorem dotMap_zero (G : Generator F S ℓ) :
    G.dotMap (0 : Fin ℓ → F) = 0 := by
  ext x
  simp

/-- A function `w : S → F` lies in `inducedCode G` iff there is a coefficient
vector `v` whose dot products with `G` produce `w` pointwise. -/
theorem mem_inducedCode_iff (G : Generator F S ℓ) (w : S → F) :
    w ∈ G.inducedCode ↔ ∃ v : Fin ℓ → F, ∀ x : S, w x = ∑ j, G x j * v j := by
  unfold inducedCode
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, fun x => ?_⟩
    rw [← hv]
    rfl
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    ext x
    exact (hv x).symm

/-- `0` always lies in `inducedCode G` (it's a submodule). -/
theorem zero_mem_inducedCode (G : Generator F S ℓ) :
    (0 : S → F) ∈ G.inducedCode :=
  G.inducedCode.zero_mem

/-! ### Hamming-weight machinery for `S → F` codes

We need a sister to `LinearCodes.hammingWeight` (defined for `Fin n → F`)
that operates over any finite index type. This lets us state minimum-
distance hypotheses on `inducedCode G : Submodule F (S → F)`. -/

variable [DecidableEq F]

/-- Number of coordinates where `w : α → F` is nonzero, for any finite
indexing type `α`. -/
def fnHammingWeight {α : Type*} [Fintype α] (w : α → F) : ℕ :=
  (Finset.univ.filter fun i => w i ≠ 0).card

/-- A submodule `c ⊆ α → F` has minimum distance at least `d` if every
nonzero element has at least `d` nonzero coordinates. -/
def fnMinDistAtLeast {α : Type*} [Fintype α] (c : Submodule F (α → F)) (d : ℕ) :
    Prop :=
  ∀ w ∈ c, w ≠ 0 → d ≤ fnHammingWeight w

end Generator

/-! ### BCGM25 Lemma 3.13: zero-evading from induced-code distance -/

theorem fnHammingWeight_le_card {F : Type*} [Field F] [DecidableEq F] {α : Type*} [Fintype α] (w : α → F) : Generator.fnHammingWeight w ≤ Fintype.card α := by
  unfold Generator.fnHammingWeight
  calc
    (Finset.univ.filter (fun x : α => w x ≠ 0)).card ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card α := by rw [Finset.card_univ]

theorem fnZeroCount_eq_card_sub_fnHammingWeight {F : Type*} [Field F] [DecidableEq F] {α : Type*} [Fintype α] (w : α → F) : (Finset.univ.filter (fun x : α => w x = 0)).card = Fintype.card α - Generator.fnHammingWeight w := by
  unfold Generator.fnHammingWeight
  have h :
      (Finset.univ.filter (fun x : α => w x ≠ 0)).card +
        (Finset.univ.filter (fun x : α => w x = 0)).card = Fintype.card α := by
    simpa only [not_not, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (p := fun x : α => w x ≠ 0))
  omega

theorem seedProb_eq_zero_le_of_fnHammingWeight_ge {F : Type*} [Field F] [DecidableEq F] {α : Type*} [Fintype α] [Nonempty α] (w : α → F) (d : ℕ) (hw : d ≤ Generator.fnHammingWeight w) : seedProb (S := α) (fun x => w x = 0) ≤ ((Fintype.card α - d : ℚ) / Fintype.card α) := by
  classical
  unfold seedProb
  have hw_le_card : Generator.fnHammingWeight w ≤ Fintype.card α := fnHammingWeight_le_card w
  have hdcard : d ≤ Fintype.card α := le_trans hw hw_le_card
  have hcount : (Finset.univ.filter (fun x : α => w x = 0)).card ≤ Fintype.card α - d := by
    rw [fnZeroCount_eq_card_sub_fnHammingWeight]
    omega
  have hpos_nat : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
  have hpos : (0 : ℚ) < Fintype.card α := by
    exact_mod_cast hpos_nat
  rw [← Nat.cast_sub hdcard]
  apply (div_le_div_iff_of_pos_right hpos).2
  exact_mod_cast hcount

theorem ZeroEvading_from_inducedCode_min_dist {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] [Nonempty S] {ℓ : ℕ}
    (G : Generator F S ℓ) (d : ℕ)
    (h_dist : Generator.fnMinDistAtLeast G.inducedCode d)
    (h_inj : Function.Injective G.dotMap) :
    ZeroEvading G ((Fintype.card S - d : ℚ) / Fintype.card S) := by
  intro v hv
  let w : S → F := G.dotMap v
  have hw_mem : w ∈ G.inducedCode := by
    rw [Generator.mem_inducedCode_iff]
    refine ⟨v, ?_⟩
    intro x
    rfl
  have hw_nonzero : w ≠ 0 := by
    intro hzero
    apply hv
    apply h_inj
    simpa [w, Generator.dotMap_zero] using hzero
  have hweight : d ≤ Generator.fnHammingWeight w := by
    exact h_dist w hw_mem hw_nonzero
  have hbound := seedProb_eq_zero_le_of_fnHammingWeight_ge (w := w) (d := d) hweight
  simpa [w, Generator.dotMap_apply] using hbound


/-! ### Dimension and injectivity -/

theorem inducedCode_finrank_le {F : Type*} [Field F] {S : Type*} [Fintype S]
    {ℓ : ℕ} (G : Generator F S ℓ) :
    Module.finrank F G.inducedCode ≤ ℓ := by
  have h : Module.finrank F G.inducedCode ≤ Module.finrank F (Fin ℓ → F) :=
    LinearMap.finrank_range_le (f := G.dotMap)
  rwa [Module.finrank_fin_fun] at h


theorem dotMap_injective_iff {F : Type*} [Field F] {S : Type*} {ℓ : ℕ}
    (G : Generator F S ℓ) :
    Function.Injective G.dotMap ↔
    ∀ v : Fin ℓ → F, (∀ x : S, ∑ j, G x j * v j = 0) → v = 0 := by
  constructor
  · intro hinj v hv
    apply hinj
    ext x
    simpa only [Generator.dotMap_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hv x
  · intro hker u v huv
    have hsub : G.dotMap (u - v) = 0 := by
      rw [LinearMap.map_sub, huv, sub_self]
    have huv0 : u - v = 0 := by
      apply hker
      intro x
      have hx := congrFun hsub x
      simpa only [Generator.dotMap_apply, Pi.zero_apply] using hx
    exact sub_eq_zero.mp huv0


/-! ### Singleton bound

The Singleton bound `dim c + d ≤ |α| + 1` for any linear code `c ⊆ α → F`,
proved by puncturing: restricting codewords to `|α| − (d−1)` coordinates is
injective on `c` (two codewords agreeing there would differ on at most
`d − 1` coordinates, but a nonzero codeword has weight `≥ d`), so
`dim c ≤ |α| − (d−1)`. When the bound is met with equality the code is MDS;
`fn_exists_minWeight` extracts the attaining codeword. Both are stated over a
generic finite index type `α`, so they specialise to `Fin n → F` (Reed-Solomon)
and `S → F` (generator-induced codes) alike. They are deliberately placed in
the neutral `LinearCodes` namespace (not `Generator`) since nothing here is
generator-specific. -/

/-- **Singleton bound.** Any linear code `c ⊆ α → F` with minimum distance at
least `d` and positive dimension satisfies `dim c + d ≤ |α| + 1`. -/
theorem fnSingleton_bound {F : Type*} [Field F] [DecidableEq F] {α : Type*}
    [Fintype α] (c : Submodule F (α → F)) (d : ℕ)
    (hc : 0 < Module.finrank F c) (hmd : Generator.fnMinDistAtLeast c d) :
    Module.finrank F c + d ≤ Fintype.card α + 1 := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0
    have h := Submodule.finrank_le c
    rw [Module.finrank_pi] at h
    omega
  · have hbot : c ≠ ⊥ := by
      intro h; rw [h] at hc; simp [finrank_bot] at hc
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff c).mp hbot
    have hdcard : d ≤ Fintype.card α :=
      le_trans (hmd v hv hv0) (fnHammingWeight_le_card v)
    -- choose `d − 1` coordinates to drop; keep `T = Dᶜ`
    obtain ⟨D, _hDsub, hDcard⟩ :=
      Finset.exists_subset_card_eq
        (show d - 1 ≤ (Finset.univ : Finset α).card by rw [Finset.card_univ]; omega)
    set T : Finset α := Dᶜ with hT
    have hTcard : T.card = Fintype.card α - (d - 1) := by
      rw [hT, Finset.card_compl, hDcard]
    -- restriction to the kept coordinates is injective on `c`
    let P : c →ₗ[F] (↥T → F) :=
      (LinearMap.funLeft F F (fun x : ↥T => (x : α))).comp c.subtype
    have hPinj : Function.Injective P := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨w, hw⟩ hPw
      have hwT : ∀ x : α, x ∈ T → w x = 0 := by
        intro x hxT
        have := congrFun hPw (⟨x, hxT⟩ : ↥T)
        simpa [P, LinearMap.funLeft_apply] using this
      have hwle : Generator.fnHammingWeight w ≤ d - 1 := by
        unfold Generator.fnHammingWeight
        have hsub : (Finset.univ.filter fun i => w i ≠ 0) ⊆ D := by
          intro i hi
          rw [Finset.mem_filter] at hi
          by_contra hiD
          exact hi.2 (hwT i (by rw [hT, Finset.mem_compl]; exact hiD))
        calc (Finset.univ.filter fun i => w i ≠ 0).card
            ≤ D.card := Finset.card_le_card hsub
          _ = d - 1 := hDcard
      have hw0 : w = 0 := by
        by_contra hne
        have := hmd w hw hne
        omega
      exact Subtype.ext hw0
    have hfr : Module.finrank F c ≤ T.card := by
      have h := LinearMap.finrank_le_finrank_of_injective hPinj
      rwa [Module.finrank_pi, Fintype.card_coe] at h
    rw [hTcard] at hfr
    omega

/-- **Singleton bound attained ⇒ exact MDS.** A `k`-dimensional code
`c ⊆ α → F` whose minimum distance is at least the Singleton value
`|α| − k + 1` contains a nonzero codeword of weight *exactly* `|α| − k + 1`.
With the `fnMinDistAtLeast` hypothesis this pins the minimum distance to
exactly `|α| − k + 1` (the code is MDS, Singleton met with equality). -/
theorem fn_exists_minWeight {F : Type*} [Field F] [DecidableEq F] {α : Type*}
    [Fintype α] (c : Submodule F (α → F)) (k : ℕ)
    (hfin : Module.finrank F c = k) (hk : 0 < k)
    (hmd : Generator.fnMinDistAtLeast c (Fintype.card α - k + 1)) :
    ∃ w ∈ c, w ≠ 0 ∧ Generator.fnHammingWeight w = Fintype.card α - k + 1 := by
  classical
  have hkn : k ≤ Fintype.card α := by
    have h := Submodule.finrank_le c
    rw [Module.finrank_pi, hfin] at h; exact h
  by_contra hcon
  push_neg at hcon
  -- if no codeword has weight exactly `|α| − k + 1`, the distance is `≥ |α| − k + 2`
  have hmd2 : Generator.fnMinDistAtLeast c (Fintype.card α - k + 1 + 1) := by
    intro w hw hw0
    have hge := hmd w hw hw0
    have hne := hcon w hw hw0
    omega
  have hpos : 0 < Module.finrank F c := by rw [hfin]; exact hk
  have hb := fnSingleton_bound c (Fintype.card α - k + 1 + 1) hpos hmd2
  rw [hfin] at hb
  omega

end LinearCodes
