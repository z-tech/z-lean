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

set_option linter.unusedSectionVars false

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

/-- **BCGM25 Lemma 3.13 (special case).** If the generator-induced code
`C_G` has minimum distance at least `d` and `dotMap` is injective, then
`G` is zero-evading with error `(|S| − d) / |S|`.

Equivalently in BCGM25 notation: `ε_ZE ≤ 1 − δ_{C_G}` where
`δ_{C_G} = d / |S|` is the relative distance. -/
theorem ZeroEvading_from_inducedCode_min_dist
    {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] [Nonempty S] {ℓ : ℕ}
    (G : Generator F S ℓ) (d : ℕ)
    (h_dist : Generator.fnMinDistAtLeast G.inducedCode d)
    (h_inj : Function.Injective G.dotMap) :
    ZeroEvading G ((Fintype.card S - d : ℚ) / Fintype.card S) := by
  sorry

end LinearCodes
