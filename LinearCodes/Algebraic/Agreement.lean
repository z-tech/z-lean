/-
# Agreement sets

The agreement set of two vectors `u, v : Fin n → F` is the set of
coordinates where they coincide. This is the central combinatorial
object in the BCGM25 mutual-correlated-agreement framework — proximity
gap arguments work by tracking how agreement sets compose under linear
combinations.

This file establishes the basic algebra of agreement sets:
* Symmetry: `agreementSet u v = agreementSet v u`.
* Self-agreement: `agreementSet u u = univ`.
* Complement to Hamming distance: `card + hammingDistance = n`.
* Closure under linear combinations: agreement on `S` for `(uᵢ, vᵢ)`
  is preserved by any fixed linear combination, on the intersection
  of the per-component agreement sets.
-/

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

namespace LinearCodes

variable {F : Type*} {n : ℕ}

/-- Number of coordinates where `u` and `v` differ. We define this directly
on `Fin n → F` rather than going through `Mathlib.InformationTheory.Hamming`
to avoid the type-synonym coercion. -/
def hammingDistance [DecidableEq F] (u v : Fin n → F) : ℕ :=
  (Finset.univ.filter fun i => u i ≠ v i).card

/-- The agreement set: coordinates where `u` and `v` coincide. -/
def agreementSet [DecidableEq F] (u v : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter fun i => u i = v i

/-! ### Basic identities -/

/-- Agreement-set membership unfolds to per-coordinate equality. -/
@[simp] theorem mem_agreementSet [DecidableEq F] {u v : Fin n → F} {i : Fin n} :
    i ∈ agreementSet u v ↔ u i = v i := by
  simp [agreementSet]

/-- The agreement set is symmetric in its arguments. -/
theorem agreementSet_comm [DecidableEq F] (u v : Fin n → F) :
    agreementSet u v = agreementSet v u := by
  ext i
  simp only [mem_agreementSet]
  exact eq_comm

/-- A vector agrees with itself on every coordinate. -/
theorem agreementSet_self [DecidableEq F] (u : Fin n → F) :
    agreementSet u u = Finset.univ := by
  ext i
  simp [agreementSet]

/-- Agreement-set cardinality and Hamming distance partition `[n]`. -/
theorem agreementSet_card_add_hammingDistance [DecidableEq F] (u v : Fin n → F) :
    (agreementSet u v).card + hammingDistance u v = n := by
  unfold agreementSet hammingDistance
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

/-! ### Closure under linear combinations -/

/-- If `u₁ ↔ v₁` agree on `S₁` and `u₂ ↔ v₂` agree on `S₂`, then for any
fixed coefficients `α, β`, the linear combinations agree on `S₁ ∩ S₂`. -/
theorem agreementSet_linComb_subset
    {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (α β : F) (u₁ v₁ u₂ v₂ : Fin n → F) :
    agreementSet u₁ v₁ ∩ agreementSet u₂ v₂ ⊆
      agreementSet (α • u₁ + β • u₂) (α • v₁ + β • v₂) := by
  intro i hi
  simp only [Finset.mem_inter, mem_agreementSet] at hi
  simp only [mem_agreementSet, Pi.add_apply, Pi.smul_apply, hi.1, hi.2]

end LinearCodes
