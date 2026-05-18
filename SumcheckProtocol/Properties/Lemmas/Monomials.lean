import CompPoly.Multivariate.CMvMonomial
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Zip

import SumcheckProtocol.Src.CMvPolynomial

open CPoly

@[simp] lemma extract_exp_var_i_eq_get {n : ℕ} (m : CPoly.CMvMonomial n) (x : Fin n) :
    extractExpVarI m x = Vector.get m x := by
  simp [extractExpVarI]

@[simp] lemma extract_exp_var_i_def {n : ℕ} (m : CPoly.CMvMonomial n) (i : Fin n) :
  extractExpVarI (n := n) m i = m.get i := by
  -- This is definitional: toFinsupp = ⟨support, m.get, ...⟩
  rfl

@[simp] lemma extract_exp_var_i_zero {n : ℕ} (i : Fin n) :
  extractExpVarI (n := n) (CPoly.CMvMonomial.zero) i = 0 := by
  -- reduce to Vector.get on a replicated vector
  simp [extractExpVarI, CPoly.CMvMonomial.zero]
  -- goal is now: (Vector.replicate n 0).get i = 0
  -- DON'T `simpa` (it will turn the lemma into `True`); just use it directly:

@[simp] lemma extract_exp_var_i_add {n : ℕ} (m₁ m₂ : CPoly.CMvMonomial n) (i : Fin n) :
  extractExpVarI (n := n) (m₁ + m₂) i
    = extractExpVarI (n := n) m₁ i + extractExpVarI (n := n) m₂ i := by
  -- unfold toFinsupp application (definitional) into `.get`
  -- so we can use the zipWith-get lemma
  cases' i with idx hidx
  -- Expand extractExpVarI
  dsimp [extractExpVarI]
  -- Expand toFinsupp for each term (it stores `get` as the function)
  -- This `change` is definitional: (toFinsupp m) ⟨idx,hidx⟩ = m.get ⟨idx,hidx⟩
  -- change (m₁ + m₂).get ⟨idx, hidx⟩ = m₁.get ⟨idx, hidx⟩ + m₂.get ⟨idx, hidx⟩
  -- Expand monomial addition
  -- CMvMonomial.add := Vector.zipWith Nat.add
  -- and `get ⟨idx,hidx⟩` is definitionally the same as indexing `[idx]`
  -- so we rewrite into a bracket-index goal
  -- (these two changes are definitional, so `rfl`/`simp` isn't needed)
  change (CPoly.CMvMonomial.add m₁ m₂)[idx] = m₁[idx] + m₂[idx]
  -- unfold add to zipWith
  dsimp [CPoly.CMvMonomial.add, CMvMonomial.add, CPoly.CMvMonomial.add]
  -- now apply the lemma exactly
  exact Vector.getElem_zipWith (f := Nat.add) (as := m₁) (bs := m₂) (i := idx) hidx

/-- Your `x^1` monomial in arity 1. -/
def mon_x1 : CPoly.CMvMonomial 1 := ⟨#[1], by decide⟩

@[simp] lemma extract_exp_var_i_mon_x1 :
  extractExpVarI (n := 1) mon_x1 (⟨0, by decide⟩ : Fin 1) = 1 := by
  change mon_x1.get (⟨0, by decide⟩ : Fin 1) = 1
  dsimp [mon_x1]

lemma evalMonomial_monomial_x1
  {𝔽 : Type _} [CommSemiring 𝔽]
  (b : 𝔽) :
  CPoly.MonoR.evalMonomial (n := 1) (R := 𝔽)
      (fun _ : Fin 1 => b) (⟨#[1], by decide⟩ : CPoly.CMvMonomial 1)
    = b := by
  classical
  simp [CPoly.MonoR.evalMonomial, pow_one]
