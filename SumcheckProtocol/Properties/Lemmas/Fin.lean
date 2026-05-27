import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

import SumcheckProtocol.Properties.Lemmas.List
import SumcheckProtocol.Properties.Lemmas.Degree

def honestSplitEqCast {n : ℕ} (i : Fin n) (m : ℕ)
    (hm : numOpenVars (n := n) i = m) :
    i.val + (m + 1) = n :=
by
  exact
    Eq.ndrec
      (motive := fun m => i.val + (m + 1) = n)
      (honest_split_eq (n := n) i)
      hm

lemma foldl_finRange_mul_eq_prod
  {α : Type _} [CommMonoid α] :
  ∀ (n : ℕ) (g : Fin n → α) (s0 : α),
    List.foldl (fun s i => s * g i) s0 (List.finRange n)
      =
    s0 * ∏ i : Fin n, g i
| 0, g, s0 => by
    simp
| n+1, g, s0 => by
    classical
    simp [List.finRange_succ, List.foldl_map, Fin.prod_univ_succ]
    have h := foldl_finRange_mul_eq_prod n (fun i : Fin n => g i.succ) (s0 * g 0)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

lemma cast_split_eq_succ_castSucc {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n) (t0 : Fin i.val) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k
      =
    Fin.castAdd (numOpenVars (n := n) j + 1) (Fin.castSucc t0)
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.castAdd (numOpenVars (n := n) i + 1) t0 := by
  classical
  dsimp
  intro h
  have hv : k.val = t0.val := by
    -- take values
    have := congrArg Fin.val h
    simpa using this
  -- now ext
  apply Fin.ext
  -- show vals equal
  simp [hv]

lemma cast_split_eq_succ_last {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k
      =
    Fin.castAdd (numOpenVars (n := n) j + 1) (Fin.last i.val)
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.natAdd i.val (0 : Fin (numOpenVars (n := n) i + 1)) := by
  -- unfold the `let` binder in the statement
  dsimp
  intro h
  have hk : k.val = i.val := by
    have hval := congrArg Fin.val h
    simpa using hval
  apply Fin.ext
  -- Compare values on both sides.
  simp [hk]

lemma cast_split_eq_succ_right {n : ℕ} (i : Fin n) (hlt : i.val.succ < n) (k : Fin n)
  (t : Fin (numOpenVars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1))
  (hm1 :
    numOpenVars (n := n) (⟨i.val.succ, hlt⟩ : Fin n) + 1 + 1
      = numOpenVars (n := n) i + 1) :
  let j : Fin n := ⟨i.val.succ, hlt⟩
  Fin.cast (honest_split_eq (n := n) j).symm k = Fin.natAdd j.val t
  →
  Fin.cast (honest_split_eq (n := n) i).symm k
    =
  Fin.natAdd i.val (Fin.cast hm1 (Fin.succ t)) := by
  classical
  dsimp
  intro hk
  have hkval : k.val = i.val + t.val.succ := by
    have hk' := congrArg Fin.val hk
    -- hk' : (Fin.cast ... k).val = (Fin.natAdd ... t).val
    -- simplify values
    -- first get k.val = i.val.succ + t.val
    have hk'' : k.val = i.val.succ + t.val := by
      simpa using hk'
    -- convert succ_add
    simpa [Nat.succ_add_eq_add_succ] using hk''
  apply Fin.ext
  -- reduce to equality on values
  simpa using hkval
