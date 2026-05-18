import Mathlib.Data.Rat.Init

lemma nat_sub_add_two (n k : ℕ) (hk : k.succ < n) :
    n - (k + 1) = 1 + (n - (k + 2)) := by
  have hle1 : k + 1 ≤ n := Nat.le_of_lt hk
  have hle2 : k + 2 ≤ n := Nat.succ_le_of_lt hk
  let m : ℕ := n - (k + 2)
  have hkm : (k + 2) + m = n := by
    simpa [m] using (Nat.add_sub_of_le hle2)
  have hk1 : (k + 1) + (n - (k + 1)) = n := by
    simpa using (Nat.add_sub_of_le hle1)
  have hk2 : (k + 1) + (1 + m) = n := by
    calc
      (k + 1) + (1 + m) = ((k + 1) + 1) + m := by
        simpa using (Nat.add_assoc (k + 1) 1 m).symm
      _ = (k + 2) + m := by
        simp [Nat.add_assoc]
      _ = n := by
        exact hkm
  have hcancel : n - (k + 1) = 1 + m := by
    -- compare the two decompositions of n and cancel (k+1)
    have hEq : (k + 1) + (n - (k + 1)) = (k + 1) + (1 + m) := by
      exact hk1.trans hk2.symm
    exact Nat.add_left_cancel hEq
  simpa [m] using hcancel
