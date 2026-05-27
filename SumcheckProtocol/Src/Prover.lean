import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Hypercube

-- number of open vars
def numOpenVars {n : ℕ} (i : Fin n) : ℕ :=
  n - (i.val + 1)

/-- Right-side map of length (open + 1): first is x0, rest are constants from b. -/
def honestRightMap
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (b : Fin (numOpenVars (n := n) i) → 𝔽) :
    Fin (numOpenVars (n := n) i + 1) → CPoly.CMvPolynomial 1 𝔽
| ⟨0, _⟩ => x0
| ⟨j + 1, hj⟩ =>
    have hj' : j < numOpenVars (n := n) i := by
      exact Nat.lt_of_succ_lt_succ hj
    c1 (b ⟨j, hj'⟩)

/-- The combined substitution map Fin n → CMvPolynomial 1 𝔽 used by the honest prover
    at round i, for a particular hypercube assignment b. -/
def honestCombinedMap
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ} (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (b : Fin (numOpenVars (n := n) i) → 𝔽) :
    Fin n → CPoly.CMvPolynomial 1 𝔽 :=
  have hn : i.val + (numOpenVars (n := n) i + 1) = n := by
    set m : ℕ := numOpenVars (n := n) i
    have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    have h1 : (i.val + 1) + m = n := by
      simp [m, numOpenVars, Nat.add_sub_of_le hle]
    calc
      i.val + (m + 1)
          = i.val + m + 1 := by simp [Nat.add_assoc]
      _   = i.val + 1 + m := by
              simpa [Nat.add_assoc] using (Nat.add_right_comm i.val m 1)
      _   = (i.val + 1) + m := by simp [Nat.add_assoc]
      _   = n := h1
  appendVariableAssignments (𝔽 := 𝔽) (k := i.val) (m := numOpenVars (n := n) i + 1)
    (n := n) hn
    (left := fun j => c1 (challenges j))
    (right := honestRightMap (𝔽 := 𝔽) (n := n) i b)

/-- New lemma-friendly API: specify the round by i : Fin n directly. -/
def honestProverMessageAt
  {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
  {n : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  sumOverDomainRecursive (β := CPoly.CMvPolynomial 1 𝔽)
    domain
    (add := fun a b =>
      @HAdd.hAdd (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽) (CPoly.CMvPolynomial 1 𝔽)
        instHAdd a b)
    (zero := c1 (𝔽 := 𝔽) 0)
    (m := numOpenVars (n := n) i)
    (F := fun b =>
      CPoly.eval₂Poly c1 (honestCombinedMap (𝔽 := 𝔽) (n := n) i challenges b) p)
