import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

import SumcheckProtocol.Src.CMvPolynomial

-- glue together the substitution functions left and right
def appendVariableAssignments
  {𝔽 : Type _} [CommSemiring 𝔽]
  {k m n : ℕ}
  (hn : k + m = n)
  (left : Fin k → CPoly.CMvPolynomial 1 𝔽)
  (right : Fin m → CPoly.CMvPolynomial 1 𝔽) : Fin n → CPoly.CMvPolynomial 1 𝔽 :=
fun i =>
  Fin.addCases (m := k) (n := m) (motive := fun _ => CPoly.CMvPolynomial 1 𝔽)
    left right (Fin.cast hn.symm i)

/-- Sum a function `F` over all assignments from `domain^m`.
    Generalizes the boolean hypercube sum from `{0,1}^m` to an arbitrary finite domain.
    - `domain`: the finite set of values for each variable (as a list)
    - `add`: a binary operation to combine results (typically `(· + ·)`)
    - `zero`: the identity element for `add` (typically `0`)
    - `m`: the number of variables to sum over
    - `F`: the function to evaluate at each assignment -/
def sumOverDomainRecursive
  {𝔽 β : Type _}
  (domain : List 𝔽)
  (add : β → β → β) (zero : β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) : β :=
  match m, F with
  | 0, F => F Fin.elim0
  | m + 1, F =>
      let extend (a : 𝔽) (x : Fin m → 𝔽) : Fin (m + 1) → 𝔽 :=
        fun i => Fin.cases a x i
      domain.foldl (fun acc a => add acc (sumOverDomainRecursive domain add zero (fun x => F (extend a x)))) zero

@[simp] theorem sumOverDomainRecursive.eq_zero {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β) (F : (Fin 0 → 𝔽) → β) :
  sumOverDomainRecursive domain add zero F = F Fin.elim0 := rfl

@[simp] theorem sumOverDomainRecursive.eq_succ {𝔽 β : Type _}
  (domain : List 𝔽) (add : β → β → β) (zero : β) {m : ℕ} (F : (Fin (m + 1) → 𝔽) → β) :
  sumOverDomainRecursive domain add zero F =
    domain.foldl (fun acc a => add acc (sumOverDomainRecursive domain add zero
      (fun x => F (fun i => Fin.cases a x i)))) zero := rfl

attribute [irreducible] sumOverDomainRecursive

/-- Sum over the boolean hypercube {b0, b1}^m. Kept for backwards compatibility. -/
def sumOverHypercubeRecursive
  {𝔽 β : Type _}
  (b0 b1 : 𝔽)
  (add : β → β → β)
  {m : ℕ}
  (F : (Fin m → 𝔽) → β) : β :=
  match m, F with
  | 0, F => F Fin.elim0
  | m + 1, F =>
      let extend (b : 𝔽) (x : Fin m → 𝔽) : Fin (m + 1) → 𝔽 :=
        fun i => Fin.cases b x i
      add (sumOverHypercubeRecursive b0 b1 add (fun x => F (extend b0 x)))
          (sumOverHypercubeRecursive b0 b1 add (fun x => F (extend b1 x)))

@[simp] theorem sumOverHypercubeRecursive.eq_zero {𝔽 β : Type _}
  (b0 b1 : 𝔽) (add : β → β → β) (F : (Fin 0 → 𝔽) → β) :
  sumOverHypercubeRecursive b0 b1 add F = F Fin.elim0 := rfl

@[simp] theorem sumOverHypercubeRecursive.eq_succ {𝔽 β : Type _}
  (b0 b1 : 𝔽) (add : β → β → β) {m : ℕ} (F : (Fin (m + 1) → 𝔽) → β) :
  sumOverHypercubeRecursive b0 b1 add F =
    add (sumOverHypercubeRecursive b0 b1 add (fun x => F (fun i => Fin.cases b0 x i)))
        (sumOverHypercubeRecursive b0 b1 add (fun x => F (fun i => Fin.cases b1 x i))) := rfl

attribute [irreducible] sumOverHypercubeRecursive

/-- Non-dependent `Fin.addCases` specialized to functions. Avoids needing to specify `motive`. -/
def addCasesFun {α : Type*} {m n : ℕ}
  (f : Fin m → α) (g : Fin n → α) : Fin (m + n) → α :=
fun i => Fin.addCases (m := m) (n := n) (motive := fun _ => α) f g i

def residualSum
  {𝔽 : Type*} [CommRing 𝔽] [DecidableEq 𝔽]
  {k numVars : ℕ}
  (domain : List 𝔽)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial numVars 𝔽)
  (hk : k ≤ numVars) : 𝔽 :=
  let openVars : ℕ := numVars - k
  have hn : k + openVars = numVars := by
    simpa [openVars] using Nat.add_sub_of_le hk
  sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
    domain (· + ·) 0 (m := openVars)
    (fun x =>
      let point : Fin numVars → 𝔽 :=
        fun i => addCasesFun ch x (Fin.cast hn.symm i)
      CPoly.CMvPolynomial.eval point p)

def residualSumWithOpenVars
  {𝔽 : Type*} [CommRing 𝔽] [DecidableEq 𝔽]
  {k n : ℕ}
  (domain : List 𝔽)
  (openVars : ℕ)
  (hn : k + openVars = n)
  (ch : Fin k → 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
  sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
    domain (· + ·) 0 (m := openVars)
    (fun x =>
      let point : Fin n → 𝔽 := fun i => addCasesFun ch x (Fin.cast hn.symm i)
      CPoly.CMvPolynomial.eval point p)

def roundSum
  {𝔽 : Type*} [CommRing 𝔽] [DecidableEq 𝔽]
  {numChallenges numVars : ℕ}
  (domain : List 𝔽)
  (challenges : Fin numChallenges → 𝔽)
  (current : 𝔽)
  (p : CPoly.CMvPolynomial numVars 𝔽)
  (hcard : numChallenges + 1 ≤ numVars) : 𝔽 :=
  -- the same as residual sum after fixing the current variable
  residualSum (𝔽 := 𝔽)
    domain
    (k := numChallenges + 1) (numVars := numVars)
    (ch := Fin.snoc challenges current)
    (p := p)
    (hk := hcard)

-- The claim the honest prover makes: the sum of p over domain^n
def honestClaim
  {n : ℕ} {𝔽 : Type*} [CommRing 𝔽] [DecidableEq 𝔽]
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
  residualSum (𝔽 := 𝔽) domain (k := 0) (numVars := n) Fin.elim0 p (Nat.zero_le n)
