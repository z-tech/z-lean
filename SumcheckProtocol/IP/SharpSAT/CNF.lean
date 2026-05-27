import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card

namespace SharpSAT

-- A literal over n variables: a variable index and a polarity.
-- pol = true  means the positive literal  xᵢ
-- pol = false means the negative literal ¬xᵢ
structure Literal (n : ℕ) where
  var : Fin n
  pol : Bool
  deriving DecidableEq

-- A literal is satisfied by an assignment iff the assignment matches its polarity.
def Literal.eval {n : ℕ} (x : Fin n → Bool) (ℓ : Literal n) : Bool :=
  x ℓ.var == ℓ.pol

-- A 3-clause is a disjunction of exactly three literals.
structure Clause3 (n : ℕ) where
  ℓ₁ : Literal n
  ℓ₂ : Literal n
  ℓ₃ : Literal n
  deriving DecidableEq

def Clause3.eval {n : ℕ} (x : Fin n → Bool) (c : Clause3 n) : Bool :=
  c.ℓ₁.eval x || c.ℓ₂.eval x || c.ℓ₃.eval x

-- A 3-CNF formula is a conjunction (represented as a list) of 3-clauses.
abbrev CNF3 (n : ℕ) := List (Clause3 n)

def CNF3.eval {n : ℕ} (x : Fin n → Bool) (φ : CNF3 n) : Bool :=
  φ.all (fun c => c.eval x)

-- Prop form for use in statements.
def CNF3.satisfies {n : ℕ} (φ : CNF3 n) (x : Fin n → Bool) : Prop :=
  φ.eval x = true

instance {n : ℕ} (φ : CNF3 n) (x : Fin n → Bool) : Decidable (φ.satisfies x) := by
  unfold CNF3.satisfies; infer_instance

-- Number of satisfying assignments — this is the value #SAT asks about.
def numSatisfying {n : ℕ} (φ : CNF3 n) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => φ.eval x = true)).card

@[simp] lemma CNF3.eval_nil {n : ℕ} (x : Fin n → Bool) :
    CNF3.eval x ([] : CNF3 n) = true := rfl

@[simp] lemma CNF3.eval_cons {n : ℕ} (x : Fin n → Bool) (c : Clause3 n) (φ : CNF3 n) :
    CNF3.eval x (c :: φ) = (c.eval x && φ.eval x) := by
  unfold CNF3.eval; simp [List.all_cons]

lemma numSatisfying_le {n : ℕ} (φ : CNF3 n) :
    numSatisfying φ ≤ 2 ^ n := by
  have : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_pi_const Bool n]; simp
  calc numSatisfying φ
      ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
    _ = Fintype.card (Fin n → Bool) := rfl
    _ = 2 ^ n := this

end SharpSAT
