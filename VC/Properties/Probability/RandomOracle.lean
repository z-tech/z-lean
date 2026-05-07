import Mathlib.Data.Vector.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Random-oracle infrastructure for VC. See VC/DESIGN.md §3.5.

/-- Idealized random oracle: a function from queries to fixed-size digests.

    Note: although DESIGN.md §3.5 motivates a uniform distribution over
    `ROFunction κ`, the function space `List ByteArray → List.Vector Bool κ`
    has uncountable cardinality (the input list domain is unbounded), so a
    uniform `PMF` over the *full* function space cannot be honestly defined.
    L4 commits to the *interface* (`ROFunction`, `RODistribution`,
    `ROQueryTrace`); the genuine lazy-sampling distribution arrives in L5/L8
    when binding/hiding proofs require it. -/
def ROFunction (κ : Nat) : Type := List ByteArray → List.Vector Bool κ

/-- The "all-zeros" random oracle: maps every query to the all-`false`
    bit-vector. Used as the support point of the placeholder
    `RODistribution`. -/
def ROFunction.zero (κ : Nat) : ROFunction κ :=
  fun _ => List.Vector.replicate κ false

/-- Placeholder distribution: deterministically returns the constant
    "all-zeros" oracle. This is a valid `PMF` (a `Dirac` at `ROFunction.zero`)
    and lets downstream proofs typecheck against `RODistribution`.

    L5/L8 will replace this with the real lazy-sampling distribution; the
    point of L4 is that *the symbol exists with the right type*. -/
noncomputable def RODistribution (κ : Nat) : PMF (ROFunction κ) :=
  PMF.pure (ROFunction.zero κ)

/-- A query-answer trace: queries the algorithm has made to ρ and answers
    received. Used by the §12.3 collision lemma. -/
structure ROQueryTrace (κ : Nat) where
  queries : List (List ByteArray × List.Vector Bool κ)

namespace ROQueryTrace

/-- The empty trace (no queries made yet). -/
def empty (κ : Nat) : ROQueryTrace κ := ⟨[]⟩

instance (κ : Nat) : Inhabited (ROQueryTrace κ) := ⟨ROQueryTrace.empty κ⟩

/-- Append a new query-answer pair to a trace. -/
def append {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) : ROQueryTrace κ :=
  ⟨t.queries ++ [(q, a)]⟩

end ROQueryTrace

-- ## Smoke lemmas

/-- Smoke lemma: the placeholder `RODistribution` is a valid PMF
    (its mass sums to 1, inherited from `PMF.tsum_coe`). -/
theorem RODistribution_tsum_eq_one (κ : Nat) :
    (∑' f : ROFunction κ, RODistribution κ f) = 1 :=
  (RODistribution κ).tsum_coe

/-- Smoke lemma: the empty trace has no queries. -/
@[simp]
theorem ROQueryTrace.empty_queries (κ : Nat) :
    (ROQueryTrace.empty κ).queries = [] := rfl

/-- Smoke lemma: appending a query extends the query list by one entry. -/
@[simp]
theorem ROQueryTrace.append_queries {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) :
    (t.append q a).queries = t.queries ++ [(q, a)] := rfl
