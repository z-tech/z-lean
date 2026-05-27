import Mathlib.Data.Vector.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Random-oracle infrastructure for VectorCommitment

This file provides two layers:

1. **Legacy interface (L4 placeholder).** `ROFunction`, `RODistribution`,
   `ROQueryTrace` — the function-view of an RO. `RODistribution` is a
   `PMF.pure` placeholder because the full function space `List ByteArray →
   List.Vector Bool κ` has uncountable cardinality, so a uniform `PMF`
   over it cannot be honestly defined as a single distribution.

2. **Lazy-sampling model (the real RO).** `OracleSpec`, `QueryLog`,
   `OracleComp`, `query`, `simulateQ`. Operationally identical to the
   function view but well-defined: queries are sampled fresh on first
   encounter and cached. Probability of any finite event is honest.

API names mirror [VCVio](https://github.com/Verified-zkEVM/VCV-io) so that
when VCVio updates to Lean 4.28+ the dependency swap becomes a mechanical
rename (`import VectorCommitment.Properties.Probability.RandomOracle` →
`import VCVio.OracleComp.QueryTracking.CachingOracle`).
-/

-- ---------------------------------------------------------------------------
-- Layer 1: legacy interface (kept verbatim for downstream compatibility).
-- ---------------------------------------------------------------------------

/-- Idealized random oracle: a function from queries to fixed-size digests. -/
def ROFunction (κ : Nat) : Type := List ByteArray → List.Vector Bool κ

/-- The "all-zeros" random oracle. -/
def ROFunction.zero (κ : Nat) : ROFunction κ :=
  fun _ => List.Vector.replicate κ false

/-- Placeholder distribution: a Dirac mass at the all-zeros oracle. Kept
    for backwards compatibility with L4 lemma signatures. Real
    probabilistic content lives in the lazy-sampling layer below. -/
noncomputable def RODistribution (κ : Nat) : PMF (ROFunction κ) :=
  PMF.pure (ROFunction.zero κ)

/-- A query-answer trace (function-view). -/
structure ROQueryTrace (κ : Nat) where
  queries : List (List ByteArray × List.Vector Bool κ)

namespace ROQueryTrace

def empty (κ : Nat) : ROQueryTrace κ := ⟨[]⟩

instance (κ : Nat) : Inhabited (ROQueryTrace κ) := ⟨ROQueryTrace.empty κ⟩

def append {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) : ROQueryTrace κ :=
  ⟨t.queries ++ [(q, a)]⟩

end ROQueryTrace

/-- Smoke lemma: the placeholder is a valid PMF. -/
theorem RODistribution_tsum_eq_one (κ : Nat) :
    (∑' f : ROFunction κ, RODistribution κ f) = 1 :=
  (RODistribution κ).tsum_coe

@[simp]
theorem ROQueryTrace.empty_queries (κ : Nat) :
    (ROQueryTrace.empty κ).queries = [] := rfl

@[simp]
theorem ROQueryTrace.append_queries {κ : Nat} (t : ROQueryTrace κ)
    (q : List ByteArray) (a : List.Vector Bool κ) :
    (t.append q a).queries = t.queries ++ [(q, a)] := rfl

-- ---------------------------------------------------------------------------
-- Layer 2: lazy-sampling model (the real RO).
-- ---------------------------------------------------------------------------

/-- Specification of a random oracle: query and response types, plus the
    instances needed for sampling and caching.

    For Merkle we typically instantiate with `Domain = List ByteArray`
    (tagged-input encoding handles domain separation) and
    `Range = List.Vector Bool κ` (digest). -/
structure OracleSpec where
  Domain : Type
  Range  : Type
  [decEqDomain : DecidableEq Domain]
  [fintypeRange : Fintype Range]
  [inhabitedRange : Inhabited Range]

attribute [instance] OracleSpec.decEqDomain
attribute [instance] OracleSpec.fintypeRange
attribute [instance] OracleSpec.inhabitedRange

/-- The query log: an ordered list of `(query, response)` pairs the
    oracle has produced so far. Newer entries near the head. Acts as the
    cache for lazy sampling. -/
def QueryLog (spec : OracleSpec) : Type := List (spec.Domain × spec.Range)

namespace QueryLog
variable {spec : OracleSpec}

/-- The empty log. -/
def empty : QueryLog spec := ([] : List _)

instance : Inhabited (QueryLog spec) := ⟨QueryLog.empty⟩

/-- Look up a query's cached response, if any. -/
def lookup (log : QueryLog spec) (d : spec.Domain) : Option spec.Range :=
  (log.find? (fun p => p.fst = d)).map Prod.snd

/-- Append a fresh `(d, r)` pair to the log. -/
def append (log : QueryLog spec) (d : spec.Domain) (r : spec.Range) :
    QueryLog spec := (d, r) :: log

/-- Number of queries logged (with repeats; the lazy-sampler dedupes
    operationally via `lookup`). -/
def length (log : QueryLog spec) : Nat := List.length log

@[simp] theorem lookup_empty (d : spec.Domain) :
    (QueryLog.empty : QueryLog spec).lookup d = none := rfl

@[simp] theorem length_empty :
    (QueryLog.empty : QueryLog spec).length = 0 := rfl

@[simp] theorem length_append (log : QueryLog spec)
    (d : spec.Domain) (r : spec.Range) :
    (log.append d r).length = log.length + 1 := by
  simp [QueryLog.append, QueryLog.length]

end QueryLog

/-- A computation with access to the random oracle. Concretely: a
    function taking the starting cache and returning a `PMF` over
    `(value, ending cache)` pairs. -/
def OracleComp (spec : OracleSpec) (α : Type) : Type :=
  QueryLog spec → PMF (α × QueryLog spec)

namespace OracleComp
variable {spec : OracleSpec}

noncomputable instance : Monad (OracleComp spec) where
  pure x := fun log => PMF.pure (x, log)
  bind m f := fun log => (m log).bind fun p => f p.fst p.snd

/-- Query the oracle on `d`. On a novel query, sample a fresh response
    uniformly from `spec.Range` and cache it; on a repeat, return the
    cached response. -/
noncomputable def query (d : spec.Domain) : OracleComp spec spec.Range :=
  fun log =>
    match log.lookup d with
    | some r => PMF.pure (r, log)
    | none =>
        (PMF.uniformOfFintype spec.Range).bind fun r =>
          PMF.pure (r, log.append d r)

/-- Run a computation from the empty log; project the value distribution. -/
noncomputable def simulateQ (c : OracleComp spec α) : PMF α :=
  (c QueryLog.empty).map Prod.fst

/-- Run a computation from a pre-populated log. Used by the equivocation
    simulator: pre-populate the log to *program* the oracle at chosen
    points, then sample freshly elsewhere. -/
noncomputable def simulateQFrom (c : OracleComp spec α) (log : QueryLog spec) :
    PMF α :=
  (c log).map Prod.fst

end OracleComp

/-- The lazy-sampled random oracle. An alias to make the API name match
    VCVio's `randomOracle`. -/
@[inline, reducible]
noncomputable def randomOracle {spec : OracleSpec} :
    spec.Domain → OracleComp spec spec.Range :=
  OracleComp.query
