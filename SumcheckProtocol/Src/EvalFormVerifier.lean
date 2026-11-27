import CompPoly.Univariate.Barycentric
import SumcheckProtocol.Src.Verifier

/-!
# Computable evaluation-form verifier

A sumcheck verifier whose round messages are lists of field values: the
round polynomial's values at the `d + 1` nodes of a
`CompPoly.CPolynomial.CLagrange.BarycentricDomain`, where `d` is the
round's individual degree bound `indDegreeK p i`. This is the verifier
requested in [`doc/stability.md`](../doc/stability.md) ("Removed:
noncomputable eval-form IP wrapper"): the interpolant is evaluated with
CompPoly's computable barycentric evaluator `BarycentricDomain.eval`
(compiled through its `@[csimp]` single-division form `evalFast`), and no
polynomial is constructed from the received values.

Interface, matching `isVerifierAccepts`:

* arbitrary verifier domain (a list; order and multiplicity are kept),
* per-round degree bounds `indDegreeK p i`,
* partial runs `k : Fin (n + 1)` with the final residual-sum check.

Round messages are external `List 𝔽` values. A list whose length is not
`indDegreeK p i + 1` is rejected at the boundary (`tupleOf?`).

Node sets are supplied by the caller as `RoundNodes`, one certified
domain per round; `BarycentricDomain.weights_spec` ties the stored weights
to the nodes, independently of the prover.

The equivalence with the symbolic verifier is proved in
`SumcheckProtocol/Properties/EvalFormVerifier.lean`.
-/

open CompPoly.CPolynomial.CLagrange (BarycentricDomain)

/-- Per-round node sets: round `i` with degree bound `deg i` uses a
certified barycentric domain of `deg i + 1` nodes. Rounds may use different
nodes even at equal degree. (A single degree-indexed family cannot exist
over a finite field, since `d + 1` distinct nodes need `d < |𝔽|`.) -/
abbrev RoundNodes (𝔽 : Type*) [Field 𝔽] [DecidableEq 𝔽] {n : ℕ} (deg : Fin n → ℕ) : Type _ :=
  (i : Fin n) → BarycentricDomain 𝔽 (deg i + 1)

/-- An evaluation-form transcript: the received value lists (one per
round, of arbitrary length) and the verifier's challenges. -/
structure EvalTranscript (𝔽 : Type*) (n : ℕ) where
  roundEvals : Fin n → List 𝔽
  challenges : Fin n → 𝔽

section

variable {𝔽 : Type*} [Field 𝔽] [DecidableEq 𝔽]

/-- Boundary parser: a list of exactly `d + 1` values, as a length-indexed
tuple. Conversion to an array takes O(ys.length) time
(O(d+1) for well-formed messages), with O(1) indexed lookups. -/
def tupleOf? (d : ℕ) (ys : List 𝔽) : Option (Fin (d + 1) → 𝔽) :=
  let a := ys.toArray
  if h : a.size = d + 1 then
    some (fun j => a[j.val]'(by rw [h]; exact j.isLt))
  else
    none

/-- The value at `r` of the round polynomial described by `ys`: the
barycentric interpolant of `ys` on the nodes of `D`. Malformed lists have
value `0`; the verifier rejects them before this value matters. -/
def evalMessage {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1)) (ys : List 𝔽) (r : 𝔽) : 𝔽 :=
  match tupleOf? d ys with
  | some y => D.eval y r
  | none => 0

/-- Evaluation-form counterpart of `verifierCheck`: the list is well formed
and the interpolant sums to the round claim over `domain`. The degree check
of `verifierCheck` is replaced by the length check: `d + 1` values
determine an interpolant of degree at most `d`. The list is parsed once
for the whole domain sum. -/
def evalVerifierCheck {d : ℕ}
    (domain : List 𝔽) (D : BarycentricDomain 𝔽 (d + 1))
    (roundClaim : 𝔽) (ys : List 𝔽) : Bool :=
  match tupleOf? d ys with
  | some y => decide (domain.foldl (fun acc a => acc + D.eval y a) 0 = roundClaim)
  | none => false

/-- Round claims of an evaluation-form transcript:
`claims 0 = initialClaim` and `claims (i + 1)` is round `i`'s interpolant
at challenge `i`, with `deg i` the degree bound of round `i`. -/
def EvalTranscript.claims {n : ℕ} (t : EvalTranscript 𝔽 n)
    (deg : Fin n → ℕ) (nodes : RoundNodes 𝔽 deg) (initialClaim : 𝔽) : Fin (n + 1) → 𝔽
  | ⟨0, _⟩ => initialClaim
  | ⟨j + 1, hj⟩ =>
      let i : Fin n := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      evalMessage (nodes i) (t.roundEvals i) (t.challenges i)

/-- Degree bound of round `i` in a run of `k` rounds on `p`: the individual
degree `indDegreeK p i`, as in `isVerifierAccepts`. -/
def roundDegree {n : ℕ} (p : CPoly.CMvPolynomial n 𝔽)
    (k : Fin (n + 1)) (i : Fin k.val) : ℕ :=
  indDegreeK p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩

/-- Evaluation-form counterpart of `isVerifierAccepts`, with the same stop
round `k`, domain, polynomial, initial claim and final residual check. -/
def isEvalVerifierAccepts
    {n : ℕ}
    (k : Fin (n + 1))
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (nodes : RoundNodes 𝔽 (roundDegree p k))
    (initialClaim : 𝔽)
    (t : EvalTranscript 𝔽 k.val) : Bool :=
  let deg := roundDegree p k
  let claims := t.claims deg nodes initialClaim
  have hk_le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  let roundsOk : Bool :=
    (List.finRange k.val).all (fun i : Fin k.val =>
      evalVerifierCheck domain (nodes i) (claims (Fin.castSucc i)) (t.roundEvals i)
      &&
      decide (claims i.succ = evalMessage (nodes i) (t.roundEvals i) (t.challenges i)))
  let finalOk : Bool :=
    decide (claims (Fin.last k.val) = residualSum (𝔽 := 𝔽) domain t.challenges p hk_le)
  roundsOk && finalOk

/-- Encode a symbolic round polynomial by its values at the nodes of `D`
(the honest evaluation-form message). -/
def encodeMessage {d : ℕ} (D : BarycentricDomain 𝔽 (d + 1))
    (q : CPoly.CMvPolynomial 1 𝔽) : List 𝔽 :=
  List.ofFn fun j => CPoly.CMvPolynomial.eval (fun _ => D.nodes j) q

/-- Encode a symbolic transcript, round by round, with degree bounds `deg`. -/
def Transcript.encode {n : ℕ} (t : Transcript 𝔽 n) (deg : Fin n → ℕ)
    (nodes : RoundNodes 𝔽 deg) : EvalTranscript 𝔽 n where
  roundEvals i := encodeMessage (nodes i) (t.roundPolys i)
  challenges := t.challenges

end
