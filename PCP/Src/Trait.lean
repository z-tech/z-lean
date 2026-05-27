/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Mathlib.Data.ENNReal.Basic

/-!
# `PCPSystem` — abstract typeclass for probabilistically checkable proofs

This typeclass abstracts the interface to a PCP for a relation `R`.
Mirrors the shape of `VectorCommitment` in
[`VectorCommitment/Src/Trait.lean`](../../VectorCommitment/Src/Trait.lean):
typed associated members, model-neutral, no probabilistic content in
the class itself.

Higher-level constructions (Kilian's protocol, the BCS transform) bind
on `[PCPSystem P]` to access the PCP's statement / alphabet / proof
length / query complexity / soundness error abstractly.

## References

* S. Arora, S. Safra, *Probabilistic checking of proofs*, JACM 1998.
* A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash
  Functions*, §17 (PCP definitions).
* A. Chiesa, M. Dall'Agnol, Z. Guan, N. Spooner, E. Yogev,
  *Untangling the Security of Kilian's Protocol*,
  [eprint 2024/1434](https://eprint.iacr.org/2024/1434), §2–3.
-/

/-- A probabilistically-checkable proof system. Carries the types of
    statements / witnesses / proof alphabet / verifier randomness, plus
    the honest prover, the verifier's query and decision functions, and
    the soundness error.

    `P` is the "scheme handle" — a type-level token that allows
    multiple PCP systems for the same relation to coexist. -/
class PCPSystem (P : Type) where
  /-- Statement type (input to the PCP — e.g. SAT formulas, R1CS instances). -/
  Statement : Type
  /-- Witness type for the honest prover. -/
  Witness : Type
  /-- The PCP proof-string alphabet. Typically `Bool`, a field, or
      a small finite type. -/
  Alphabet : Type
  /-- The verifier's randomness space. -/
  Randomness : Type
  /-- Length of the PCP proof string as a function of statement size `n`. -/
  proofLength : ℕ → ℕ
  /-- Number of queries the verifier makes, as a function of `n`. -/
  queryComplexity : ℕ → ℕ
  /-- The honest prover: given statement and witness, output the PCP
      string. Length should equal `proofLength n` for an honestly-formed
      input; this is not enforced at the typeclass level. -/
  honestProver : Statement → Witness → List Alphabet
  /-- The verifier's query function: given the statement and its random
      tape, list the indices of the PCP it will probe. Length should
      equal `queryComplexity n`. -/
  verifierQueries : Statement → Randomness → List ℕ
  /-- The verifier's decision function: given the statement, its
      randomness, and the queried responses, accept or reject. -/
  verifierDecide : Statement → Randomness → List Alphabet → Bool
  /-- Soundness error: an upper bound on the probability that the
      verifier accepts a false statement, over a fixed PCP string and
      uniform randomness. -/
  soundnessError : ℕ → ENNReal
