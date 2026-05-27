/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import Kilian.Src.Construction

/-!
# Kilian's protocol — honest prover and verifier

Concrete data definitions for the honest prover and the verifier, on
top of the `Transcript` data type from
[`Construction.lean`](Construction.lean).

The honest prover:
1. Computes the PCP string via `PCPSystem.honestProver x w`.
2. Commits to it via `VectorCommitment.commit`.
3. Receives randomness `ρ` as message-2.
4. Queries positions via `PCPSystem.verifierQueries x ρ`, reads off the
   values, opens via `VectorCommitment.open`.

The verifier:
* Re-derives the queried positions from `(x, ρ)`.
* Checks every opening with `VectorCommitment.check`.
* Runs the PCP verifier's decision function on the opened values.

Both are pure data — no probabilistic content, no sorries.
-/

namespace Kilian

open KilianCompatible

variable {P V : Type} [PCPSystem P] [VectorCommitment V] [KilianCompatible P V]

/-- The honest Kilian prover. Given the statement, witness, committer
    key, and verifier's randomness, produce a transcript. -/
noncomputable def honestProver
    (x : PCPSystem.Statement P) (w : PCPSystem.Witness P)
    (ck : VectorCommitment.CommitterKey V) (ρ : PCPSystem.Randomness P) :
    Transcript P V :=
  let pcp_P : List (PCPSystem.Alphabet P) := PCPSystem.honestProver (P := P) x w
  let pcp_V : List (VectorCommitment.Alphabet V) :=
    KilianCompatible.castAlphabet (P := P) (V := V) pcp_P
  let commit_result := VectorCommitment.commit (V := V) ck pcp_V
  let commitment := commit_result.fst
  let state := commit_result.snd
  let queries : List ℕ := PCPSystem.verifierQueries (P := P) x ρ
  let queries_V : List (VectorCommitment.Index V) :=
    KilianCompatible.castIndex (P := P) (V := V) queries
  let values_V : List (VectorCommitment.Alphabet V) :=
    queries.filterMap (fun i => pcp_V[i]?)
  let values_P : List (PCPSystem.Alphabet P) :=
    KilianCompatible.uncastAlphabet (P := P) (V := V) values_V
  let proof : VectorCommitment.Proof V :=
    VectorCommitment.«open» (V := V) ck pcp_V commitment queries_V values_V state
  { commitment := commitment,
    randomness := ρ,
    values := values_P,
    proof := proof }

/-- The Kilian verifier. Accepts iff (a) every opening verifies under
    `VectorCommitment.check` and (b) the PCP verifier's decision
    function accepts on the opened values. -/
noncomputable def verifyTranscript
    (x : PCPSystem.Statement P) (vk : VectorCommitment.VerifierKey V)
    (t : Transcript P V) : Bool :=
  let queries : List ℕ := PCPSystem.verifierQueries (P := P) x t.randomness
  let queries_V : List (VectorCommitment.Index V) :=
    KilianCompatible.castIndex (P := P) (V := V) queries
  let values_V : List (VectorCommitment.Alphabet V) :=
    KilianCompatible.castAlphabet (P := P) (V := V) t.values
  let vc_ok : Bool :=
    VectorCommitment.check (V := V) vk t.commitment queries_V values_V t.proof
  let pcp_ok : Bool :=
    PCPSystem.verifierDecide (P := P) x t.randomness t.values
  vc_ok && pcp_ok

end Kilian
