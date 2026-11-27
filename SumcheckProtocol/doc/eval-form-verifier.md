# Evaluation-form verifier

A computable sumcheck verifier whose round messages are the round
polynomial's values at `d + 1` nodes, with `d = indDegreeK p i`, proved
equivalent to the symbolic verifier `isVerifierAccepts`.

- Definitions: [`Src/EvalFormVerifier.lean`](../Src/EvalFormVerifier.lean)
- Proofs: [`Properties/EvalFormVerifier.lean`](../Properties/EvalFormVerifier.lean)
- Tests: [`Tests/EvalFormVerifierTests.lean`](../Tests/EvalFormVerifierTests.lean)

## Verifier

Round `i` receives a list `ys : List 𝔽` and uses a
`BarycentricDomain 𝔽 (d + 1)` from CompPoly: distinct nodes `x_j` and
stored weights `w_j = ∏_{l ≠ j} (x_j - x_l)⁻¹`, tied to the nodes by the
field `weights_spec`. The verifier

1. rejects `ys` unless `ys.length = d + 1` (`tupleOf?`);
2. checks `Σ_{a ∈ domain} q(a) = claim_i`, keeping the domain list's order
   and multiplicity;
3. sets `claim_{i+1} = q(r_i)`;
4. after `k` rounds, checks the last claim against
   `residualSum domain r p`, as `isVerifierAccepts` does.

Here `q(z)` is `BarycentricDomain.eval y z`, the second barycentric form
with an explicit node branch (DLMF §3.3(i); Berrut–Trefethen 2004).
CompPoly compiles it via `@[csimp] eval_eq_evalFast` to a single-division
fold, so each evaluation costs O(d) field operations and one inversion.
The verifier builds no polynomial from the received values.

Node sets are per round (`RoundNodes`). A single family of node sets for
every degree cannot exist over a finite field, because `d + 1` distinct
nodes require `d < |𝔽|`.

## Results

For every stop round `k : Fin (n + 1)`, domain list, polynomial `p`,
round nodes and initial claim:

| Theorem | Statement |
|---|---|
| `isEvalVerifierAccepts_eq_decode` | for **every** `t : EvalTranscript 𝔽 k` (any values, any list lengths), `isEvalVerifierAccepts … t = isVerifierAccepts … (t.decode …)` |
| `isVerifierAccepts_eq_encode` | if every round polynomial of `t : Transcript 𝔽 k` satisfies `degreeOf 0 ≤ indDegreeK p i`, then `isVerifierAccepts … t = isEvalVerifierAccepts … (t.encode …)` |
| `isEvalVerifierAccepts_encode_of_accepts` | symbolic acceptance of `t` implies evaluation-form acceptance of `t.encode` |
| `honest_eval_accepts_on_challenges_k` | the honest prover's node values are accepted for every challenge vector |
| `isEvalVerifierAccepts_eq_of_rounds` | the simulation lemma behind the three above |
| `isEvalVerifierAccepts_eq_false_of_malformed`, `isVerifierAccepts_eq_false_of_round` | a round failing its check for every claim (in particular a malformed list) makes the verifier reject |

How the proofs work:

- **Decoding.** A well-formed list decodes to its Lagrange interpolant,
  which has `degreeOf 0 ≤ d` (`Lagrange.degree_interpolate_lt`). The
  interpolant agrees with `BarycentricDomain.eval` everywhere
  (`eval_eq_interpolate_eval`, CompPoly).
- **Malformed lists.** A malformed list decodes to `X^(d+1)`, which the
  symbolic degree check rejects. The proof splits into two cases. If
  every list is well formed, the simulation lemma applies. Otherwise both
  verifiers reject by the two rejection lemmas. Decoding round `i` reads
  only round `i`'s list, not its challenge, so `t.decode` is causal: an
  evaluation-form prover's message function, composed with decoding, is a
  symbolic prover's message function. Turning that into a soundness
  transfer is not done here.
- **Encoding.** The encoding direction uses uniqueness of the interpolant
  (`Lagrange.eq_interpolate`). The degree hypothesis is necessary: a
  degree-2 message in a degree-1 round is rejected symbolically, yet its
  two node values are accepted (`Tests/EvalFormVerifierTests.lean`,
  `Example1.overDegree`).
- **Simulation.** Round `i + 1`'s claim depends only on round `i`'s message
  and challenge. So the simulation lemma needs only per-round agreement:
  equal round verdicts for every claim, and equal values at the challenge.

One-variable `CMvPolynomial`s are moved to Mathlib's `Polynomial` through
`CPoly.fromCMvPolynomial` and `MvPolynomial.uniqueAlgEquiv`. Under that
map, `degreeOf 0` is `natDegree` (`degreeOf_eq_natDegree_uniqueAlgEquiv`).
The decoding functions are `noncomputable` and appear only in theorem
statements.

The Mathlib results used are `eval_interpolate_at_node`,
`degree_interpolate_lt` and `eq_interpolate` in
`Mathlib/LinearAlgebra/Lagrange.lean`. The CompPoly results are in
`CompPoly/Univariate/Barycentric.lean`. This development adds the verifier
interface and the transcript-level theorems.
