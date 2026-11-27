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

## Correspondence with the Agda development

[`agda-sumcheck`](https://github.com/verify-right/agda-sumcheck) (Agda,
stdlib, `--safe --without-K`) proves the same transcript-level statements
for a circuit-polynomial verifier over commutative rings.

| Lean (this repo) | Agda (`src/`) |
|---|---|
| `BarycentricDomain` (CompPoly): distinct nodes, `weights_spec` | `Circuit.Barycentric.NodeSet`: `Certified x w = ∀ i → w i * ∏_{j≠i}(x i - x j) ≈ 1` (`Ring.Lagrange`) |
| `BarycentricDomain.eval` (second form, node branch, one division) | `Circuit.Barycentric.evalAt` (first form, prefix–suffix products, division-free) |
| `eval_eq_interpolate_eval` (CompPoly) | `evalAt-correct`, `lagrange-node` |
| `Lagrange.eq_interpolate` (Mathlib, field) | `Ring.LagrangeInverse.eval-injective`, `coefficient-evaluation` (`Inverse`, commutative ring with unit differences) |
| `tupleOf?` | `Circuit.Barycentric.exactly`, `Circuit.General.parse` |
| `RoundNodes`, `isEvalVerifierAccepts` | per-round `Config` list, `Circuit.General.evVerify` |
| `isEvalVerifierAccepts_eq_of_rounds` | `Circuit.General.symRun-cong` |
| `isEvalVerifierAccepts_eq_decode` | `verify-representation` (well-formed) plus `malformed-rejected` |
| `evalMessage_encodeMessage`, `isVerifierAccepts_eq_encode` | `Circuit.Reconstruction.reconstruction`, `encode-verify-equivalent` |
| `honest_eval_accepts_on_challenges_k` | `Circuit.GeneralCompleteness.evaluation-form-complete` |
| `residualSum`, stop round `k` | `Circuit.General.residual`, `residual-sum` |

Differences:

- **Scalars.** Lean needs a field: `BarycentricDomain` stores inverses,
  and `isVerifierAccepts` assumes `[Field 𝔽] [Fintype 𝔽]`. The Agda proofs
  need only a commutative ring whose node differences are units, so they
  cover `ℤ/15` with suitable nodes.
- **Degree check.** Lean's symbolic verifier checks the exact `degreeOf`
  of a `CMvPolynomial`. The Agda circuit verifier checks a conservative
  occurrence count, so its decoding builds a sum of single basis terms to
  pass that check.
- **Malformed messages.** Both developments prove a separate rejection
  lemma for them. Lean states a single equation for all transcripts by
  decoding a malformed list to `X^(d+1)`. Agda states equality on parsed
  transcripts only.
- **Equality.** Lean uses propositional equality; Agda uses setoid
  equality.
- **Evaluator.** The two use different barycentric evaluators (second and
  first form). Each is proved equal to Lagrange interpolation, so the
  transcript theorems do not depend on the choice.

## Limitations

- Fields only; no composite moduli.
- Nodes are supplied by the caller. The tests build natural nodes `0..d`
  in `ZMod 17` (valid for `d < 17`) and shifted nodes `3, 5, 7`. No
  general node constructor for `ZMod p` is provided.
- Operation counts per round: O(d) per evaluation, so O(|domain| · d) for
  the domain sum. Weight construction (`BarycentricDomain.mk'`) costs
  O(d²) and is done once per node set. These are field-operation counts,
  not bit complexity or measured run time. No benchmarks.
- When the domain is contained in the nodes, the domain sum still goes
  through `eval`; there is no specialised indexed-lookup path.
- `tupleOf?` copies the list into an array in O(|ys|) time
  (O(d+1) for well-formed messages), enabling O(1) indexed lookups. The round check parses the list once for the whole domain sum. The
  claim at the challenge parses it again, each time the claim is
  read.
- No soundness theorem is stated for the evaluation-form verifier.
  Transferring `sumcheck_hasSoundnessError` through
  `isEvalVerifierAccepts_eq_decode` would need an adversary translation;
  that is not done here.
