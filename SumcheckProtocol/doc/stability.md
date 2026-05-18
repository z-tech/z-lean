# SumcheckProtocol — Stability Tiers

The `SumcheckProtocol/` tree is in active development. Tiers below
describe what downstream consumers should expect.

## Stable (safe to depend on)

Breaking changes will be called out in PR descriptions and the
CHANGELOG.

- **Symbolic protocol** — the canonical sumcheck protocol over
  `CPoly.CMvPolynomial`:
  - [`Src/Prover.lean`](../Src/Prover.lean) — `honestProverMessageAt`,
    `sumcheckHonestProver`
  - [`Src/Verifier.lean`](../Src/Verifier.lean) — `verifierCheck`,
    `isVerifierAccepts`
  - [`Src/Transcript.lean`](../Src/Transcript.lean) —
    `Transcript`, `nextClaim`, `generateHonestTranscript`
  - [`IP/Statement.lean`](../IP/Statement.lean) —
    `SumcheckProtocolStatement`, `sumcheckClaimIsCorrect`,
    `sumcheckProtocol`
- **Theorems** on the symbolic protocol:
  - `perfect_completeness`
    ([`Properties/Theorems/Completeness.lean`](../Properties/Theorems/Completeness.lean))
  - `sumcheck_hasSoundnessError`
    ([`Properties/Theorems/Soundness.lean`](../Properties/Theorems/Soundness.lean))
- **Inner-product sumcheck** ([`IP/InnerProduct.lean`](../IP/InnerProduct.lean)):
  `InnerProductStatement`, `toSumcheck` reduction,
  completeness/soundness, the multilinear `n · 2 / |𝔽|` corollary.
- **#SAT ∈ IP** ([`IP/SharpSAT/`](../IP/SharpSAT/)):
  arithmetization, `honestClaim_arithmetize_eq_numSatisfying`,
  `sharpSAT_inIPFamily_concrete`.

## Recently landed (may evolve)

Public names unlikely to change but locations / signatures may.

- **VSBW eval-table prover** for multilinears
  ([`Src/MultilinearProver.lean`](../Src/MultilinearProver.lean) +
  [`Properties/MultilinearProver.lean`](../Properties/MultilinearProver.lean) +
  [`Properties/MultilinearProverBridge.lean`](../Properties/MultilinearProverBridge.lean)).
  Bridge to the symbolic spec proven at **round 0**; the inductive
  step over all `n` rounds (`multi_round_correctness`) is open.
- **MSB / LSB convention layer** ([`Src/Convention.lean`](../Src/Convention.lean)).
  Council direction: collapse to **MSB-only**; LSB wrappers will be
  removed.
- **Coefficient prover scaffold** ([`IP/CoefficientProver.lean`](../IP/CoefficientProver.lean) +
  [`Src/RoundEvaluator.lean`](../Src/RoundEvaluator.lean)). The
  `RoundPolyEvaluator` structure is stable; the operational `respond`
  still routes through symbolic `eval₂Poly` — performance work pending.
- **Partial-run sumcheck** (P1 roadmap): a `k : Fin (n+1)` stop
  parameter is planned; the symbolic protocol will gain this as a
  generalization rather than a separate variant.

## Partial — known incomplete

Things proven against a weaker spec than their headline name suggests.
Do not rely on these for downstream proofs without reading the
docstring carefully.

- `compute_correctness_table`
  ([`Properties/MultilinearProver.lean`](../Properties/MultilinearProver.lean#L153)) —
  table-internal, doesn't bridge to `honestProverMessageEvalsAt`.
- `fold_msb_succ_lerp_form`
  ([`Properties/MultilinearProver.lean`](../Properties/MultilinearProver.lean#L194)) —
  algebraic invariant only; full `fold_correctness` deferred pending
  `eval_substRound0` (upstream CompPoly PR planned).
- `multilinearProverEvalForm_length_and_head`
  ([`Properties/MultilinearProver.lean`](../Properties/MultilinearProver.lean#L224)) —
  proves length + first round message only, NOT full transcript
  equivalence.
- `eval_substRound0` / `eval_substRound0_multilinear`
  ([`Src/SubstRound0.lean`](../Src/SubstRound0.lean#L80)) — parked
  pending CompPoly upstream.
- Eval-form soundness lift
  ([`IP/InnerProductNative.lean`](../IP/InnerProductNative.lean#L288)) —
  native-side deferred.

## Removed: noncomputable eval-form IP wrapper

The previously-shipped eval-form IP wrapper (`Src/EvalFormVerifier.lean`,
`IP/EvalForm.lean`, `IP/CoefficientProver.lean`, `IP/InnerProductNative.lean`,
`Properties/EvalForm.lean`) routed its round-polynomial check through
`Lagrange.interpolate` from Mathlib, which is `noncomputable`. The whole
point of the eval-form was *efficiency relative to the symbolic protocol*,
and a noncomputable "efficient" path is self-defeating — correctness is
already established by the symbolic protocol. These files were **deleted**
in the P0 council fallout commit.

The eval-form *prover* (`Src/EvalForm.lean::honestProverMessageEvalsAt`)
remains and is computable; it's the prover-side evaluation tuple used by
the VSBW multilinear prover. To resurrect a verifier that consumes this
output, the next implementer should:

1. Define a computable `evalAt evalPoints qEvals challenge` using an
   explicit barycentric formula on scalars (no `Polynomial 𝔽` infra).
2. Restate the verifier acceptance predicate in terms of `evalAt`.
3. (Optional) Prove `evalAt = (Lagrange.interpolate ...).eval challenge`
   if existing proofs are to be ported.

The old code is recoverable from git history if anyone takes this on.

## Out of scope (for now)

- **Fiat–Shamir / NIZK soundness.** The placeholder
  `InteractiveProtocol/Properties/FiatShamir.lean` (a `True := by
  sorry` stub) has been **deleted**. A ROM-model formalization is a
  multi-month investment and is not currently planned. If you need
  Fiat–Shamir, fork the Arc III scaffold from pre-`4336abd` history.
- **Batched sumcheck**, **zero-knowledge sumcheck**, **small-field
  sumcheck** (BCKL24-style), **polynomial-commitment oracle final-query
  verifier**: all P2 features; not started.

## How to read theorem statements

If a name ends in `_uniform`, `_partial`, `_at_zero`, or appears in
the "Partial" tier above, read the docstring carefully — the
statement is honestly proven but **narrower** than the name might
suggest. The maintainer's policy is to push the qualifier into the
first line of the docstring; if you find one that doesn't, please
file an issue.
