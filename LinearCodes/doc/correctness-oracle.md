# Correctness-oracle status of `LinearCodes`

Quick reference for the verification picture of the Reed-Solomon
implementation in this library — what's runnable, what's verified, and
what would be needed to make it a *verified* correctness oracle in the
same epistemic sense as `Sumcheck.Src.Transcript.generateHonestTranscript`
(which has `perfect_completeness` + `soundness_dishonest` formally
attached).

## Current state (2026-05-05)

| Layer | Status |
|---|---|
| `reedSolomonEncode` (Horner-loop polynomial evaluation on a domain) | **Computable** ✅ |
| `LinearCode` typeclass methods (`messageLen`, `codeLen`, `minimumDistance`, `johnsonRadius`, `mcaProximityGapError`) | **Computable** ✅ |
| Derived helpers (`rate`, `uniqueDecodingRadius`) | **Computable** ✅ |
| `encode_size`, `encode_add`, `encode_smul` (encoder linearity) | **Proved** ✅ |
| `encode_min_distance`, `encode_injective`, `johnson_list_decoding_radius` | **Proved** ✅ |
| `mca_correlated_agreement` (case-(a) form, Johnson regime) | **Proved** ✅ |
| Bridge to Mathlib's `Polynomial.eval` (`reedSolomonEncode_eq_polynomial_eval`) | **Proved** ✅ |

**Zero sorries.** The encoder is computable, machine-verified to agree
with Mathlib's canonical polynomial-evaluation, and all seven property
theorems are closed.

### Note on the MCA theorem shape

The `mca_correlated_agreement` theorem is in **case-(a) form**: it
assumes directly that *every* `α ∈ 𝔽` gives a δ-close combination, and
concludes mutual correlated agreement (shared support, possibly
different witness codewords per `fᵢ`). The proof uses
`2^(domain size)` pigeonhole on the supports + Lagrange interpolation,
requiring the field-size hypothesis `|𝔽| > (l + 1) · 2^n`.

The published BCGM25 quantitative form bounds the *number of bad
seeds* by `O((l+1) · n²)` via a Guruswami-Sudan polynomial
construction — machinery (rational function fields, GS interpolation)
that is not yet in Mathlib. Our case-(a) form is the structural
implication that downstream protocols invoke; the BCGM25 quantitative
threshold is treated as an external runtime check, not a Lean theorem.

For practical RS instances with `n ≤ 60` and Goldilocks-class fields
(`|𝔽| ≈ 2^64`), our `(l+1)·2^n` field-size requirement is satisfied
comfortably.

## What "FFT" is and isn't here

The encoder uses **Horner's method**, point by point on the explicit
domain — `O(n · k)`, no FFT. The Rust ark-codes encoder uses arkworks'
`GeneralEvaluationDomain.fft` for `O(n log n)`. Both compute the same
polynomial-evaluation function, just at different speeds. An FFT-backed
Lean encoder (matching the Rust one for benchmarking) is a separate
~1-week add and is not currently in the tree.

## Two tiers of properties

The seven stubs in `ReedSolomonProperties.lean` split cleanly into two
categories with very different stakes for a correctness-oracle claim:

### Tier 1 — encoder correctness

Properties that say "this implementation correctly computes RS
encoding." These are what a correctness-oracle claim actually rests on.

| # | Theorem | Status | Effort | Notes |
|---|---|---|---|---|
| — | **Bridge: `reedSolomonEncode = Polynomial.eval ∘ ofCoeffs`** | Not written | 1–2 days | Optional now that 1–3 are proved without it |
| 1 | `encode_size` | ✅ Proved | — | `Array.size_map` |
| 2 | `encode_add` | ✅ Proved | — | List-foldr induction + `Array.zipWith_map` + `Array.zipWith_self` |
| 3 | `encode_smul` | ✅ Proved | — | List-foldr induction + `Array.map_map` |
| 5 | `encode_injective` | Stubbed | ~few hours | Corollary of (4) |

**Cumulative effort to close Tier 1: ~3–5 days.** Closing this tier
turns the encoder into a verified correctness oracle in the same sense
as `generateHonestTranscript`: any Rust encoder that matches Lean's
output on the same inputs inherits the guarantee "computes polynomial
evaluation," which **is** the spec of an RS encoder.

### Tier 2 — code-level properties

Properties that say things about the *set of codewords* — they're
consumed by **protocol** soundness analyses (FRI, STIR, WHIR), not by
encoder correctness.

| # | Theorem | Effort | Notes |
|---|---|---|---|
| 4 | `encode_min_distance` (Singleton MDS) | 2–3 days | Distinct codewords differ in ≥ n−k+1 positions |
| 6 | `johnson_list_decoding_radius` | ~1 week | List of codewords inside Johnson radius is finite |
| 7 | `mca_correlated_agreement` | 2–3 weeks | BCIKS18 proximity gap. Research-level formalisation |

**Tier 2 is decoupled from "encoder correctness oracle" status.**
The encoder being formally correct doesn't depend on any of these.
Protocols built on RS *do* depend on them — so Tier 2 effort is
amortised against whichever downstream protocol you formalise first.

The big asymmetry: theorem 7 (BCIKS18) alone is over half the total
proof effort across all seven stubs, and it's the technical heart of
all proximity-test protocols. No one has formalised it yet; doing so
would be a real contribution.

## Recommended path

If/when the Rust encoder needs to claim "verified reference":

1. **Day 1–2**: write the bridge theorem connecting `reedSolomonEncode`
   to `Mathlib.Polynomial.eval`. This is the keystone.
2. **Day 3–5**: close stubs 1, 2, 3, 5 as Mathlib corollaries via the
   bridge.
3. **Stop here for "verified correctness oracle" status.** The
   encoder is now a verified reference in the same sense as
   `generateHonestTranscript`.
4. (Optional, when downstream protocols need it) Tier 2 work — start
   with the easiest (theorem 4), keep theorem 7 as a long-term goal.

## Security-profiling primitives

For STIR/WHIR/(future)WARP security analyses, the key inputs are:

* `LinearCode.minimumDistance c` — `ℕ`
* `LinearCode.johnsonRadius c` — `ℕ`
* `LinearCode.mcaProximityGapError c regime l δ q` — `ℚ`
* `LinearCodes.rate c` — `ℚ` (derived: `k/n`)
* `LinearCodes.uniqueDecodingRadius c` — `ℕ` (derived: `⌊(d−1)/2⌋`)

All five are **runnable**. A profiler calls them on a concrete config
and chains the results through whatever per-protocol soundness formula
it needs.

### The `regime` parameter on `mcaProximityGapError`

WHIR and STIR both report soundness in two modes:

* **`ProximityRegime.proven`** — uses the Johnson-regime bound (`δ < 1 − √ρ`).
  Backed by BCIKS18 et al. Solid pen-and-paper math; trusted under peer
  review.
* **`ProximityRegime.conjectured`** — uses the capacity-regime bound
  (`δ → 1 − ρ`). Tighter — so higher bit-security at the same protocol
  parameters — but relies on the **capacity-achieving proximity-gap
  conjecture**, which is unproved even at the paper level. Standard
  practice in the field; protocol authors report both numbers and
  practitioners pick based on risk tolerance.

The `mcaProximityGapError` typeclass method takes a `regime` argument so
profilers can compute either or both. Closing `sorry` #7
(`mca_correlated_agreement`) would formalise the *proven* mode; the
*conjectured* mode requires resolving the underlying conjecture, not
just formalisation.

### Epistemic chain

| Number | Backing today |
|---|---|
| Proven mode bit-security | Trust BCIKS18-class papers (peer-reviewed) |
| Conjectured mode bit-security | Trust the capacity-achieving proximity-gap conjecture (unproved) |

Closing the four sorries would *not* affect conjectured-mode security
(which is downstream of an open math conjecture, not formalisation
work). It would upgrade proven-mode security from "trust the paper" to
"machine-checked."
