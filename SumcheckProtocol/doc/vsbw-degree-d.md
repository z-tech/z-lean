# VSBW Prover at Degree d > 1 — Design Notes

The eval-table VSBW prover in
[`Src/MultilinearProver.lean`](../Src/MultilinearProver.lean) is
multilinear-only by construction. This note sketches what generalizing
to arbitrary individual degree `d ≥ 1` would entail. **No code shipped
yet** — this is a planning artifact so the design is settled before
implementation.

## Why multilinear is special

For multilinear `p` in variable `i`, the partial assignment
`p(.., w, ..)` is a linear blend
`(1 − w) · p(.., 0, ..) + w · p(.., 1, ..)`. The eval-table stores
`p` at every Boolean point; the fold computes the blend pointwise in
`O(2^(n−1))`. Two evaluation points (`0`, `1`) per round suffice for
the verifier to recover the degree-1 round polynomial — hence
`computeS0S1_msb` returns just `(s0, s1) : 𝔽 × 𝔽`.

For degree-`d` `p` in variable `i`, the partial assignment is a
degree-`d` polynomial in `w`. Three changes ripple:

| Layer | Multilinear (today) | Degree d (proposed) |
|---|---|---|
| Round-message type | `𝔽 × 𝔽` | `Fin (d+1) → 𝔽` |
| Round-message comp | `computeS0S1_msb` (sum low / sum high) | `computeEvals_d` — `d+1` partial sums, one per node |
| Verifier interp | Linear interpolation `s0 + (s1 − s0) · c` | Lagrange/barycentric over fixed nodes `0..d` |
| Fold update | `lo + (hi − lo) · w` (linear lerp) | `Σ_j coef_j(w) · t[k + j · stride]` — `d+1`-point Lagrange interpolant in `w` |

## Two viable representations

### Option A — keep `EvalTable n = Vector 𝔽 (2^n)`, generalize fold

Reuse the existing data structure. The fold becomes a `(d+1)`-point
Lagrange interpolant evaluated at the challenge `w`, applied per low/
high block in the table. Cost:

- `toEvalTable` still O(2^n) (just hypercube evals).
- `computeEvals_d`: for each of the `d+1` evaluation nodes
  `e_0, …, e_d ∈ 𝔽`, sum `p`'s evaluation table at the corresponding
  slice. **But** the slice for `e_j` requires evaluating `p` at points
  *outside* the Boolean hypercube when `e_j ∉ {0, 1}` — and the eval
  table only stores Boolean-hypercube values. This kills Option A for
  `d ≥ 2` *unless* `e_j ∈ {0, 1, …}` happens to all be Boolean —
  impossible for `d ≥ 2`.

**Verdict: doesn't work.** The eval-table representation is
fundamentally tied to the Boolean hypercube and only carries enough
information for the multilinear case.

### Option B — coefficient form per round

Materialize the round-`i` univariate polynomial directly as a
`Fin (d+1) → 𝔽` tuple of coefficients (or evaluations at fixed nodes
`0, 1, …, d`). The prover walks the symbolic structure of `p`,
accumulating contributions per round via the coefficient prover
already sketched in [`Src/RoundEvaluator.lean`](../Src/RoundEvaluator.lean).

This is the standard generalization in the cryptography literature
(Thaler Ch. 4.3). Cost:

- Per-round work: `O(2^(n−i) · |p_support| · d)` for the symbolic walk,
  vs `O(2^(n−i))` for VSBW eval-table. The constant `|p_support|`
  bites when `p` is sparse.
- Storage: `O(d+1)` per round message (vs `O(2^(n−i))` table).

The `RoundPolyEvaluator` structure in
[`Src/RoundEvaluator.lean`](../Src/RoundEvaluator.lean) and
[the deleted `IP/CoefficientProver.lean`](https://github.com/z-tech/z-lean/blob/2e007a1~1/SumcheckProtocol/IP/CoefficientProver.lean)
were the scaffold for exactly this. The deletion was about the
noncomputable Lagrange verifier — the `RoundPolyEvaluator` abstraction
itself is sound and would be the right starting point.

### Option C — product structure (Thaler's "phase 2" prover)

For polynomials that factor as a product `f₁ · f₂ · … · f_k` where each
`f_j` is multilinear (the GKR / Hyperplonk case), the round message is
the convolution of multilinear round messages. The prover maintains an
eval table per `f_j` (each `O(2^(n−i))` updates per round), then
combines `(d+1)` evaluations from the convolution structure.

This is what the inner-product `f · g` reduction already does
implicitly. A clean degree-`d` API would expose
`MultilinearProductProver` and `ProductEvalTable n d : Fin (d+1) → Vector 𝔽 (2^n)`.

**Strongest fit** for the existing codebase's use cases (inner product,
GKR-style layered protocols).

## Recommendation

**Two-track build**:

1. **Track 1 — Option B (CoefficientProver) for arbitrary `p`.** Brings
   back the deleted scaffolding with a *computable* verifier (no
   `Lagrange.interpolate`). This is the general-purpose path; degrades
   gracefully to Option A's complexity in the multilinear case but
   pays the symbolic walk cost.

2. **Track 2 — Option C (ProductEvalTable) for product polynomials.**
   Optimized for inner-product / GKR. Keeps VSBW's linear-time
   advantage when `p = ∏ fⱼ` with each `fⱼ` multilinear.

The existing `multilinearProverEvalForm` becomes the `k = 1` special
case of Track 2 (single multilinear factor, `d = 1`).

## Scope estimate

- **Track 1**: 2-3 weeks of focused work. Resurrects ~1500 lines of
  the deleted `CoefficientProver` scaffold + new computable verifier
  (~300 lines barycentric) + correctness proofs against the symbolic
  spec (~500 lines). Conditional on the same upstream CompPoly piece
  as `fold_correctness` (`eval_substAt` and the multilinear extension
  property).

- **Track 2**: 1-2 months. Requires new `ProductEvalTable` data
  structure with per-factor tables; convolution-based round message
  computation; correctness proof reducing to `compute_correctness` per
  factor. The inner-product specialization (already shipped as
  `InnerProduct.toSumcheckProtocol`) is the `k = 2` instance — that's
  the proof-of-concept.

## Dependencies

Both tracks block on:
- `eval_substAt` (CompPoly upstream) — generalizes
  `eval_substRound0` to arbitrary positions, needed when the prover's
  recursion peels variable `i` (not just variable 0).
- A computable barycentric / Lagrange-evaluator at scalars (rolling
  our own; ~50 lines of Mathlib-free arithmetic).

## Not recommended

**Skip** the "generalize Option A by storing non-Boolean evaluations"
direction. The eval-table abstraction breaks for `d ≥ 2`, and patching
it would lose VSBW's `O(2^n)` linear-time property — defeating the
purpose. Use Option B (general-purpose) or Option C (product-optimized)
or both.
