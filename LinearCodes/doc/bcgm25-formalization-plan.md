# Plan: Formalising BCGM25 `mcaProximityGapError`

A planning document for replacing the runtime-only `mcaProximityGapError`
typeclass method with a machine-checked theorem matching the BCGM25 bound
(Bordage, Chiesa, Guan, Manzur — *All Polynomial Generators Preserve
Distance with Mutual Correlated Agreement*, Feb 2026).

This is research-level formalisation. The plan below is honest about the
size: estimates are months, not days, and parts of the work involve
building Mathlib infrastructure that does not yet exist.

## What we're aiming at

BCGM25 Theorem 1 (paraphrased to match our typeclass shape):

> Let `G : S → 𝔽^ℓ` be a polynomial generator with individual degrees
> `(dᵢ)` over domains `(Sᵢ)`. For every linear code `𝒞 ⊆ 𝔽^n` with
> relative distance `δ_𝒞`, and any tradeoff parameter `η ∈ (0,1)`:
> `ε_MCA(γ) ≤ max{n·γ, 1} · Σᵢ dᵢ/|Sᵢ|` if `γ ≤ δ_𝒞 / (max dᵢ + 2)`,
> and `ε_MCA(γ) ≤ O(n/η) · Σᵢ dᵢ/|Sᵢ|` if `γ ≤ 1 − (1 − δ_𝒞 + η)^(1/(max dᵢ + 2))`.

The first branch is the **unique-decoding regime**; the second is the
**list-decoding (Johnson) regime**. They have very different proof
machinery and we plan to attack them in that order.

The downstream payoff is replacing this stub:

```lean
mcaProximityGapError : ProximityRegime → ℕ → ℚ → ℚ → ℚ
```

with a verified bound chained back to a Lean theorem about the actual
probability over the seed space.

## The two-phase split

| Phase | Regime | Core technique | Mathlib infra needed |
|---|---|---|---|
| **A** | Unique-decoding | Corrádi lemma + MDS structure | Linear codes basics, Corrádi |
| **B** | List-decoding (Johnson) | Bivariate Guruswami-Sudan | All of Phase A + GS polynomial method |

Phase A is **a real but bounded project** — combinatorics + linear
algebra, all within current Mathlib's vocabulary. Phase B is **research
formalisation** — it requires building the polynomial method into
Mathlib, which is its own multi-month effort that no one has done yet.

A useful early milestone: Phase A alone lets us replace the `proven`
regime in `mcaProximityGapError` with a verified bound, *but only valid
up to relative distance `δ_𝒞 / 3`*. That's strictly weaker than the
Johnson radius `1 − √ρ` that STIR/WHIR profilers actually use, so Phase A
on its own does not retire the runtime stub — it just provides a verified
*lower-confidence* mode.

## Phase A — Unique-decoding regime

### A.1 — Linear-code algebraic core

We currently have a typeclass `LinearCode` with method-level interface
but no underlying structural theorems. BCGM25 reasons about codes as
`𝔽`-subspaces of `𝔽^n` with parity-check matrices; we need that view.

**New file: `LinearCodes/Algebraic/LinearCodeStruct.lean`**

```lean
structure LinearCodeStruct (F : Type*) [Field F] (n : ℕ) where
  toSubmodule : Submodule F (Fin n → F)
  decidableMembership : DecidablePred (· ∈ toSubmodule)

def dimension (c : LinearCodeStruct F n) : ℕ := ...
def minDistance (c : LinearCodeStruct F n) : ℕ := ...
def isMDS (c : LinearCodeStruct F n) : Prop := minDistance c = n - dimension c + 1
def parityCheckMatrix (c : LinearCodeStruct F n) : Matrix (Fin r) (Fin n) F := ...
def restrictToSupport (c : LinearCodeStruct F n) (T : Finset (Fin n)) :
    LinearCodeStruct F T.card := ...
```

Bridge theorem from Reed-Solomon: `reedSolomonCode cfg`'s submodule
equals the image of `reedSolomonEncode`. This is one of the easier
items.

**Estimate: 2–3 weeks.** Most of the work is in `restrictToSupport` and
proving its dimension/distance properties under MDS.

### A.2 — Hamming distance / agreement-set lemmas

Mathlib has `Hamming.lean` (built on `PiLp`). We need it specialised to
finite-dimensional `Fin n → F` with combinatorial accessors:

- `agreementSet u v : Finset (Fin n)` — coordinates where `u i = v i`
- Bridge: `(agreementSet u v).card + hammingDist u v = n`
- Closure under linear combinations: agreement of `α·u₁ + β·u₂` with `α·v₁ + β·v₂` ⊇ `agreementSet u₁ v₁ ∩ agreementSet u₂ v₂`
- Restriction-to-support codeword lifting

**New file: `LinearCodes/Algebraic/Agreement.lean`**

**Estimate: 1 week.** Mostly bookkeeping; agreement-set algebra is
elementary but voluminous.

### A.3 — Corrádi lemma (Mathlib-bound contribution)

BCGM25 Lemma 3.23 (Corrádi 1969): if `A₁, …, Aₘ ⊆ A` with `|Aᵢ| = α|A|`
and `|Aᵢ ∩ Aⱼ| ≤ ρ|A|` for `i ≠ j`, then `α² > ρ` implies
`m ≤ (α − ρ) / (α² − ρ)`.

This is pure finite combinatorics. Mathlib does not have it. The proof
is double-counting: count `(i, x)` pairs in two ways. Roughly a one-page
proof in undergraduate combinatorics.

**New file: `Mathlib/Combinatorics/Corradi.lean`** (target: upstream PR
to Mathlib)

```lean
theorem Finset.corradi {A : Finset α} (As : ι → Finset α) (h_sub : ∀ i, As i ⊆ A)
    (h_size : ∀ i, (As i).card * |A| = α * (As i).card)  -- shape will need rationals
    (h_pairwise : ∀ i j, i ≠ j → ((As i) ∩ (As j)).card ≤ ρ * |A|)
    (h_strict : α^2 > ρ) :
    Fintype.card ι ≤ (α - ρ) / (α^2 - ρ) := ...
```

Exact statement to be tightened once we settle on real/rational
representation. BCGM25 also proves a generalised version for `k`-wise
intersections in Appendix D — we will need that too for some
applications, but Lemma 3.23 unblocks the unique-decoding branch.

**Estimate: 2–3 weeks** including upstreaming. Could be done in parallel
with A.1/A.2.

### A.4 — MCA toolbox (BCGM25 §4)

Three composition lemmas that BCGM25 uses to glue MCA results across
operations on generators:

- **Linear transformations** (§4.1): `G` has MCA ⇒ `MG` has MCA after a
  full-rank linear pre-composition.
- **Tensor products** (§4.2): MCA composes through `G₁ ⊗ G₂`.
- **Matrix-vector composition** (§4.3): a key reduction lemma that
  decomposes a polynomial generator into simpler pieces.

These are mostly index-juggling + `Matrix.mul` lemmas once the algebraic
core (A.1) is in place. They have no exotic dependencies.

**New file: `LinearCodes/MCA/Toolbox.lean`**

**Estimate: 2–3 weeks.**

### A.5 — Two counting lemmas (BCGM25 §5)

Section 5 of the paper bridges Corrádi to the MCA setting:

- A "many-good-seeds-implies-shared-support" counting lemma (uses A.3).
- A "support-restriction" lemma that strips `T` down to the actual
  agreement set.

These are direct corollaries of A.3 plus combinatorics; ~1 week.

### A.6 — Theorem 6.1, unique-decoding branch (BCGM25 §6.1)

The capstone of Phase A. Combine A.1–A.5 to prove:

> For an MDS generator `G` with relative MCA distance `γ ≤ δ_𝒞/3`,
> `ε_MCA(γ) ≤ max{n·γ, 1} · ε_ZE(G)`.

This is the **unique-decoding** branch of BCGM25 Theorem 1. The proof
runs over ~3 pages of the paper (§6.1) and is the most technically dense
part of Phase A, but it stays inside finite linear algebra and Corrádi.

**New file: `LinearCodes/MCA/UniqueDecoding.lean`**

**Estimate: 3–4 weeks.**

### Phase A totals

| Step | Estimate | Status |
|---|---|---|
| A.1 Linear-code algebraic core | 2–3 weeks | **expanded (2026-05-05)** — `LinearCodes/Algebraic/Code.lean` and `LinearCodes/Algebraic/Restriction.lean`, zero sorries. Includes `hammingWeight`, `hammingDistance` (algebra: triangle, comm, bounds, weight-distance bridge, neg/smul/add invariance), `MinDistAtLeast` + monotonicity, `IsMDS`, `InRestrictedCode` predicate (the BCGM25 `c|T` form) with 8 closure properties. Deferred: `parityCheckMatrix` — until A.6 needs it. Design deviation: lightweight predicates on `Submodule F (Fin n → F)` instead of a `LinearCodeStruct` record; restriction expressed as a predicate (`InRestrictedCode c T u`) rather than a separate Submodule. |
| A.2 Agreement-set lemmas | 1 week | **✅ done (2026-05-05)** — `LinearCodes/Algebraic/Agreement.lean`, zero sorries |
| A.3 Corrádi lemma | 2–3 weeks | **✅ done (2026-05-05)** — `Upstream/Combinatorics/Corradi.lean`, zero sorries |
| MCA scaffolding | — | **partial (2026-05-05)** — `LinearCodes/MCA/Definitions.lean`, `Generator`, `Generator.combine`, `seedProb` with non-neg + ≤1 bounds, zero sorries. Full `MCA`/`CA`/`ZeroEvading` predicates pending toolbox + counting lemmas. |
| A.4 MCA toolbox | 2–3 weeks | not started |
| A.5 Two counting lemmas | 1 week | not started |
| A.6 Unique-decoding theorem | 3–4 weeks | not started |
| **Total** | **~3–4 months full-time** | |

(Phase A standalone wire-up to `mcaProximityGapError` at δ_𝒞/3 is
omitted — Phase A is treated as a building block for Phase B, not a
deliverable on its own.)

A.1–A.4 can be parallelised modestly. End-to-end calendar time on
solo-with-Aleph-as-second pace: **realistic estimate 4–6 months**.

## Phase B — List-decoding (Johnson) regime

This is what STIR/WHIR/WARP profilers actually need. Phase B replaces
the `proven` mode of `mcaProximityGapError` with a verified bound valid
up to the Johnson radius `1 − √ρ`.

### B.1 — Bivariate polynomial method infrastructure

The Guruswami-Sudan construction is the proof technique for both
BCIKS18 and BCGM25 list-decoding sections. It needs Mathlib-level
infrastructure:

- **Bivariate polynomial representation** — choose between
  `MvPolynomial (Fin 2) F` (general but heavyweight) or
  `Polynomial (Polynomial F)` (lighter, asymmetric). Mathlib has both;
  neither has the GS-specific lemmas we need.
- **Multiplicity at a point** — the `m`-fold zero of `Q(X,Y)` at `(αᵢ, βᵢ)`.
  Mathlib has `Polynomial.rootMultiplicity` for univariate; the bivariate
  generalisation needs to be developed.
- **Weighted degree** — `(1, k−1)`-weighted degree of `Q(X,Y)`. New.
- **Parameter-counting interpolation existence theorem** — "if the number
  of monomials of weighted degree `< D` exceeds `m·(m+1)/2 · |interp set|`,
  a non-zero interpolant exists." Linear-algebra one-liner *given* the
  weighted-degree machinery.
- **Restricted polynomial degree bound** — `Q(X, p(X))` has degree
  `< D + (k−1) · deg p` when `p` agrees on enough points.

**New module: `LinearCodes/Algebraic/Bivariate/`**

**Estimate: 2–4 months.** This is the heaviest single block. Some pieces
could be upstreamed to Mathlib's `MvPolynomial` library, which would
benefit other formalisations (algebraic geometry, coding theory).

### B.2 — Guruswami-Sudan list decoder (BCGM25 §6.2)

The list-decoding theorem itself: given received word `r`, the list of
codewords `c ∈ RS[F, D, k]` with `Δ(c, r) ≤ τ` has size `≤ L` for
explicit `L = O(n)`. Proof factors through B.1.

**New file: `LinearCodes/MCA/ListDecoding.lean`**

**Estimate: 1–2 months.**

### B.3 — BCGM25 list-decoding bound (Theorem 6.1, second branch)

Combine B.1, B.2 with the toolbox (A.4) and the generalised Corrádi
(A.3 extended) to get the second branch of BCGM25 Theorem 1, valid up
to Johnson radius.

**Estimate: 1–2 months.**

### B.4 — RS-specific improvement (BCGM25 §9)

Section 9 of BCGM25 sharpens the bound for Reed-Solomon specifically.
This is the result that STIR/WHIR/WARP authors actually cite. Builds on
B.1–B.3 plus RS-specific arguments.

**Estimate: 1 month.**

### Phase B totals

| Step | Estimate |
|---|---|
| B.1 Bivariate polynomial infrastructure | 2–4 months |
| B.2 GS list decoder | 1–2 months |
| B.3 List-decoding MCA bound | 1–2 months |
| B.4 RS-specific improvement | 1 month |
| **Total** | **~6–9 months full-time** |

Phase B has more research risk than Phase A — the bivariate polynomial
infra has never been built in Mathlib for this purpose. Estimates carry
±50% uncertainty.

## Combined timeline

| | Optimistic | Realistic | Pessimistic |
|---|---|---|---|
| Phase A only | 3 months | 4–5 months | 6 months |
| Phase A + Phase B | 9 months | 12–14 months | 18 months |

These assume one full-time formaliser using the `Aleph` prover as
acceleration. Halve speed for spare-time pace.

## What gets shipped along the way

Even partial completion has value:

- **After A.3 (Corrádi)**: a Mathlib PR. Useful far beyond this project.
- **After A.6**: machine-checked unique-decoding-regime soundness for
  STIR/WHIR/WARP at `δ ≤ δ_𝒞/3`. Looser than practitioners use, but a
  real verified guarantee for a real protocol regime.
- **After B.1**: a Mathlib bivariate polynomial library that benefits
  any future coding-theory or algebraic-geometry formalisation effort.
- **After B.3**: the actual deliverable — verified `proven`-mode
  bit-security for STIR/WHIR/WARP up to Johnson radius.
- **After B.4**: tighter RS-specific numbers matching state-of-the-art
  practitioner profilers.

## Risk register

- **Mathlib drift**: 12-month projects against `v4.28` can hit breaking
  changes. Mitigation: pin and rebase quarterly.
- **B.1 underestimation**: the bivariate machinery is the biggest
  unknown. If it slips by 2× it dominates the timeline. Mitigation:
  scout it early (~2 weeks of B.1 prototyping before committing to
  Phase B).
- **Aleph rate of helpfulness**: Aleph excels at well-formed algebraic
  goals but struggles with combinatorial counting. Phases A.3 and A.5
  may benefit less from Aleph than A.6 or B.3 do.
- **Scope creep on `LinearCodeStruct`**: the algebraic core (A.1) can
  expand if we try to cover too many code constructions. Mitigation:
  scope it to "what BCGM25 needs," not "general coding theory library."

## Decisions locked in (2026-05-05)

1. **Scope** — Phases A and B are committed together. Phase A is *not*
   a standalone deliverable; the wire-up to `mcaProximityGapError` at
   `δ_𝒞/3` is dropped from the plan. The full target is verified
   Johnson-radius MCA (Phase B.3) plus the RS-specific sharpening
   (Phase B.4).
2. **Upstreaming** — Mathlib-bound material (Corrádi lemma, bivariate
   polynomial library) is built in this repo first under `Upstream/`,
   structured to mirror Mathlib's directory layout. Upstream PRs come
   later, after the in-tree proofs are stable.
3. **Generality** — `LinearCodeStruct` is parameterised over `[Field F]`
   throughout. Finite-field hypotheses are added per-theorem only where
   strictly required (e.g., `Fintype F` for counting arguments).
4. **Aleph budget** — ~2 weeks of free Aleph use available for the
   kickoff sprint. Spend it on whichever blocks have the highest
   density of fiddly algebraic sub-goals (likely A.6 and B.3).
5. **Urgency** — foundation-speculative; no specific protocol deadline
   driving the timeline. Quality over speed; correctness over coverage.
6. **Personnel** — solo formalisation, with reviewers brought in once
   substantive blocks are complete.

## Starting point

A.3 (Corrádi) is the kickoff block: cleanest standalone, low coupling,
reusable everywhere downstream, candidate for the first upstream PR.
