# Session checkpoint — 2026-05-05

A faithful snapshot of where the BCGM25 formalization stands, what
worked, and where the breadth-first parallel-agent push hit
diminishing returns. This is the document to hand to the next session.

## Honest status

**What's solid:**

* `Upstream/Combinatorics/Corradi.lean` — Corrádi's lemma (BCGM25 Lemma
  3.23) fully proven. ~7 theorems, no sorries. Candidate for upstream
  Mathlib PR.
* `LinearCodes/Algebraic/Agreement.lean` — agreement-set algebra,
  symmetry, complement-to-Hamming-distance bridge. 5 theorems.
* `LinearCodes/Algebraic/Code.lean` — `hammingWeight`, `hammingDistance`,
  full algebra (triangle, comm, smul/neg/add invariance), `MinDistAtLeast`,
  `IsMDS`, plus the **§6.1 foundation** (`hammingDistance_le_of_agree_on`,
  `agreement_implies_eq_of_MDS`). ~22 theorems.
* `LinearCodes/Algebraic/Restriction.lean` — `InRestrictedCode`
  predicate with full closure (zero/add/sub/neg/smul/mono/univ-iff/
  empty/singleton). 11 theorems.
* `LinearCodes/MCA/Definitions.lean` — `Generator`, `Generator.combine`
  + algebra, `seedProb`, `ZeroEvading`, `MutualCorrelatedAgreement`,
  `CorrelatedAgreement`. 11 theorems including `combine_smul_const`.
* `LinearCodes/MCA/Properties.lean` — trivial-error cases, monotonicity
  in ε, **Lemma 3.18 forward (Aleph)**. 7 theorems including
  `MCA_implies_ZeroEvading_at_zero`.
* `LinearCodes/MCA/SeedProbLemmas.lean` — `seedProb_mono`, `_congr`,
  `_or_le`, MCA-bad-event monotonicity in γ. 5 theorems.
* `LinearCodes/MCA/Examples.lean` — `identity`, `univariatePowers`,
  `affineLine`, `affineSpace` generators + identities. 7 theorems.
* `LinearCodes/MCA/InducedCode.lean` — `dotMap`, `inducedCode`,
  weight machinery, **Lemma 3.13 (Aleph)**. ~10 theorems including
  `ZeroEvading_from_inducedCode_min_dist`.
* `LinearCodes/MCA/CAImplications.lean` — **MCA-zero simplification
  (Aleph)**. Plus `MCA_implies_CA` (Lemma 3.22) — see below.

**Total:** ~90 theorems, mostly clean, full project builds.

## Where we hit a wall

### Lemma 3.22 (MCA → CA)

Aleph determined the statement is false (twice). My current revision
adds `hℓ : 0 < ℓ` to fix the trivial counterexample at `ℓ = 0`, but
Aleph still rejects it.

**My math says this should be true.** Either:
* There's another edge case I'm missing (e.g., `εMCA` allowed to be
  negative; `n = 0` after the case split; rational-arithmetic issue
  with the `(e − 1) / n` cast).
* Aleph has a counterexample I haven't seen yet — pull the PR and
  read it.
* Aleph couldn't find the proof and reported "false" as the default.

**Suggested next step:** read Aleph's specific counterexample. Either
fix the statement (likely tightening hypotheses on εMCA or n), or
attempt a manual proof to verify the math is sound.

### Aleph "theorem not found"

Two recent stubs (`inducedCode_finrank_le`, `dotMap_injective_iff`)
weren't visible to Aleph because I added them locally without pushing.
The user controls git and is the sole author. **Workflow rule going
forward:** I add sorries locally, the user pushes when ready, then
sends to Aleph. I should stop racing ahead with new stubs.

### Quality slipping

Past 3-4 rounds have been small definitional lemmas (`rfl`, `simp`)
that the agent fanout closes trivially but which add little to
project value. The hard work (§4 toolbox, §6 capstone, Phase B) is
ahead and won't yield to the same approach.

## Plan refresh

### Immediate (next session)

1. **Resolve Lemma 3.22.** Read Aleph's counterexample (pull
   `ai-prover-20260505_135034`). Either fix the statement or attempt
   manual proof.
2. **Push staged stubs** (`inducedCode_finrank_le`,
   `dotMap_injective_iff`, the §6.1 foundation in `Code.lean`).
3. **Pivot from breadth to depth.** Stop adding small lemmas. The
   accumulated infrastructure is enough for the next hard theorem.

### Next hard target

**BCGM25 Theorem 6.1 (unique-decoding regime, capstone of Phase A).**

What it needs that we have:
* MDS rigidity (`agreement_implies_eq_of_MDS`) ✓
* Corrádi (`Upstream/Combinatorics/Corradi.lean`) ✓
* MCA + ZE definitions ✓
* Code restriction (`InRestrictedCode`) ✓
* Generator + dotMap algebra ✓

What it needs that we don't have:
* The combinatorial argument: bound the number of "bad" α ∈ F where
  the linear combination is δ-close to a (different) codeword. Uses
  Corrádi on the family of agreement sets.
* Specific to MDS generators: `Generator.IsMDS` predicate and the
  zero-evading bound from Lemma 3.13 chained back to MCA.

This is real BCGM25 §6 mathematics. ~5 pages of paper proof to
formalize. Best done with Aleph in tight loop, not breadth-first
agents.

### Phase A remaining

| Block | Status |
|---|---|
| A.1 core | ~80% (deferred parityCheckMatrix; decision: continue deferring until needed) |
| A.2 agreement | ✅ |
| A.3 Corrádi | ✅ |
| A.4 toolbox (§4) | 0% — biggest unstarted block |
| A.5 counting lemmas (§5) | 0% — unblocked by A.4 |
| A.6 capstone (Theorem 6.1) | 0% — needs A.4, A.5 |

**Realistic Phase A completion:** 2-4 more weeks at current pace,
mostly bottlenecked on A.4 and A.6 difficulty.

### Phase B remains the unknown

Bivariate polynomial machinery, Guruswami-Sudan list decoder, BCGM25
§6.2 / §9. None of this exists in Mathlib. ~6-9 months of work as per
the original plan. No agent has been near it.

## Workflow rules going forward

1. **User is sole git author.** I never push or commit; user pushes
   batches and sends targets to Aleph.
2. **Throughput matters.** Stage as many *substantive* targets as makes
   sense in a batch — Aleph runs them in parallel. The earlier
   problem wasn't volume, it was racing ahead of the user's push
   cadence and padding with trivia.
3. **No padding.** Trivial `rfl`/`simp` lemmas go inline. Aleph
   targets must be load-bearing toward Theorem 6.1, §4 toolbox, or
   Phase B.
4. **Each target gets a clean docstring** plus a brief in
   `LinearCodes/doc/aleph-target-*.md` when the proof strategy is
   non-obvious.
5. **General-purpose agent fanout** is still useful for *known-tractable*
   sub-goals (helpers, definitional unfolding) — Aleph for the
   research-grade theorems.

## Git state (at refresh)

* Working tree clean (user pushed after this checkpoint was first
  written). All local sorries are now on the remote.
* Three Aleph runs **in flight** (started 2026-05-05 ~16:00):
  * `MCA_implies_CA` in `LinearCodes/MCA/CAImplications.lean` —
    revised with `hℓ : 0 < ℓ` per Aleph's earlier counterexample.
  * `inducedCode_finrank_le` in `LinearCodes/MCA/InducedCode.lean`.
  * `dotMap_injective_iff` in `LinearCodes/MCA/InducedCode.lean`.
* §6.1 foundation lemmas (`hammingDistance_le_of_agree_on`,
  `agreement_implies_eq_of_MDS`) are **proved and pushed** in
  `LinearCodes/Algebraic/Code.lean`.

## First prompt for the next session

Suggested kickoff message:

> Continuing the BCGM25 formalization. Read
> `LinearCodes/doc/session-checkpoint-2026-05-05.md` for full context.
>
> Workflow rules:
> 1. I am sole git author. You never push or commit.
> 2. Stage as many *substantive* targets per round as makes sense — I'll
>    push them in batches and feed Aleph in parallel. Throughput matters.
> 3. **No padding.** Trivial `rfl`/`simp` lemmas go inline. Aleph targets
>    must be load-bearing toward Theorem 6.1 / §4 toolbox / Phase B.
> 4. Each Aleph target needs a clean docstring + (when non-obvious) a
>    brief explaining the proof strategy and helper lemmas in scope.
>
> Direction: BCGM25 Theorem 6.1 capstone. Next sub-blocks are §4 toolbox
> (linear transformations, tensor products, matrix-vector composition)
> and §5 counting lemmas. §6.1 foundation (MDS rigidity) is already done.
>
> First questions:
> 1. Did the three pending Aleph runs finish? Which proved, which failed?
> 2. After they land, stage the next batch toward §4.1 / §6.1.

## Where the project actually is

* **~90 theorems closed**, full project builds clean.
* **§3 Preliminaries**: ~75% done. Lemma 3.18 forward (Aleph),
  Lemma 3.13 (Aleph), MCA-zero simplify (Aleph), Corrádi (me),
  full structural framework.
* **§6.1 foundation**: MDS rigidity proved (the algebraic backbone
  of Theorem 6.1).
* **§4 toolbox**: 0%. Next major block.
* **§5 counting**: 0%. Unblocked by §4.
* **§6 capstone (Theorem 6.1)**: 0%. Needs §4, §5, plus the seed-
  counting argument that uses Corrádi.
* **Phase B (bivariate, GS list-decoder, §6.2, §9)**: 0%. Research-
  grade, not yet started.

**Honest progress estimate:** ~17–20% of total project. Phase A is
~50–60% done; Phase B is the major remaining mass.
