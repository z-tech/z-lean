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

1. **User is sole git author.** I add files/sorries locally; user
   pushes, sends to Aleph, merges PRs.
2. **I don't push.** Ever.
3. **Don't race ahead with stubs.** Stage one or two clean targets
   per round, wait for the user to feed Aleph, then continue.
4. **Stop padding theorems.** If a lemma is `rfl` or `simp`, write
   it inline rather than as a separate theorem unless it's load-
   bearing.
5. **Pivot to depth when shallow agents stop adding value.** That
   point is here. Next hard target should be tackled with focused
   work, not 100-agent fanout.

## Git state

* Local changes (uncommitted): `Code.lean`, `CAImplications.lean`,
  `InducedCode.lean`, `aleph-target-lemma-3-22.md`.
* Local sorries: 3 (Lemma 3.22, `inducedCode_finrank_le`,
  `dotMap_injective_iff`).
* Remote `origin/z-tech/linear-codes`: through Aleph's Lemma 3.13 +
  MCA-zero-simplify merges.

## What I need from the user to continue cleanly

1. Pull Aleph's `MCA_implies_CA` PR diff so I can see the actual
   counterexample, OR confirm I should pivot away from 3.22.
2. Decide whether to push my local stubs (`§6.1 foundation lemmas`
   in Code.lean — these are genuinely useful and proved, not stubs).
3. Direction: continue trying to crack Phase A blocks (A.4 toolbox
   is the next major one), or pause and review architecture.
