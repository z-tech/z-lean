# Swarm plan: BCGM25 Theorem 6.1 (unique-decoding regime)

The Phase A capstone. Decomposes into independent sub-blocks
suitable for parallel agent fanout.

## Theorem statement (target)

```lean
/-- **BCGM25 Theorem 6.1, unique-decoding branch.** Let `G : S → F^ℓ`
be a generator and let `c ⊆ F^n` be a code that admits an MDS
generator-induced bound. For tradeoff `γ ≤ δ_c / 3` (where
`δ_c = (n - k + 1) / n` is the relative distance):
`ε_MCA(γ) ≤ max{n·γ, 1} · ε_ZE(G)`. -/
theorem MCA_unique_decoding_bound ...
```

(Exact statement to refine after sub-blocks land.)

## What we already have (foundation)

All in tree, zero sorries:

* `Upstream/Combinatorics/Corradi.lean` — Corrádi's lemma.
* `LinearCodes/Algebraic/Code.lean` — MDS rigidity:
  - `agreement_implies_eq_of_MDS`
  - `MDS_distinct_codewords_disagree`
  - `MDS_pairwise_agreement_bound`
  - `MDS_unique_decoding`
  - `hammingDistance_le_of_agree_on`
* `LinearCodes/MCA/InducedCode.lean` — `dotMap`, `inducedCode`,
  `dotMap_injective_iff`, `inducedCode_finrank_le`,
  `ZeroEvading_from_inducedCode_min_dist`.
* `LinearCodes/MCA/Definitions.lean` — Generator, combine, seedProb,
  ZE/CA/MCA predicates.
* `LinearCodes/MCA/SeedProbLemmas.lean` — seedProb monotonicity.
* `LinearCodes/MCA/CAImplications.lean` — Lemma 3.22, MCA-zero
  simplify.

## Decomposition into parallel-executable chunks

The BCGM25 §6.1 proof breaks naturally into 4 phases. Each phase has
internal parallelism.

### Phase 1: Witness-codeword construction (parallel: 3-4 agents)

For each "bad" seed `α` in the MCA bad event at γ, we need a witness
codeword `c_α ∈ c` such that `(G(α) · U)|T_α = c_α|T_α` for some
`T_α` of size `≥ n(1-γ)`. The MCA-bad-event predicate already encodes
this existential. We need to extract it as a function.

Sub-tasks (independent):

1. **Define `mcaWitnessCodeword`**: from a seed `x` in the bad event,
   extract the witness codeword. Uses classical choice. ~5 lines def.
2. **Define `mcaWitnessSet`**: extract the witness `T_α`. Similar.
3. **Lemma**: in unique-decoding regime (γ < δ_c/3 with appropriate
   slack), the witness codeword is unique. Use `MDS_unique_decoding`.
4. **Lemma**: `mcaWitnessCodeword x ∈ c`. Trivial from the definition.

**Agent fanout: 4 parallel tasks**, each ~5-15 lines.

### Phase 2: Pairwise-intersection bound (parallel: 2-3 agents)

For two distinct bad seeds `α, α'` with witness codewords
`c_α, c_α'`, bound the pairwise intersection of their agreement sets:
* If `c_α ≠ c_α'`: directly apply `MDS_pairwise_agreement_bound`.
* If `c_α = c_α'`: this requires the unique-decoding range argument
  to show such collision is impossible (else `α = α'`).

Sub-tasks (independent):

1. **`witness_distinct_codeword_of_distinct_seeds`**: in unique-
   decoding regime, distinct bad seeds have distinct witness codewords
   (uses `MDS_unique_decoding`).
2. **`pairwise_intersection_lt_k`**: combines #1 with
   `MDS_pairwise_agreement_bound` to bound `|T_α ∩ T_α'| < k` for
   distinct `α, α'`.

**Agent fanout: 2 parallel tasks**, each ~10-20 lines.

### Phase 3: Corrádi application (parallel: 2 agents)

Apply Corrádi's lemma (already proved) to the family of agreement
sets `{T_α : α bad seed}` to bound the number of bad seeds.

Sub-tasks (independent):

1. **`bad_seed_count_le_corradi_bound`**: instantiate Corrádi with
   the witness sets. Each `T_α` has size `≥ n(1-γ)`, pairwise
   intersection `< k`. Plug into `Finset.corradi_unconditional` or
   `_ratio` form.
2. **Sanity-check the field-size assumption**: confirm Corrádi
   applies (the `α² > b · |A|` hypothesis where `α = (1-γ)`,
   `b = (k-1)/n`, `A = [n]`).

**Agent fanout: 2 parallel tasks**, total ~30 lines.

### Phase 4: Wire to seedProb and εMCA (sequential: 1-2 agents)

Translate the bad-seed count into a seed-probability bound, then
combine with `ε_ZE` to produce the final `max{n·γ, 1} · ε_ZE` bound.

Sub-tasks:

1. **`bad_seed_seedProb_bound`**: convert "≤ N bad seeds" to
   `seedProb ≤ N / |S|`.
2. **Final theorem `MCA_unique_decoding_bound`**: combine #1 with
   `ZeroEvading_from_inducedCode_min_dist` and the multiplicative
   structure of the bound.

**Agent fanout: 1 sequential then 1 final**, ~20-40 lines.

## Total agent budget estimate

Phase 1: 4 agents × 1 round
Phase 2: 2 agents × 1 round (depends on Phase 1)
Phase 3: 2 agents × 1 round (depends on Phase 2)
Phase 4: 2 agents × 1 round (depends on Phase 3)

**~10 agents across 4 sequential rounds**, plus possible Aleph
escalations on whichever block resists general-purpose agents.

## What we DON'T have yet (potential blockers)

* The `Generator.IsMDS_inducedCode` predicate — connects MDS structure
  of the generator-induced code to the BCGM25 hypothesis. Needs
  `inducedCode` distance estimation.
* The exact `δ_c / 3` threshold encoding — need to phrase
  `γ ≤ δ_c/3` cleanly in ℚ.
* The `max{n·γ, 1}` factor in the final bound — needs careful ℚ
  arithmetic to handle the regime split.

These should be handled inline as sub-lemmas during Phase 4.

## Risk register

* **Phase 2 unique-decoding range**: the `MDS_unique_decoding` we have
  uses `2*hd ≤ n − k`, but BCGM25's `γ ≤ δ_c/3` translates to a
  different inequality. May need a refinement of `MDS_unique_decoding`
  with a sharper hypothesis.
* **Phase 3 Corrádi instantiation**: the strict `α² > b·|A|` may not
  hold for all γ in the unique-decoding regime — need to verify the
  range carefully.
* **Phase 4 multiplicative bound**: `max{n·γ, 1}` arithmetic in ℚ
  with both regimes (small γ and γ near `δ_c/3`) is fiddly.

## Suggested execution order

1. Stage Phase 1 stubs (4 sorries) → user pushes → fanout.
2. Verify Phase 1 lands; adjust if any block stuck → user pushes Aleph
   request for stuck pieces.
3. Stage Phase 2 stubs → fanout.
4. ...

Each phase: stage all stubs in one batch, push, fan out. If stuck on
any block after 1-2 agent rounds, escalate that specific block to
Aleph while continuing other blocks.
