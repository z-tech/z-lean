# Aleph target: Theorem 6.1 Case 2 (γ ≥ 1/n)

The targets are the two remaining `sorry`s in `LinearCodes/MCA/MaximalDomain.lean`:

| Theorem | Path |
|---|---|
| `MCA_unique_decoding_large_gamma_bound` | `LinearCodes/MCA/MaximalDomain.lean` |
| `MCA_unique_decoding_bound` | `LinearCodes/MCA/MaximalDomain.lean` |

The second is just a case-merge of Case 1 (already proved as
`MCA_unique_decoding_small_gamma_bound`) and Case 2 (the first target).

## What you're proving (Case 2)

```lean
theorem MCA_unique_decoding_large_gamma_bound
    [Fintype S] [DecidableEq S] [Nonempty S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_lo : 1 / n ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ n * γ * (ℓ - 1 : ℚ) / Fintype.card S
```

## BCGM25 §6.1 Case 2 proof (paper, page 29-30)

The proof is by contradiction. Suppose the bad set `B` (set of `x` satisfying
the bad event) has `|B| > n·γ·(ℓ-1)`. Then `|B| ≥ ℓ` (since `n·γ·(ℓ-1) ≥ ℓ-1`).
Pick ℓ distinct `x₁,...,xₗ ∈ B`.

For each `xᵢ`, let `cᵢ ∈ c` be the unique closest codeword to `G.combine xᵢ us`.
By MDS hypothesis, the matrix `M := Mat(G(xᵢ))` is invertible. Define:
```
Mat(c₁*, ..., cₗ*) := M⁻¹ · Mat(c₁, ..., cₗ)
```
For any `x ∈ B`, by triangle inequality:
- `Δ(uₓ, G(x)·Mat(c*)) ≤ n·γ·ℓ` (where `uₓ := G.combine x us`)
- `Δ(cₓ, G(x)·Mat(c*)) ≤ n·γ·(ℓ+1) < n·δ_C` (by `hγ_hi`)

By min distance: `cₓ = G(x)·Mat(c*)` for any `x ∈ B`. The set
`T̃ := {i : ∀ j, uⱼ[i] = cⱼ*[i]}` is a CA domain with `|T̃| > n·(1-γ)`.

For any `x ∈ B`, the agreement set `Tₓ` between `uₓ` and `cₓ` strictly
contains `T̃`. By Lemma 6.6 (`strict_superset_count_bound`, already proved),
the number of such distinct `Tₓ` is `< |[n]\T̃|·(ℓ-1) < n·γ·(ℓ-1)`,
contradicting `|B| > n·γ·(ℓ-1)`.

## Available infrastructure (all proved, in tree)

* `MCABadWitness G c us γ x` — bundle of `T, cw, T_size, cw_mem, agree, bad_row`
  for each `x` in the bad event.
* `mkMCABadWitness` — extract from `∃ T ...` form.
* `MCABadWitness.exists_maxAgreement_extending` — extend `w.T` to a maximal
  agreement domain.
* `exists_max_agreement_domain_extending`, `exists_max_CA_domain_extending`
  — extension lemmas.
* `maxAgreement_intersection_isMaxCA` (Lemma 6.4) — intersection of max
  agreement domains, with `T ⊆ each Aⱼ` and maximality, becomes a max CA domain.
* `maxAgreement_inter_eq_maxCA` (Lemma 6.5).
* `strict_superset_count_bound` (Lemma 6.6).
* `MDS_unique_decoding` — unique-decoding rigidity.
* `agreement_implies_eq_of_MDS`, `MDS_distinct_codewords_disagree`,
  `MDS_pairwise_agreement_bound`, `MinDistAtLeast.codewords_eq_of_agree`.
* `Generator.IsMDS.dotMap_zero_at_distinct_seeds_implies_zero`,
  `all_us_mem_of_combine_at_distinct_seeds` — the kernel/surjectivity bridge
  from MDS to matrix-style invertibility.
* `seedProb_le_ncard_div`, `seedProb_mono`.
* `MCA_bad_event_at_small_gamma_eq_zero_event` (Case 1, but the
  reduction-to-univ part may be useful).
* The MCA bad event predicate at γ — proved monotone in γ.

## Suggested high-level structure

```lean
-- 1. By contradiction, assume the bad set has card > n·γ·(ℓ-1).
-- 2. Convert to {x | bad event at γ}.ncard > n·γ·(ℓ-1).
-- 3. For each bad seed x, construct a max agreement domain B_x containing
--    its witness T, via `MCABadWitness.exists_maxAgreement_extending`.
-- 4. Show ∃ ℓ-tuple of distinct bad seeds whose B_xᵢ's intersect in size
--    > n - δ_C (using hγ_hi to control sizes).
-- 5. Apply Lemma 6.4 to get a max CA domain A := T ⊆ each B_xᵢ with
--    A.card > n - δ_C.
-- 6. Apply Lemma 6.5 to all bad witnesses (any ℓ chosen) to show their
--    intersection equals A.
-- 7. Conclude every bad seed's witness B_x strictly contains A.
-- 8. Apply `strict_superset_count_bound` (Lemma 6.6) to bound the count
--    of distinct B_x's by `(ℓ-1) * (n - A.card) ≤ (ℓ-1) * (n - (n - δ_C + 1)) ≤ (ℓ-1)·n·γ`.
-- 9. Contradiction.
```

The rational/ℕ-cast arithmetic for connecting `n·γ·(ℓ-1)` (ℚ-valued) to the
Lemma 6.6 ℕ-bound `(ℓ-1) * (n - A.card)` is fiddly but mechanical.

## What you're proving (Unified)

```lean
theorem MCA_unique_decoding_bound
    [Fintype S] [DecidableEq S] [Nonempty S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS) (hℓ : 0 < ℓ)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (ℓ + 1) < δ_C / n) :
    seedProb (S := S) (fun x => <bad event>)
    ≤ max ((n : ℚ) * γ) 1 * (ℓ - 1) / Fintype.card S
```

After Case 2 lands, this is just a case-split on `n*γ < 1` (apply Case 1)
vs `1 ≤ n*γ` (apply Case 2), with the `max` evaluating accordingly.

## Pre-flight check

`lake build LinearCodes.MCA.MaximalDomain` should succeed with two warnings.

## Status

Case 1 (γ < 1/n, ε_MCA(γ) ≤ (ℓ-1)/|S|) is fully proved. Lemmas 6.4, 6.5,
6.6 fully proved. All structural infrastructure in place. This is the
final wiring step for BCGM25 Theorem 6.1 (unique-decoding regime).
