# Aleph target: BCGM25 Lemma 3.13 (zero-evading from induced-code distance)

Target: `ZeroEvading_from_inducedCode_min_dist` in
`LinearCodes/MCA/InducedCode.lean`.

## What you're proving

```lean
theorem ZeroEvading_from_inducedCode_min_dist
    {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] [Nonempty S] {ℓ : ℕ}
    (G : Generator F S ℓ) (d : ℕ)
    (h_dist : Generator.fnMinDistAtLeast G.inducedCode d)
    (h_inj : Function.Injective G.dotMap) :
    ZeroEvading G ((Fintype.card S - d : ℚ) / Fintype.card S)
```

This is BCGM25 Lemma 3.13 (specialized form). The intuition: if the
induced code `C_G` has min distance `≥ d`, then any nonzero codeword
has at most `|S| − d` zero coordinates, so the seed-probability that
`G(x) · v = 0` is at most `(|S| − d) / |S|`.

## Definitions in scope

```lean
def Generator.dotMap (G : Generator F S ℓ) : (Fin ℓ → F) →ₗ[F] (S → F) where
  toFun := fun v x => ∑ j, G x j * v j
  ...

def Generator.inducedCode (G : Generator F S ℓ) : Submodule F (S → F) :=
  LinearMap.range G.dotMap

def Generator.fnHammingWeight (w : α → F) : ℕ :=
  (Finset.univ.filter fun i => w i ≠ 0).card

def Generator.fnMinDistAtLeast (c : Submodule F (α → F)) (d : ℕ) : Prop :=
  ∀ w ∈ c, w ≠ 0 → d ≤ Generator.fnHammingWeight w

def ZeroEvading G ε := ∀ v : Fin ℓ → F, v ≠ 0 →
  seedProb (S := S) (fun x => ∑ j, G x j * v j = 0) ≤ ε

def seedProb {S : Type*} [Fintype S] (P : S → Prop) : ℚ :=
  letI : DecidablePred P := Classical.decPred P
  (Finset.univ.filter P).card / (Fintype.card S : ℚ)
```

## Proof strategy

Fix `v : Fin ℓ → F` with `v ≠ 0`. Goal:
```
seedProb (fun x => ∑ j, G x j * v j = 0) ≤ (|S| - d) / |S|
```

**Step 1.** Note `(∑ j, G x j * v j) = G.dotMap v x` by `dotMap_apply`.
So the predicate `(∑ j, G x j * v j = 0)` is `(G.dotMap v x = 0)`.

**Step 2.** `G.dotMap v ≠ 0` because `v ≠ 0` and `G.dotMap` is injective
(use `h_inj` plus `LinearMap.map_zero` to compare):
```lean
have h_dotv_ne : G.dotMap v ≠ 0 := by
  intro h_eq
  apply hv
  apply h_inj
  rw [h_eq]
  exact (LinearMap.map_zero G.dotMap).symm
```

**Step 3.** `G.dotMap v ∈ G.inducedCode` (definitional — it's the range).

**Step 4.** By `h_dist`, `d ≤ fnHammingWeight (G.dotMap v)`. That is,
the *number of nonzero* coordinates of `G.dotMap v` is at least `d`.
Hence the number of *zero* coordinates is at most `|S| − d`:
```
(Finset.univ.filter (fun x => G.dotMap v x = 0)).card ≤ |S| - d
```

This requires the partition identity:
```
(filter (≠ 0)).card + (filter (= 0)).card = |univ|
```
which is `Finset.card_filter_add_card_filter_not` (or similar) applied
to the predicate `(G.dotMap v x ≠ 0)`.

**Step 5.** Conclude. After unfolding `seedProb`:
```
seedProb (fun x => G.dotMap v x = 0)
  = (filter (= 0)).card / |S|
  ≤ (|S| - d) / |S|
```

Use `div_le_div_of_nonneg_right` (or `div_le_div_iff_of_pos_right`) with
the cardinality bound.

## Helper lemmas already proved

* `Generator.dotMap_apply : G.dotMap v x = ∑ j, G x j * v j` (def-eq)
* `LinearMap.map_zero G.dotMap : G.dotMap 0 = 0`
* `LinearMap.mem_range : w ∈ LinearMap.range f ↔ ∃ v, f v = w`
* `seedProb_mono` — for the conditional reduction (may not be needed
  here, since we go directly through the cardinality argument)

## Mathlib hints

* `Finset.card_filter_add_card_filter_not` — partition identity
* `Finset.card_filter_le` — filter card bounded by parent card
* `div_le_div_of_nonneg_right` — divide both sides by nonneg
* `Fintype.card_pos` (under `Nonempty S`)

## Edge cases

* `d = 0`: bound becomes `|S| / |S| = 1`, trivially holds.
* `d > |S|`: would make `|S| − d` negative in ℕ but we cast through ℚ.
  Hypothesis `h_dist` is vacuous if d > |S| (no nonzero element has
  weight that high). Bound `(|S| − d) / |S|` becomes `0 / |S| = 0` (in ℚ
  with truncated subtraction)... actually in ℚ, `|S| − d` could be
  negative, and the quotient becomes negative. The seedProb is ≥ 0,
  so `0 ≤ seedProb ≤ ε` would fail. Either flag this or assume `d ≤ |S|`
  as a hypothesis. **Action:** if you find this, return a partial proof
  noting the issue and we'll add `d ≤ Fintype.card S` as a hypothesis.

## Pre-flight check

`lake build LinearCodes.MCA.InducedCode`
