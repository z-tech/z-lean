# Lemma 5.3 boundary case: numerical counterexample

**TL;DR.** A small concrete example with `n = 5, ℓ = 2, γ = 0.4,
F = ZMod 5` shows the *Lean-shape* "paper bound" `|B_set| > nγ(ℓ-1)` is
**genuinely insufficient** to conclude `|T̃| ≥ n(1-γ)`. We exhibit
`(|B_set|, |T̃|) = (3, 2)`, which satisfies `3 > 2 = nγ(ℓ-1)` but
violates `|T̃| ≥ 3 = n(1-γ)`. The Lean lemma's strengthened hypothesis
`|B_set| > (nγ + 1)(ℓ-1) = 3` rules this out (`3 > 3` is false), so the
`+1` slack is **necessary** for the Lean shape of the lemma. The slack
is *not* merely an artifact of the Lean proof.

The Lemma file: `LinearCodes/MCA/Lemma53Examples.lean` (with `#eval`
sanity checks). The Lean theorem under analysis:
`Ttilde_card_gt_of_MDS_aggregate` in
`LinearCodes/MCA/Case2/` (line 917).

## 1. Parameters and threshold values

| symbol | value |
|---|---|
| `n` (codeword length) | 5 |
| `ℓ` (output dim, also the field-power `k`) | 2 |
| `γ` (proximity parameter) | 2/5 |
| `F` (field) | `ZMod 5` |
| `S` (seed type) | `F`, so `|S| = 5` |
| `G : S → F^ℓ` | `affineLine F`, i.e. `G(x) = (1, x)` |
| ε_ZE (MDS bound) | `(ℓ-1)/|S| = 1/5` |

| threshold | value |
|---|---|
| `n · γ` | 2 |
| `n · γ · (ℓ - 1)` (paper hypothesis: |B| > 2) | 2 |
| `(n · γ + 1) · (ℓ - 1)` (Lean hypothesis: |B| > 3) | 3 |
| `n · (1 - γ)` (target conclusion: |T̃| ≥ 3) | 3 |

## 2. The construction

Take `cstars j = 0` for both `j ∈ {0, 1}` (the zero codeword pair; valid
in any linear subspace). Define `us` by

```
us 0 = (0, 0, 0, 4, 3)    -- mod 5
us 1 = (0, 0, 1, 1, 1)
```

Equivalently, the column-difference vectors `v(i) := us(i) - cstars(i) =
us(i)` are:

```
v(0) = (0, 0)    -- zero  → i = 0 ∈ T̃
v(1) = (0, 0)    -- zero  → i = 1 ∈ T̃
v(2) = (0, 1)    -- nonzero
v(3) = (4, 1)    -- nonzero (= (-1, 1) mod 5)
v(4) = (3, 1)    -- nonzero (= (-2, 1) mod 5)
```

Hence `T̃ = {0, 1}`, `|T̃| = 2`.

## 3. Computing `B_set`

For each seed `x ∈ F = ZMod 5`, agreement at coord `i` is
`G(x) · v(i) = v(i)_0 + x · v(i)_1 = 0`. Coords 0 and 1 always agree
(`v = 0`). For coords 2, 3, 4, the unique-zero seeds are:

| `i` | `v(i)` | unique seed `x` with `G(x)·v(i) = 0` |
|---|---|---|
| 2 | `(0, 1)` | `x = 0` |
| 3 | `(4, 1) = (-1, 1)` | `x = 1` |
| 4 | `(3, 1) = (-2, 1)` | `x = 2` |

So the per-seed agreement sets are

| `x` | agree coords | `|·|` | `Δ_x` (Hamming dist) |
|---|---|---|---|
| 0 | {0, 1, 2} | 3 | 2 |
| 1 | {0, 1, 3} | 3 | 2 |
| 2 | {0, 1, 4} | 3 | 2 |
| 3 | {0, 1} | 2 | 3 |
| 4 | {0, 1} | 2 | 3 |

The Lean-shape bad-seed set is `B_set := {x : agree-card ≥ n(1-γ) = 3}`,
giving `B_set = {0, 1, 2}`, `|B_set| = 3`.

For each `x ∈ B_set`, the witness `Tx` is just the agree-coord set
above; `|Tx| = 3 ≥ n(1-γ) = 3`, so the Lean hypothesis `h_agree` is
satisfied with the obvious witness.

## 4. Verification (`#eval` outputs)

The file `LinearCodes/MCA/Lemma53Examples.lean` evaluates these
quantities concretely. The actual `#eval` outputs match the predictions
above:

```
(2, 3, 0)                          -- (|T̃|, |B_set|, |A_strict-paper|)
((2, 3, 0), 3, 3, 3, 2, 2)         -- + per-seed agree-coord cardinalities
(5, 5, 1, 1, 1)                    -- per-coord agree-seed cardinalities
```

The per-coord cardinalities `(5, 5, 1, 1, 1)` confirm the MDS per-coord
ε_ZE bound: on `T̃` (coords 0, 1) every seed agrees (`v = 0`); off `T̃`
(coords 2, 3, 4) exactly `ℓ - 1 = 1` seed agrees per coordinate.

## 5. Comparison with the three "paper bounds"

There are *three different* statements floating around when comparing to
the paper. Distinguishing them resolves the apparent contradiction.

### 5.1 Paper Lemma 5.3 with `t_param = e` (its tightest form)

> Hypothesis: `|A_strict| > ε_ZE · |S| = ℓ - 1` where
> `A_strict := {x : G(x)·U = G(x)·c}` (i.e. `Δ_x = 0`).
> Conclusion:  `Δ_full < e` (paper's free integer parameter).

In our example `A_strict = ∅` (no seed has `Δ_x = 0` — see `(2, 3, 0)`
above, third entry). Hypothesis fails. Paper says nothing. **No
contradiction.**

### 5.2 Paper Lemma 5.3 in its general `(e, t_param)` form

> Hypothesis: `|A| > (e / t_param) · ε_ZE · |S|` where
> `A := {x : Δ_x ≤ e − t_param}`, with `1 ≤ t_param ≤ e`.

To make `A` correspond to the Lean `B_set ≡ {x : Δ_x ≤ nγ}`, one needs
`e − t_param = nγ = 2`, i.e., `e = t_param + 2`. Combined with
`t_param ≥ 1`, the smallest legal choice is `t_param = 1, e = 3`. The
hypothesis becomes

`|A| > (3 / 1) · 1 = 3`,

i.e., `|A| ≥ 4`. The conclusion is `Δ_full < e = 3`, i.e.,
`|T̃| ≥ n − e + 1 = 3`.

In our example `|A| = |B_set| = 3` and `|T̃| = 2 < 3`. Hypothesis
fails (`3 > 3` is false). Paper says nothing. **No contradiction.**

### 5.3 The "naive paper translation" claimed in the codebase comments

> Hypothesis: `|B_set| > nγ(ℓ-1) = 2`.
> Conclusion:  `|T̃| ≥ n(1-γ) = 3`.

In our example `|B_set| = 3 > 2` and `|T̃| = 2 < 3`. Hypothesis
satisfied, conclusion fails. **CONTRADICTION!** This shape of the
lemma is **simply false** as stated.

The codebase comment in `Case2/` line 723 — "BCGM25's
Lemma 5.3 states `|T̃| > n(1-γ)` (strict) under the hypothesis
`|B_set| > n·γ·(ℓ-1)`" — is **wrong** when `B_set` is taken with the
Lean-shape definition `{x : Δ_x ≤ nγ}`. It would only be correct under
the much narrower paper-shape definition `B_set = A_strict =
{x : Δ_x = 0}`.

## 6. Verdict

The Lean lemma's `+1` slack on the hypothesis (`|B_set| > (nγ+1)(ℓ-1)`
instead of `|B_set| > nγ(ℓ-1)`) is **mathematically necessary**, not a
proof-engineering artifact, **for the Lean shape of `B_set`**
(`{x : Δ_x ≤ nγ}`).

* The `+1` precisely closes the integer-rounding gap when
  `nγ ∈ ℤ`, where the combinatorial inequality `b · s ≤ (n-t)(ℓ-1)`
  with `s = n(1-γ) − t` allows a realizable `(b, t) = (3, 2)` in our
  parameters.
* The companion claim `|T̃| > n(1-γ)` (strict) is *also* correct in
  the paper, but only when one starts from the strict-paper hypothesis
  `|A_strict| > ℓ-1` (with `A_strict = {Δ_x = 0}`). That hypothesis
  is *strictly stronger* than `|B_set| > nγ(ℓ-1)`.

In particular, the planning note `lemma-5-3-paper-technique.md` line 169
("the paper-tight Phase A bound `n·γ·(ℓ−1)/|S|` follows") is **not
justified** unless the upstream Phase A code is *also* re-shaped to use
the strict `Δ_x = 0` form of `B_set`, which is a deeper restructuring
than just rewriting Lemma 5.3. Replacing the Lean `B_set` definition
with the paper's `A_strict` would break the Case 2 capstone, since the
union-bound argument that produces the bad-seed set there gives `Δ ≤
nγ`, not `Δ = 0`.

### Practical implication for the slack-removal plan

The `+1` slack in `Ttilde_card_gt_of_MDS_aggregate` cannot be removed
*locally*. To recover the BCGM25-tight Phase A bound `nγ(ℓ-1)/|S|`, one
must:

1. *Either* re-prove Case 2's bad-seed set uses `Δ_x = 0` (paper's
   strict `A`), not `Δ_x ≤ nγ` — which is harder and may fail
   altogether (the "bad" seeds in the IOP literature are inherently the
   `Δ ≤ nγ` ones), OR
2. Accept the `+1` factor as fundamental to the chosen definition of
   `B_set`, and update the doc comments in `Case2/` to
   reflect that the paper's `nγ(ℓ-1)` claim is for a *different,
   strictly stronger* `B_set` shape.

Option (2) is the honest documentation fix. Option (1) is a
research-level restructuring of the Case 2 reduction.

## 7. Files

* `/Users/zitek/Documents/z-lean/LinearCodes/MCA/Lemma53Examples.lean`
  — concrete `#eval` sanity checks of `|T̃|, |B_set|`, etc.
* `/Users/zitek/Documents/z-lean/LinearCodes/MCA/Case2/`
  line 917 — the Lean theorem `Ttilde_card_gt_of_MDS_aggregate`.
* `/Users/zitek/Documents/z-lean/LinearCodes/doc/lemma-5-3-paper-technique.md`
  — the planning note (this analysis revises its conclusions).
