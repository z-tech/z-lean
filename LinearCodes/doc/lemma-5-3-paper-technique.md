# BCGM25 Lemma 5.3 — Paper Proof Technique

**Goal of this note.** The Lean formalization of BCGM25's Lemma 5.3
(`Ttilde_card_gt_of_MDS_aggregate` in
`LinearCodes/MCA/Case2Subtargets.lean`) carries an intrinsic `+1` slack
relative to the paper's tight bound. Multiple ℚ-double-counting attempts
have confirmed the slack is unavoidable in the *current Lean shape* of
the lemma. This note records what the paper *actually* does, identifies
the precise trick that yields the tight bound, and sketches a
Lean-implementable plan.

## 1. Citation / Source

- **Paper**: Sarah Bordage, Alessandro Chiesa, Ziyi Guan, Ignacio Manzur.
  *All Polynomial Generators Preserve Distance with Mutual Correlated
  Agreement*. IACR ePrint **2025/2051**.
- **PDF**: https://eprint.iacr.org/2025/2051.pdf
- **Section**: §5 ("Two counting lemmas"), Lemma 5.3 on pp. 27–28
  (followed by Remark 5.4 with an alternative dual interpretation).
- **Companion**: Ulrich Häböck, *A note on mutual correlated agreement
  for Reed–Solomon codes*, IACR ePrint 2025/2110, contains a parallel
  bound for RS codes via a power-decoder / Berlekamp–Welch argument.

## 2. Exact Statement (paper, verbatim)

> **Lemma 5.3.** Fix a zero-evading generator `G : S → F^ℓ` with error
> `ε_ZE ∈ [0,1]`, an F-linear code `C ⊆ Σ^n`, `e ∈ {1, …, n}`,
> `1 ≤ t ≤ e`, a set of words `U = Mat(u₁, …, u_ℓ) ∈ Σ^{ℓ×n}`, and
> codewords `c₁, …, c_ℓ ∈ C`. Define the set `A` as follows:
>
> ```
> A := { x ∈ S : Δ(G(x)·U, Span_G(c₁,…,c_ℓ)[x]) ≤ e − t }.
> ```
>
> If `|A| > (e/t) · ε_ZE · |S|` then `Δ_{Σ^ℓ}(U, Mat(c₁,…,c_ℓ)) < e`.

**Reading.** `e` is the target column-Hamming-distance threshold (the
"bad event") and `t` is a *tightness slack* parameter the user picks
**inside** `[1, e]`. The hypothesis trades off `|A|` against the
per-seed agreement quality `e − t`. Setting `t = e` recovers the cleanest
form (`A = { x : G(x)·U = Span_G(...)[x] }` and `|A| > ε_ZE · |S|`).

The Lean version specializes to MDS generators with `ε_ZE = (ℓ−1)/|S|`,
absorbing the `(e, t)` parameters into a strict bound on `|B_set|`
relative to `n·γ·(ℓ−1)`. **The `(e, t)` two-parameter structure is the
crux**: it is exactly what controls the rounding boundary the Lean code
loses.

## 3. The Proof Technique (paper, ~7 sentences)

The proof is a **double-counting argument over the rectangle
`A × ([n] \ T)`**, where `T := { i : ∀ j, u_j[i] = c_j[i] }` is the
exact-agreement set. The trick that makes it tight is **bounding the
column-sum from above by a per-seed expectation, *not* a per-seed
cardinal count**, exploiting the chosen aggregate `Δ(G(x)·U, G(x)·c)`
that is *uniform on T* (zero contribution).

Concretely, define the column-difference vectors `v(i) := (c_j[i] − u_j[i])_j`,
which are *nonzero precisely when* `i ∉ T`. The proof chains four
inequalities:

```
e − t ≥ E_{x∈A} Δ(G(x)·U − G(x)·c, 0)             (definition of A)
      = (1/|A|) · Σ_{x∈A} Σ_{i ∉ T} 1{G(x)·v(i)⊺ ≠ 0}   (T contributes 0; sum over [n] = sum over [n]\T)
      = (1/|A|) · Σ_{i ∉ T} Σ_{x∈A} 1{G(x)·v(i)⊺ ≠ 0}   (Fubini)
      ≥ (1/|A|) · (n − |T|) · (|A| − ε_ZE · |S|)        (zero-evading per-coord bound on the *complement*)
      > (n − |T|) · (1 − t/e),                           (strict; uses |A| > (e/t)·ε_ZE·|S| from hypothesis)
```

Rearranging gives `|T| > n − e`, i.e., `Δ_{Σ^ℓ}(U, Mat(c₁,…,c_ℓ)) < e`.
The final strict inequality is **inherited from the strict hypothesis on
`|A|`**: the hypothesis `|A| > (e/t)·ε_ZE·|S|` is equivalent to
`(|A| − ε_ZE·|S|)/|A| > 1 − t/e`, which is exactly what propagates
through the double-counting.

### Why this avoids the `+1` slack

The Lean code derives `|T̃| ≥ n(1−γ) − 1` because it applies the
double-counting in **opposite direction**: counting bad-seed pairs
`(x, i) ∈ B_set × ([n] \ T̃)` with `1{G(x)·v(i) = 0}`. There, the
per-coord upper bound is `≤ ε_ZE·|S| = ℓ−1` and the per-seed lower
bound is `≥ |T_x| − |T̃| ≥ n(1−γ) − |T̃|`, yielding
`b·s ≤ (n − |T̃|)·(ℓ − 1)` where `s := n(1−γ) − |T̃|`. To force `s ≤ 0`
strictly from `b > n·γ·(ℓ−1)` alone, one needs an extra unit of slack
in `b`, hence `+1`.

The paper *avoids this entirely* by counting `1{G(x)·v(i) ≠ 0}` on the
**good-seed set `A`** (the *complement* of `B_set`), with the
*per-coord lower bound* `≥ |A| − ε_ZE·|S|` and **a per-seed bound that
is an arithmetic average bounded by `e − t`** (a real number, not an
integer cardinality). The strict `|A| > (e/t)·ε_ZE·|S|` hypothesis
makes the chain *strict* without any rounding step, because both sides
of the `≥`/`>` inequalities are exact rationals — no Finset
cardinality is the binding constraint.

In short: **the paper double-counts an `(e, t)`-parameterized
*expectation of distance*, while the Lean code double-counts a
*Boolean event*.** The expectation form is what enables a tight
strict-to-strict propagation.

## 4. Lean Formalization Sketch

### 4.1 Reformulate the Lean lemma in `(e, t)` form

Replace the current shape

```lean
theorem Ttilde_card_gt_of_MDS_aggregate
    (h_size : (B_set.card : ℚ) > (n * γ + 1) * (ℓ - 1))
    ...
    : (Ttilde.card : ℚ) ≥ n * (1 - γ) - 1
```

with the paper's shape parameterized by `(e, t)`:

```lean
theorem Lemma_5_3
    (G : Generator F S ℓ) (hZE : G.IsZeroEvading εZE)
    (us : Fin ℓ → (Fin n → F)) (cs : Fin ℓ → (Fin n → F))
    (hcs : ∀ j, cs j ∈ C)
    (e : ℕ) (he : 1 ≤ e ∧ e ≤ n) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ e)
    (A : Finset S)
    (hA_def : ∀ x ∈ A,
       (Finset.univ.filter (fun i => G.combine x us i ≠ G.combine x cs i)).card
         ≤ e - t)
    (hA_size : (A.card : ℚ) > (e / t) * εZE * Fintype.card S)
    : (Finset.univ.filter
         (fun i : Fin n => ∃ j, us j i ≠ cs j i)).card < e
```

The symmetric column-difference `v(i)` and the global agreement set
`T = univ \ ({i : ∃ j, us j i ≠ cs j i})` then follow.

### 4.2 Key auxiliary lemmas needed

1. **Per-coord zero-evading bound on `[n] \ T`** (essentially restated
   from the existing `bad_pair_count_per_coord_le`):
   ```lean
   ∀ i, (∃ j, us j i ≠ cs j i) →
     (Finset.univ.filter (fun x => G.combine x (us - cs) i = 0)).card
       ≤ εZE * Fintype.card S
   ```

2. **Expectation rewrite**: for `x ∈ A`, the sum
   `Σ_i 1{G(x)·v(i) ≠ 0}` equals exactly `Δ(G(x)·U, G(x)·cs)`. This is
   because indices in `T` contribute 0 by definition of `T`. So
   `Σ_{i ∉ T} 1{G(x)·v(i) ≠ 0} = Δ(G(x)·U, G(x)·cs) ≤ e − t`.

3. **Fubini / `Finset.sum_comm`** to swap the order of summation.

4. **Linear arithmetic chain** combining (1) and (2) to derive
   `(e − t)·|A| ≥ (n − |T|)·(|A| − εZE·|S|)`, then rearranging to
   `(n − |T|) < e` using strict positivity of `(|A| − εZE·|S|)`.

### 4.3 Connection back to current Case 2 capstone

The Case 2 capstone (`MCA_unique_decoding_large_gamma_bound` in
`MCA/Case2Capstone.lean`) feeds the lemma the values

```
e = ⌈ n·γ ⌉,    t = ⌈ n·γ ⌉,   ⇒  (e/t) = 1.
```

So the simplified `t = e` form of Lemma 5.3 — `|A| > εZE · |S|
⇒ Δ < e` — is what's actually invoked. With `εZE = (ℓ−1)/|S|`,
the hypothesis becomes `|A| > ℓ − 1`, equivalently
`|S \ B_set| > ℓ − 1`, i.e., `|B_set| < |S| − (ℓ − 1)`. Combined with
the standard `|B_set| ≤ n·γ·(ℓ−1)` reduction (already in the codebase),
the paper-tight Phase A bound `n·γ·(ℓ−1)/|S|` follows.

## 5. Difficulty Estimate

- **Lean LOC**: ~250–400 net new lines, broken down as:
  - ~80 LOC: new `(e, t)`-shape statement and column-difference setup.
  - ~120 LOC: rational expectation-rewrite + Fubini combinatorics
    (this is the part that is *unfamiliar* relative to the existing
    Boolean double-counting; will need new helpers around
    `Finset.sum_comm`, `Finset.card_filter`, and a clean
    `expectation := (1/|A|)·Σ ... ≤ e − t` lemma).
  - ~80 LOC: connecting the new Lemma 5.3 to the existing Case 2
    capstone (replace the `(n·γ + 1)·(ℓ−1)` hypothesis with
    `n·γ·(ℓ−1)`).
  - ~50 LOC: cleanup of the `+1`-slack annotations propagated through
    `Case2Capstone.lean` and `paper-to-lean-map.md`.
- **Hours estimate**: 6–10 focused hours for an experienced Lean user.
  The risky part is the rational-expectation manipulation; the rest is
  routine Finset-sum arithmetic similar to existing code.
- **Risk**: **Low.** The mathematical chain is short (4 inequalities)
  and the existing infrastructure already provides the per-coord
  zero-evading bound and the column-difference vector machinery. The
  only genuinely new component is the *direction-flip* of the double
  counting (count agreement on `A`, not disagreement on `B`).

## 6. Cross-references

- BCIKS18 ("Proximity Gaps for Reed–Solomon Codes", Ben-Sasson et al.,
  ePrint 2020/654) uses a related but distinct
  power-decoder / Berlekamp–Welch trick for RS codes; that proof does
  *not* generalize to arbitrary linear codes and is not what BCGM25
  uses for Lemma 5.3 specifically.
- Häböck (ePrint 2025/2110) gives a parallel bound for RS codes also
  via power decoding; again specialized to RS, not the linear-code
  setting of Lemma 5.3.
- Brakerski–Kohlmann (2024) — same observation; the BCGM25 technique
  is more general and is the one to formalize for Lean.

## 7. Verdict

The paper-tight bound *is* attainable in Lean by **reshaping the
double-counting from a Boolean count over `B_set` to a rational
expectation over `A := S \ B_set`, parameterized by `(e, t)`**. This
is a structural reformulation, not a deeper algebraic insight. The
estimated cost is moderate (~250–400 LOC, 6–10 hours).
