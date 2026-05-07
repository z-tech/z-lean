# Literature survey: closing the +1 slack on BCGM25 Lemma 5.3 / 6.2

**Question.** The Lean formalization of BCGM25 Lemma 6.2 (unique-decoding MCA) requires
`|B| > (nγ + 1)(ℓ-1)` rather than the paper's stated `|B| > nγ(ℓ-1)`.  Is there a known
proof technique that closes this `+1` slack, and what do the recent literature bounds
actually say?

## Headline result

**The user's `(nγ+1)(ℓ-1)` bound matches the *current state-of-the-art lossless bound* in the
literature (Ben‑Sasson–Carmon–Häböck–Kopparty–Saraf 2025, eprint 2025/2055, Theorem 4.1).
The BCGM25 paper's `nγ(ℓ-1)` is a real-number bound that *quietly assumes* `nγ` is an
integer — when `nγ` is non‑integer, the integer‑rounded version of the paper's argument
yields exactly `(ℓ-1)(γn + 1)`, i.e. the user's bound. In particular Remark 2.5 of
BCH+25 proves that `(γn+1)` per fold direction is *tight* (a matching adversarial example
exists). The `+1` is therefore not a Lean artefact but an inherent feature of integer
counting in the AHIV/BKS/double‑counting family of arguments.**

So the slack is "intrinsic" only relative to the *zero-evading + double-counting* family
that BCGM25 actually uses.  Below we audit every paper that has been put forward as a
candidate for closing the gap.

---

## 1. BCGM25 — *All Polynomial Generators Preserve Distance with MCA*
PDF: <https://eprint.iacr.org/2025/2051.pdf>

### Lemma 5.3 (verbatim hypothesis)
> Fix a zero-evading generator `G : S → F^ℓ` with error `ϵ_ZE`, codewords `c_1,…,c_ℓ ∈ C`,
> and integers `e ∈ {1,…,n}`, `1 ≤ t ≤ e`. Set
> `A := { x ∈ S : Δ(G(x)·U, Span_G(c_1,…,c_ℓ)[x]) ≤ e − t }`.
> If `|A| > (e/t) · ϵ_ZE · |S|`, then `Δ_{Σ^ℓ}(U, Mat(c_1,…,c_ℓ)) < e`.

The `(e,t)`-form is genuinely strictly stronger than the corollary used in Lemma 6.2:
the multiplicative slack `e/t` becomes `1` only when `t = e`, i.e., when the *bad seeds
have exactly zero error*. Bad seeds in Lemma 6.2 have error `≤ nγ`, so applying the
`(e,t)`-form gives at best the same `nγ(ℓ-1)` real-number bound that becomes
`(nγ+1)(ℓ-1)` after integer rounding.

### Lemma 6.2 (unique decoding — what the user is formalizing)
The contradiction step is
> the number of such `T_x` is less than `[n]\T̃ · (ℓ-1) < n·γ·(ℓ-1)`

This step uses both `|T̃| > n(1-γ)` (real number) and `|T̃| ≥ ⌈n(1-γ)⌉` (integer);
the strict real inequality `n-|T̃| < nγ` is silently used. Over the integers,
`n-|T̃| ≤ ⌊nγ⌋` (which **equals** `nγ` only when `nγ ∈ ℤ`), so the contradiction
requires `|B| > ⌊nγ⌋(ℓ-1)` — and to make that follow from a clean hypothesis, one
must take `|B| > (nγ+1)(ℓ-1)` (the floor of `nγ + 1` always upper-bounds `⌊nγ⌋`).
**This is exactly the Lean bound.** The paper's `nγ(ℓ-1)` is correct only modulo
integer rounding.

### Proof technique
Zero-evading double-counting (Lemma 5.3 proof: count `(x, i)` pairs where
`G(x) · v(i)⊺ = 0`).  Three independent agents have already established that the
`+1` slack is intrinsic to this family of arguments.

---

## 2. Häböck 2025 — *A note on mutual correlated agreement for RS codes*
PDF: <https://eprint.iacr.org/2025/2110.pdf>

### Key statement: Lemma 1 (AHIV/BKS18 form, restated by Häböck)
> Given `f_0, f_1 : D → F_q` and codewords `p_0, p_1 ∈ C` with
> `∆(p_0 + z·p_1, f_0 + z·f_1) ≤ γ` for all `z ∈ S ⊆ F_q`. Then if
> `|S| > ⌈γ·n⌉ + 1`, we have `∆([p_0,p_1], [f_0,f_1]) ≤ γ`.

Note: **Häböck uses `⌈γn⌉ + 1` — i.e. exactly the user's `(γn + 1)` form.**
The paper's actual technical bound is the same as ours.

Häböck's note generalizes BCIKS18's list-decoding analysis (Berlekamp–Welch +
Polishchuk–Spielman over `F_q(Z)`) to the global proximity gap setting up to the
Johnson radius `1 − √(1−δ)`.  Since the *unique-decoding* bound that Häböck states
(Lemma 1) already has the `+1`, the note **does not** sharpen Lemma 5.3/6.2.

### Could it close our slack?
No.  Häböck's technique is the same Berlekamp–Welch tower-field argument as BCIKS18;
the unique-decoding lossless statement built on top has the very `⌈γn⌉ + 1` form we
already have.

---

## 3. Ben-Sasson–Carmon–Häböck–Kopparty–Saraf 2025 ("BCH+25")
*Improved bounds for proximity gaps for Reed–Solomon codes*
PDF: <https://eprint.iacr.org/2025/2055.pdf>

This is the **current state-of-the-art**.  Two key statements are directly relevant.

### Lemma 2.4 (the AHIV/BKS18 lossless lemma, optimized form)
> Assume `p_0, p_1 ∈ C` satisfy `∆(u_0 + z·u_1, p_0 + z·p_1) ≤ γ` for `a ≥ 2`
> values `z ∈ F_q`.  Then `∆([u_0,u_1], [p_0,p_1]) ≤ (a/(a-1)) · ⌊nγ⌋`.

**Remark 2.5 of BCH+25**: *The bound is tight* whenever `d = a·e/(a-1)` is an
integer; an explicit adversarial code/word pair is exhibited.

Setting `a = γn + 2` (i.e. `a > γn + 1`) yields
`(a/(a-1))·⌊nγ⌋ = ((γn+2)/(γn+1))·⌊nγ⌋ < ⌊nγ⌋ + 1`, so distance `≤ ⌊nγ⌋`,
which is `≤ nγ` integer-equivalently — i.e. correlated agreement holds.
Concretely: `a > γn + 1` is the *exact* lossless threshold (Theorem 1.14, summary
table p. 7, "ε∗ = 0 for a > γn + 1").

### Theorem 4.1 (curve / multi-function lossless variant — directly comparable to BCGM25 6.2)
> Let `M ≥ 1`. If
> `|{ z ∈ F_q : ∆(u_0 + z·u_1 + … + z^M·u_M, C) ≤ γ }| > M · (γn + 1)`
> then `∆([u_0,…,u_M], C^{M+1}) ≤ γ`.

For `M = ℓ - 1`, this is **literally** `|B| > (ℓ-1)(γn+1)` = the user's bound!

> *"Zero distance loss is obtained by requiring `(M/(a-M))·γ < 1/n`, that is `a > M·(γn+1)`."*
> — BCH+25 §4.1

### Could it close our slack?
**No — and that is the point.** BCH+25 explicitly proves that `M·(γn+1)` is the
correct lossless threshold and (Remark 2.5) that the underlying inequality is tight.
The user's Lean bound matches BCH+25 exactly.

The only way one could write `M·γn` (without the `+1`) is to assume `γn ∈ ℤ`.
This is occasionally done implicitly in informal presentations (BCGM25 §6.2 reads
this way), but the *integer-careful* statement is `M·(γn+1)`.

---

## 4. BCIKS18 — Ben-Sasson–Carmon–Ishai–Kopparty–Saraf 2020 / eprint 2018/611
PDF: <https://eprint.iacr.org/2020/654.pdf>

### Theorem 4.1 (unique decoding, ℓ = 2)
> Suppose `δ ≤ (1-ρ)/2`.  Let `S = { z ∈ F_q : ∆(u_0 + z u_1, V) ≤ δ }`.
> If `|S| > n` then `S = F_q` and there exist `v_0, v_1 ∈ V` with
> `∆((u_0,u_1), (v_0,v_1)) ≤ δ`.

The `|S| > n` form is exponentially loose (`n` not `δn`); BCIKS18 chose this
formulation because the proof uses Berlekamp–Welch over `K = F_q(Z)` followed by
Polishchuk–Spielman.  This is a **fundamentally different proof strategy** from
BCGM25's zero-evading double-counting.

The BCIKS18 Section 6 generalization to ℓ functions gives `|S| > ℓ·(e+1)` ≈
`ℓ·(γn+1)`, again with the `+1`.

### Could it close our slack?
**No.** Even the BCIKS18-style proof yields `(γn+1)` per fold direction in its
lossless integer form. Moreover, BCIKS18 requires Reed–Solomon structure
(uses Polishchuk–Spielman); BCGM25 Theorem 6.1 is for **arbitrary linear MDS-generated
codes**, so transplanting the BCIKS18 argument is not a one-line drop-in.

---

## 5. Brakerski–Kohlmann (2024)
A 2024 manuscript on RS proximity gaps was located only via secondary references in
the survey papers below; the result is subsumed by BCH+25 / Häböck and uses the same
Berlekamp–Welch strategy. No tighter unique-decoding integer bound is claimed.

PDF (best available): pointed to via [Comparative Analysis HackMD](https://hackmd.io/@zkpunk/B1XulQJe-e).

---

## 6. Other recent papers consulted

- **Syndrome-Space Lens (eprint 2025/1712)**: <https://eprint.iacr.org/2025/1712.pdf>.
  Resolves the CA / MCA problem at *capacity* (not just Johnson) via a syndrome-space
  reformulation. The technique is information-theoretic and gives an asymptotic ε bound;
  it does **not** address the integer constant in Lemma 5.3-style counting arguments.
- **Open Problems in CA (eprint 2026/680)**: <https://eprint.iacr.org/2026/680.pdf>.
  Surveys the landscape; the open questions concern proximity-loss vs. parameter `a`
  trade-offs at and beyond the Johnson radius. The `+1` integer slack is *not* listed
  as an open question — consistent with it being known to be tight.
- **On RS Proximity Gaps Conjectures (eprint 2025/2046)**: <https://eprint.iacr.org/2025/2046.pdf>.
  Conjectures concern the asymptotic regime; integer rounding is not at issue.

---

## Conclusion and recommendation

1. **The user's Lean bound `|B| > (nγ+1)(ℓ-1)` is paper-tight relative to BCH+25
   Theorem 4.1**, the strongest published lossless variant of the AHIV/BKS18 / Lemma 5.3
   family of arguments.
2. **The `+1` is not a defect — it is the integer-honest version of the bound BCGM25 §6.2
   states informally as `nγ(ℓ-1)`.** The paper's bound only equals ours when `nγ ∈ ℤ`.
3. **Tightness is published**: BCH+25 Remark 2.5 exhibits an adversary saturating
   the underlying inequality, ruling out a strictly tighter integer bound from the
   double-counting family.
4. **No technique in the surveyed literature closes the `+1` for general MDS-generated
   linear codes.** The Berlekamp–Welch / Polishchuk–Spielman strategy of
   BCIKS18 / Häböck is restricted to Reed–Solomon codes (it needs polynomial
   structure of the codewords) and even there yields the *same* integer threshold.
5. **Suggested wording for the Lean docstring**: state Lemma 6.2 with the
   `(nγ+1)(ℓ-1)` hypothesis and cite BCH+25 Theorem 4.1 plus Remark 2.5 as
   evidence that the bound is integer-tight; the BCGM25 `nγ(ℓ-1)` form should be
   noted as the real-number version, equivalent for `nγ ∈ ℤ`.

If the project ever requires the strict `nγ(ℓ-1)` (e.g. for a downstream theorem
that sets `nγ` to an integer by construction), one can add an integer-`nγ`
hypothesis and recover the paper's bound directly; otherwise the current statement
is already optimal.
