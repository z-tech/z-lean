# CompPoly upstream handoff: `CompPoly.ext` + `LawfulBEq` plumbing

Two upstream changes to CompPoly (https://github.com/Verified-zkEVM/CompPoly,
pinned to rev `01609714…` in this repo's `lakefile.lean`) that would let the
sumcheck soundness proofs drop two load-bearing local kludges.

These are independent: ship one or both, in either order.

## Context

The sumcheck soundness chain in
[`SumcheckProtocol/Properties/Lemmas/SoundnessLemmas.lean`](../Properties/Lemmas/SoundnessLemmas.lean)
and
[`SumcheckProtocol/Properties/Lemmas/HonestRoundProofs.lean`](../Properties/Lemmas/HonestRoundProofs.lean)
has two recurring frictions when interacting with `CPoly.CMvPolynomial`:

1. **Eval-extensionality on `CMvPolynomial 1 𝔽` is implicit but unexposed.**
   `agreement_set_card_le`
   (`SoundnessLemmas.lean:268`) takes `g ≠ h : CMvPolynomial 1 𝔽` and bounds the
   set of agreement points by `degreeOf 0 (differencePoly g h)`. The chain
   `g ≠ h → differencePoly g h ≠ 0 → bounded-many roots` works locally via the
   `MvPolynomial` bridge, but is open-coded; a small upstream lemma would make
   it a one-liner. Caveat: unconditional eval-extensionality is **false** over
   finite fields (e.g. `x^p` and `x` over `F_p`). Any upstream lemma must be
   conditional — see "Item 2" below.

2. **`LawfulBEq R` has to be hand-built locally** every time a proof needs
   `CMvPolynomial`'s `==` to behave (because the internal `Std.ExtTreeMap`
   compares keys via `BEq`). Current sites:
   - [`HonestRoundProofs.lean:407-422`](../Properties/Lemmas/HonestRoundProofs.lean#L407-L422)
   - [`SoundnessLemmas.lean:759-761`](../Properties/Lemmas/SoundnessLemmas.lean#L759-L761)

   Both pin a `BEq 𝔽` via `instBEqOfDecidableEq` and then construct
   `LawfulBEq 𝔽` by hand from the underlying `DecidableEq 𝔽`. This is pure
   plumbing — the user already has `[DecidableEq 𝔽]`, so the BEq+LawfulBEq
   combo is determined.

## Item 1: `LawfulBEq R` from `DecidableEq R` (the easier win)

### Problem

Code that wants to call `CMvPolynomial`-flavored operations under a
`DecidableEq R`-only context has to manually rebuild the
`BEq R` + `LawfulBEq R` instances every time. Example from
`HonestRoundProofs.lean:407-422`:

```lean
-- Force the same `==` that `generateHonestTranscript` uses.
letI : BEq 𝔽 := instBEqOfDecidableEq (α := 𝔽)
-- Make it lawful using decide.
letI : LawfulBEq 𝔽 :=
{ rfl := by intro a; simp
  eq_of_beq := by
    intro a b h
    have hdec : decide (a = b) = true := by
      simpa [instBEqOfDecidableEq] using h
    have : (decide (a = b) = true) = (a = b) := by simp
    have hab : a = b := by simpa [this] using hdec
    exact hab }
```

### Two possible upstream fixes

**Option A — provide a named helper instance.**

Add a helper that downstream callers can `letI` in one line, instead of
hand-rebuilding:

```lean
namespace CPoly

/-- A canonical `LawfulBEq` instance derived from `DecidableEq`. Intended for
    `letI` use at call sites that need to satisfy `CMvPolynomial`'s
    `BEq`/`LawfulBEq` constraints from a `DecidableEq`-only context. -/
def lawfulBEqOfDecidableEq {α : Type*} [DecidableEq α] :
    @LawfulBEq α (instBEqOfDecidableEq) := by
  refine ⟨?_, ?_⟩
  · intro a; simp [instBEqOfDecidableEq]
  · intro a b h
    simpa [instBEqOfDecidableEq] using of_decide_eq_true h

end CPoly
```

Don't make this a `@[instance]` — it would conflict with other `BEq` paths.
The win is just that downstream call sites become `letI := CPoly.lawfulBEqOfDecidableEq`.

**Option B — change CompPoly signatures to take `DecidableEq R` directly.**

The deeper fix: replace `[BEq R] [LawfulBEq R]` in `CMvPolynomial` API surfaces
with `[DecidableEq R]` (and synthesize `BEq`/`LawfulBEq` internally where
needed). This is a bigger refactor but eliminates the plumbing entirely.

**Recommendation:** ship A first (small, unblocks local cleanup), evaluate
whether B is worth the churn separately.

### Local cleanup once Item 1 lands

Replace the hand-rolled `letI : LawfulBEq 𝔽 := { ... }` blocks at the two cited
sites with `letI := CPoly.lawfulBEqOfDecidableEq` (Option A) or remove them
entirely (Option B). The `simp`/`cases` that follow should go through unchanged.

## Item 2: Conditional eval-extensionality on `CMvPolynomial 1 R`

### Problem

`agreement_set_card_le` at `SoundnessLemmas.lean:268` is essentially Schwartz–Zippel
specialised to univariate `CMvPolynomial`s. The crux step needs:

> If `g ≠ h : CMvPolynomial 1 R`, then `g.eval` and `h.eval` disagree somewhere
> (subject to a degree-vs-field-size hypothesis).

The current local proof reaches this via the `MvPolynomial` bridge plus a
hand-rolled count argument over `Finset 𝔽`. Most of that machinery would
collapse if CompPoly exposed a contrapositive eval-ext lemma.

### Why this must be conditional

`x^p` and `x` over `F_p` are different `MvPolynomial`s but agree on every
input. So **unconditional** `(∀ vs, p.eval vs = q.eval vs) → p = q` is false
for finite fields and any general upstream eval-ext lemma must include a
hypothesis ruling this out (degree bound + |R| > degree, or `R` infinite).

### Suggested lemma

```lean
namespace CPoly.CMvPolynomial

/-- **Univariate eval-extensionality (degree-bounded).** Two univariate
    `CMvPolynomial`s that agree on more than `d` points, where `d` bounds the
    degree of their difference, are equal.

    The hypothesis form matches Schwartz–Zippel usage at call sites: callers
    typically have a degree bound on the *difference* polynomial, not on
    `p` and `q` individually. -/
theorem eval_ext_univariate {R : Type*}
    [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]
    {p q : CMvPolynomial 1 R} (d : ℕ)
    (hdeg : (fromCMvPolynomial p - fromCMvPolynomial q).degreeOf 0 ≤ d)
    (hagree : Fintype.card {vs : Fin 1 → R // p.eval vs = q.eval vs} > d) :
    p = q := by
  sorry  -- proof strategy: contrapositive of MvPolynomial Schwartz–Zippel;
         -- bridge via `eval_equiv` and `eq_iff_fromCMvPolynomial`.
```

Variants to consider while drafting:

- **Predicate over `R` not `Fin 1 → R`:** the agreement set is more natural on
  `R` directly; pick whichever shape is easier for the `MvPolynomial` proof
  to bridge to. The local site at `agreement_set_card_le` filters
  `Finset.univ : Finset R`, so an `R`-flavored statement may be more direct.
- **Cardinality vs membership:** an alternative is to use `Set.ncard` over
  `Set.univ : Set R` and a `d.succ ≤ …` form. Whichever matches the
  Schwartz–Zippel surface CompPoly already exposes.
- **Multivariate generalisation:** the natural multivariate form would
  parameterise over `Fin n → R` agreement; cleaner to ship the univariate
  case first and generalise if a caller needs it.

### Natural home

[`CompPoly/Multivariate/CMvPolynomialEvalLemmas.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/master/CompPoly/Multivariate/CMvPolynomialEvalLemmas.lean),
alongside the existing `eval_zero`, `eval_one`, `eval_C`, `eval_add`,
`eval_mul`, `eval_pow` lemmas. (The user's local branch
`z-tech/add_eval_lemmas` already has staged additions of `eval_neg` /
`eval_sub` in that file — see `CompPoly` commit `a4d20db` — so the file is
already being extended.)

### Local cleanup once Item 2 lands

Refactor [`agreement_set_card_le`](../Properties/Lemmas/SoundnessLemmas.lean#L268)
to use `eval_ext_univariate` via its contrapositive. The local `agreeF`
bookkeeping plus the function-space-to-scalar mapping should compress
substantially.

## How the CompPoly agent verifies

1. Land the additions in CompPoly (one PR per item, or combined).
2. Note the new commit SHA.
3. Hand the SHA back. We'll bump the pin in this repo's `lakefile.lean`
   (currently `01609714fa06e8f83485fe663f953d59c229477f`), rebuild, then
   land the local cleanups in `HonestRoundProofs.lean` and `SoundnessLemmas.lean`
   in a follow-up PR.

The integration smoke test is `lake build SumcheckProtocol` here — should stay
green after the bump, before the local cleanup is even applied.

## Existing in-progress work on CompPoly

There's an open local branch `z-tech/add_eval_lemmas` in
`~/Documents/GitHub/CompPoly` (most recent local commit: `a4d20db chkpt` from
2026-04-12; the remote `origin/z-tech/add_eval_lemmas` has merged master in
since but added no new eval lemmas). The two `chkpt`-era additions there are:

- `CMvPolynomialEvalLemmas.lean`: adds `eval_zero`, `eval_one`, `eval_C`,
  `eval_neg`, `eval_sub`. Useful and complementary — keep.
- `Lawful.lean`: adds mixed-arity `HAdd`/`HSub`/`HMul` instances. Unrelated to
  this handoff but not in the way either.

The CompPoly agent can build Items 1 and 2 either on top of that branch (after
syncing with origin) or on a fresh branch off upstream master — both work.
