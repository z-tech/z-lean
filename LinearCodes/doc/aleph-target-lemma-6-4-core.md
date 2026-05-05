# Aleph target: Lemma 6.4 algebraic core (matrix inversion)

The target is the `sorry` at the first goal of
`maxAgreement_intersection_isMaxCA` in `LinearCodes/MCA/MaximalDomain.lean`
line 76 (Part 1: showing `T` is a CA domain).

## Context

The full theorem `maxAgreement_intersection_isMaxCA` (BCGM25 Lemma 6.4) is
*almost* proved — the maximality argument (Part 2) is fully closed. The
remaining `sorry` is just Part 1: showing `T` is a CA domain.

```lean
theorem maxAgreement_intersection_isMaxCA
    [DecidableEq S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)} {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin ℓ → (Fin n → F))
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (As : Fin ℓ → Finset (Fin n))
    (h_max_agree : ∀ j, IsMaxAgreementDomain c (G.combine (xs j) us) (As j))
    (T : Finset (Fin n)) (h_T_inter : ∀ j, T ⊆ As j)
    (h_T_max_inter : ∀ T₀ : Finset (Fin n), (∀ j, T₀ ⊆ As j) → T₀ ⊆ T)
    (h_T_size : T.card > n - δ_C) :
    IsMaxCADomain c us T
```

## What you need to prove

After the existing setup (extracts `cw j ∈ c` agreeing with
`G.combine (xs j) us` on `T`, plus a uniqueness helper `h_uniq`), the
goal at the `sorry` is:

```
⊢ IsCADomain c us T
-- Unfolds to: ∀ k : Fin ℓ, InRestrictedCode c T (us k)
-- Which is:   ∀ k : Fin ℓ, ∃ v ∈ c, ∀ i ∈ T, v i = us k i
```

## Math (BCGM25 §6.1)

The MDS hypothesis gives invertibility of the matrix `M_{j,k} := G(xs j) k`.
Use this to *solve* for each `us k`:

For each `k ∈ Fin ℓ`, find coefficients `α_{k,1}, ..., α_{k,ℓ} ∈ F` such
that `∑_j α_{k,j} · G(xs j) = e_k` (the k-th standard basis vector of
`F^ℓ`). Existence: M is invertible, so its transpose is too, so any
target vector (including `e_k`) is in the column-span of `G(xs j)`'s.

Define `v_k := ∑_j α_{k,j} • cw j ∈ c`. Then for `i ∈ T`:
```
v_k i = ∑_j α_{k,j} · cw j i
      = ∑_j α_{k,j} · G(xs j)·us i        (since cw j agrees with G.combine on T)
      = ∑_j α_{k,j} · ∑_p G(xs j) p · us p i
      = ∑_p (∑_j α_{k,j} · G(xs j) p) · us p i
      = ∑_p (e_k p) · us p i              (by choice of α_k)
      = us k i ✓
```

## Available helpers

- `Generator.IsMDS.dotMap_zero_at_distinct_seeds_implies_zero`
  in `LinearCodes/MCA/UniqueDecoding.lean` line 220 — kernel triviality
  of the dotMap-at-seeds linear map. This is the M-injective fact.

- The Mathlib infrastructure needed:
  - `LinearMap.injective_iff_surjective` (finite-dim equal-dim)
  - `Matrix.det_ne_zero_iff_isUnit`, `Matrix.isUnit_iff_isUnit_det`,
    `Matrix.mul_nonsing_inv` for matrix inversion
  - Or: build `LinearEquiv.ofBijective` from M's bijectivity, take its
    `.symm`, extract α via `.symm` applied to standard basis.

## Strategy hint: use the dual / transpose

The challenge is that we have M's *injectivity* but want to solve a system
on M^T. Use `LinearEquiv.ofBijective M ⟨inj, surj⟩` to get a LinearEquiv,
then... actually for the right algebraic identity we may need the transpose.

**Alternative formulation that avoids transpose:** use that {G(xs j)}_j
forms a *basis* of `F^ℓ` (since they're ℓ linearly-independent vectors in
dim ℓ). Each `e_k` can be expressed in this basis with coefficients α_{k,j}.

Linear independence of {G(xs j)}: if `∑ j, β_j • G(xs j) = 0`, then for
each coord `p`, `∑ j, β_j · G(xs j) p = 0`. Now show β = 0.

Hmm — this requires showing that the *function* `j ↦ G(xs j) · v` (with
v fixed) is the zero function only when v = 0. We have the dual: if
`v ↦ G.dotMap v (xs j) = 0` for all j, then v = 0 (our existing lemma).

These are dual statements. The bridge: in finite-dim square setting,
M injective ⇔ M^T injective. So {G(xs j)} are linearly independent.

**Cleanest Lean path:** define a helper lemma that extracts this
linear-independence, then use `Module.Basis.mk` or `LinearIndependent` +
`finrank` to get a basis, then use `Basis.sum_repr` or similar.

## What I tried

The general agent got the structural setup right (witness extraction,
maximality contradiction in Part 2) but couldn't navigate the
matrix-inversion plumbing. Part 2 is fully proved already; only Part 1
(the `sorry` at line 76 in MaximalDomain.lean) remains.

## Pre-flight check

`lake build LinearCodes.MCA.MaximalDomain` should succeed with one
warning at the target sorry.
