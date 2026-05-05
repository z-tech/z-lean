# Aleph target: MCA-at-zero simplification

Target: `MutualCorrelatedAgreement_zero_simplify` in
`LinearCodes/MCA/CAImplications.lean`.

## What you're proving

```lean
theorem MutualCorrelatedAgreement_zero_simplify
    {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA)
    (us : Fin ℓ → (Fin n → F)) :
    seedProb (S := S) (fun x => G.combine x us ∈ c ∧ ∃ j : Fin ℓ, us j ∉ c)
      ≤ εMCA 0
```

This is a useful corollary of `MutualCorrelatedAgreement` — at `γ = 0`,
the MCA bad event reduces to plain code membership (since `T` must be
all of `[n]`).

## Definitions in scope

```lean
def MutualCorrelatedAgreement G c εMCA := ∀ us γ, 0 ≤ γ → γ ≤ 1 →
  seedProb (S := S) (fun x =>
    ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
  ≤ εMCA γ

def InRestrictedCode c T u := ∃ v ∈ c, ∀ i ∈ T, v i = u i
```

## Proof strategy

Apply `hMCA us 0` (with the proofs `0 ≤ 0` and `0 ≤ 1`), then
`seedProb_mono` to deduce the simplified form.

Specifically, show that:
```
(G.combine x us ∈ c ∧ ∃ j, us j ∉ c)
  →
(∃ T, T.card ≥ n*(1-0) ∧ InRestrictedCode c T (G.combine x us) ∧
                         ∃ j, ¬ InRestrictedCode c T (us j))
```

Take `T := Finset.univ`. The conditions become:
* `T.card ≥ n * (1 - 0) = n`. Since `T = univ`, `T.card = n`. ✓
* `InRestrictedCode c univ (G.combine x us)` ↔ `G.combine x us ∈ c` (via
  `inRestrictedCode_univ_iff`). ✓ from hypothesis.
* `∃ j, ¬ InRestrictedCode c univ (us j)` ↔ `∃ j, us j ∉ c` (via
  `inRestrictedCode_univ_iff`). ✓ from hypothesis.

## Helper lemmas already proved

* `seedProb_mono : (∀ x, P x → Q x) → seedProb P ≤ seedProb Q`
* `inRestrictedCode_univ_iff : InRestrictedCode c Finset.univ u ↔ u ∈ c`
* `Finset.card_univ`, `Fintype.card_fin`

## Suggested proof

```lean
intro
have h := hMCA us 0 (le_refl 0) zero_le_one
apply le_trans _ h
apply seedProb_mono
intro x ⟨h_in, j, hj⟩
refine ⟨Finset.univ, ?_, ?_, j, ?_⟩
· -- T.card ≥ n*(1-0) = n
  rw [Finset.card_univ, Fintype.card_fin]
  push_cast
  linarith
· rw [inRestrictedCode_univ_iff]; exact h_in
· rw [inRestrictedCode_univ_iff]; exact hj
```

## Pre-flight check

`lake build LinearCodes.MCA.CAImplications` should build with one
expected `sorry` (the other staged Aleph target `MCA_implies_CA` at
line 23).
