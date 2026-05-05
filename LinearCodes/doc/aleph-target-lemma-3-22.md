# Aleph target: BCGM25 Lemma 3.22 (MCA implies CA)

The target is `MCA_implies_CA` in `LinearCodes/MCA/CAImplications.lean`.

**Note (2026-05-05):** Aleph correctly identified that the original
statement is false at `ℓ = 0` (vacuous CA premise but non-vacuous bad
event). The statement now has `(hℓ : 0 < ℓ)` as a hypothesis. Use it
where needed (extracting `j₀ : Fin ℓ` for the `∃ j` branch).

## What you're proving

```lean
theorem MCA_implies_CA {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    CorrelatedAgreement G c (fun e _ => εMCA ((e - 1 : ℚ) / n))
```

This is BCGM25 Lemma 3.22 (page 21). It's the "MCA is strictly stronger
than CA" reduction.

## Definitions in scope

```lean
def CorrelatedAgreement G c εCA := ∀ (e t : ℕ), 1 ≤ t → t < e → e ≤ n →
  ∀ (us : Fin ℓ → (Fin n → F)),
    (∀ i : Fin ℓ, ∀ codeword ∈ c, e ≤ hammingDistance (us i) codeword) →
    seedProb (S := S) (fun x =>
      ∃ codeword ∈ c, hammingDistance (G.combine x us) codeword ≤ e - t)
    ≤ εCA e t

def MutualCorrelatedAgreement G c εMCA := ∀ us γ, 0 ≤ γ → γ ≤ 1 →
  seedProb (S := S) (fun x =>
    ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
  ≤ εMCA γ

def InRestrictedCode c T u := ∃ v ∈ c, ∀ i ∈ T, v i = u i
def hammingDistance u v := (Finset.univ.filter fun i => u i ≠ v i).card
def agreementSet u v := Finset.univ.filter fun i => u i = v i
```

## Proof strategy

Fix `e t : ℕ` with `1 ≤ t`, `t < e`, `e ≤ n`. Fix `us` with row distance
≥ `e` to every codeword. Goal:
```
seedProb (∃ codeword ∈ c, hammingDistance (G.combine x us) codeword ≤ e - t)
  ≤ εMCA ((e − 1) / n)
```

**Step 1.** Apply MCA at `γ := (e − 1 : ℚ) / n`. To use `hMCA`, we need
`0 ≤ γ` and `γ ≤ 1`:
* `0 ≤ (e − 1) / n` from `e ≥ 2` (since `t ≥ 1, t < e`) and `n ≥ 0`.
* `(e − 1) / n ≤ 1` from `e ≤ n + 1` (we have `e ≤ n`) and `n > 0`
  (since otherwise `e ≤ 0`, contradicting `e ≥ 2`). Use
  `div_le_one_of_le` after establishing `n > 0`.

**Step 2.** Reduce via `seedProb_mono`: show that
```
(∃ codeword ∈ c, hammingDistance (G.combine x us) codeword ≤ e − t)
  →
(∃ T : Finset (Fin n), T.card ≥ n * (1 − γ) ∧
   InRestrictedCode c T (G.combine x us) ∧
   ∃ j, ¬ InRestrictedCode c T (us j))
```

For the witness, take `T := agreementSet (G.combine x us) codeword`.

**Step 3.** Verify the witness conditions:

* **`(T.card : ℚ) ≥ n * (1 − γ)`.** Compute
  ```
  T.card + hammingDistance (G.combine x us) codeword = n
  ```
  (via `agreementSet_card_add_hammingDistance`). So
  `T.card = n − hd ≥ n − (e − t)` (using `hd ≤ e − t`). And
  `n − (e − t) ≥ n − (e − 1) = n − e + 1 = n · (1 − (e−1)/n) = n · (1 − γ)`.
  In ℚ: `T.card ≥ n · (1 − γ)`. ✓

* **`InRestrictedCode c T (G.combine x us)`.** By definition, T is the
  agreement set, so `(G.combine x us) i = codeword i` for `i ∈ T`. The
  witness for `InRestrictedCode` is `codeword ∈ c` itself.

* **`∃ j, ¬ InRestrictedCode c T (us j)`.** This is the subtle step. By
  hypothesis, every row `us j` has distance `≥ e` from every codeword
  in `c`. Suppose for contradiction `∀ j, InRestrictedCode c T (us j)`,
  i.e., `∀ j, ∃ c' ∈ c, ∀ i ∈ T, c' i = us j i`. Then
  `agreementSet (us j) c' ⊇ T`, so `|agreement| ≥ |T| ≥ n − e + 1`,
  hence `hammingDistance (us j) c' ≤ n − |T| ≤ e − 1 < e`,
  contradicting the row-distance hypothesis.

  Actually we just need *some* `j` to fail. Pick any `j` (use `Fin ℓ`'s
  inhabitedness — but if `ℓ = 0` the conclusion is vacuous; handle that
  edge case via `Nat.eq_zero_or_pos`).

  Actually re-examine: the "∃j" form means we exhibit one. Since the
  argument applies to *all* j, just pick `j := ⟨0, ?⟩` if `0 < ℓ`; if
  `ℓ = 0`, the original closeness condition is vacuous (us is empty),
  so `G.combine x us` reduces to a sum over empty, which is `0`. Then
  `∃ codeword ∈ c, hammingDistance 0 codeword ≤ e − t` requires `0 ∈ c`
  (yes) with `hammingDistance 0 0 = 0 ≤ e − t`. So the bad event always
  triggers. But the MCA side at `ℓ = 0` is also vacuous in `∃ j`, so
  the bound doesn't apply. Hmm — `ℓ = 0` is a degenerate case worth
  flagging.

  Let me just assume `0 < ℓ` is available or handle the edge case. If
  needed, add `[Nonempty (Fin ℓ)]` or do `rcases Nat.eq_zero_or_pos ℓ`.

**Step 4.** Conclude via `seedProb_mono` + `hMCA`'s bound.

## Helper lemmas already proved

* `agreementSet_card_add_hammingDistance u v : (agreementSet u v).card + hammingDistance u v = n`
* `agreementSet_self`, `agreementSet_comm`
* `seedProb_mono : (∀ x, P x → Q x) → seedProb P ≤ seedProb Q`
* `inRestrictedCode_iff`, `inRestrictedCode_of_mem`

## Mathlib hints

* `div_le_one`, `div_le_one_of_le`
* `Nat.cast_le`, `Nat.cast_sub`
* `Finset.mem_filter`
* `linarith`, `nlinarith` for the rational inequalities

## Edge cases to flag

* `ℓ = 0`: vacuously trivial bad event. May need a case split.
* `n = 0`: `e ≤ 0`, contradicting `e ≥ 2`, so this case is excluded by
  hypotheses (good).

## Pre-flight check

Run `lake build LinearCodes.MCA.CAImplications` to verify.

## What to do if you get stuck

* The `T.card ≥ n · (1 − γ)` rational arithmetic is the most likely
  sticking point. Compute step by step rather than using `nlinarith`
  blindly. `Nat.cast` chains can be finicky.
* If the `∃ j` step is awkward, return a partial proof with that
  specific obstacle marked and we'll iterate.
