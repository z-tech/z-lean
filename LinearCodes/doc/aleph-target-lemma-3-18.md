# Aleph target: BCGM25 Lemma 3.18 forward direction

This is a brief you can hand to Aleph. The target is `MCA_implies_ZeroEvading_at_zero`
in `LinearCodes/MCA/Properties.lean` line 117.

## What you're proving

```lean
theorem MCA_implies_ZeroEvading_at_zero {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) {c : Submodule F (Fin n → F)}
    (h_proper : c < ⊤)
    {εMCA : ℚ → ℚ}
    (hMCA : MutualCorrelatedAgreement G c εMCA) :
    ZeroEvading G (εMCA 0)
```

This is the forward direction of BCGM25 Lemma 3.18 (page 19). The full
lemma is `ε_MCA(0) = ε_ZE`; we're doing `≤` (i.e., `ε_ZE ≤ ε_MCA(0)`).

## Definitions in scope

```lean
def ZeroEvading G ε := ∀ v : Fin ℓ → F, v ≠ 0 →
  seedProb (S := S) (fun x => ∑ j, G x j * v j = 0) ≤ ε

def MutualCorrelatedAgreement G c εMCA := ∀ us γ, 0 ≤ γ → γ ≤ 1 →
  seedProb (S := S) (fun x =>
    ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
      InRestrictedCode c T (G.combine x us) ∧
      ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
  ≤ εMCA γ

def InRestrictedCode c T u := ∃ v ∈ c, ∀ i ∈ T, v i = u i
```

## Proof strategy

Fix nonzero `v : Fin ℓ → F`. We instantiate the MCA bad event at `γ = 0`
with a carefully chosen `U`.

1. **Pick `u ∉ c`.** Exists because `c < ⊤`.
   ```lean
   have h_ne_top : c ≠ ⊤ := h_proper.ne
   obtain ⟨u, hu_not⟩ : ∃ u, u ∉ c := by
     by_contra h; push_neg at h
     exact h_ne_top (Submodule.eq_top_iff'.mpr h)
   ```

2. **Pick `j₀` with `v j₀ ≠ 0`.** Exists because `v ≠ 0`.
   ```lean
   obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
     by_contra h; push_neg at h
     exact hv (funext h)
   ```

3. **Let `U j := v j • u`.**

4. **Apply MCA at `γ = 0`.** Get `seedProb (bad event at γ=0 for U) ≤ εMCA 0`.

5. **Show `{x : G(x)·v = 0} ⊆ {x : MCA bad event}`** using `seedProb_mono`.
   The witness for the bad event is `T = Finset.univ`:
   - `T.card = n`, so `(T.card : ℚ) ≥ n * (1 - 0)` holds.
   - `(G.combine x U)|T ∈ c|T` ⟺ `G.combine x U ∈ c` (via `inRestrictedCode_univ_iff`).
     By the helper `Generator.combine_smul_const`:
     `G.combine x U = (∑ⱼ G(x)ⱼ * vⱼ) • u`.
     If `∑ⱼ G(x)ⱼ * vⱼ = 0` then this equals `0 • u = 0 ∈ c`. ✓
   - `U_{j₀} ∉ c|T` ⟺ `U_{j₀} ∉ c` (via `inRestrictedCode_univ_iff`).
     Suppose `U_{j₀} = v_{j₀} • u ∈ c`. Then by `c.smul_mem (v_{j₀})⁻¹`:
     `(v_{j₀})⁻¹ • (v_{j₀} • u) = u ∈ c` (using `inv_mul_cancel₀ hj₀` and
     `smul_smul`), contradicting `hu_not`. ✓

6. **Conclude:** Combine via `le_trans`.

## Helper lemmas already proved (you can use these)

In `LinearCodes/MCA/Definitions.lean`:
- `Generator.combine_smul_const G x v u : G.combine x (fun j => v j • u) = (∑ j, G x j * v j) • u`
- `Generator.combine_apply` etc.

In `LinearCodes/MCA/SeedProbLemmas.lean`:
- `seedProb_mono : (∀ x, P x → Q x) → seedProb P ≤ seedProb Q`

In `LinearCodes/Algebraic/Restriction.lean`:
- `inRestrictedCode_univ_iff (c) {u} : InRestrictedCode c Finset.univ u ↔ u ∈ c`

## Mathlib hints

* `Submodule.eq_top_iff' : c = ⊤ ↔ ∀ x, x ∈ c`
* `Submodule.smul_mem c (a : F) : x ∈ c → a • x ∈ c` (also `c.smul_mem`)
* `Submodule.zero_mem c : 0 ∈ c`
* `inv_mul_cancel₀ : a ≠ 0 → a⁻¹ * a = 1` (or `mul_inv_cancel₀`)
* `smul_smul : a • b • x = (a * b) • x`
* `zero_smul : (0 : F) • x = 0`
* `one_smul : (1 : F) • x = x`
* `Finset.card_univ`, `Fintype.card_fin`

## Pre-flight check

Run `lake build LinearCodes.MCA.Properties` after edits to verify.

## What to do if you get stuck

* If membership extraction in step 1 doesn't work cleanly, the alternative
  is `Submodule.exists_of_lt_top` if it exists, or `lt_iff_le_and_exists`
  on `SetLike`.
* The `seedProb_mono` reduction in step 5 should work but the inner predicate
  is large — leave a partial proof if the instantiation gets fiddly and we'll
  iterate.
* Don't worry about `let U` — it's just a name. You can `show` the explicit
  form whenever needed.
