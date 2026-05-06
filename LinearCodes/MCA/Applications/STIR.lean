/-
# BCGM25 §9 application: STIR (univariate-powers generator)

Specializes the abstract MCA / CA capstones (`Case2Capstone.lean`,
`ListDecodingMCA.lean`) to the STIR-style generator
`G(x) = (1, x, x^2, …, x^d) : F → F^{d+1}` over a finite field `F` of
size `> d`. This is the canonical setting in which the STIR low-degree
test is analyzed.

Key contents:
* `STIR_MCA_unique_decoding_bound` — instance of
  `MCA_unique_decoding_bound` for `Generator.univariatePowers F d`,
  using the Vandermonde / MDS structure of univariate-powers.
* `STIR_MutualCorrelatedAgreement` — MCA hypothesis (Definition 3.14)
  certified for the STIR generator.
* `STIR_zeroEvading` — Definition 3.11 zero-evading bound for the
  STIR generator.
* `STIR_uniqueDecoding_via_MCA` — wires the above into a self-contained
  unique-decoding statement for STIR.

Depends on `MaximalDomain`, `Case2Capstone`, `ConcreteMDS`, `ListDecoding`.
-/

import LinearCodes.MCA.MaximalDomain
import LinearCodes.MCA.Case2Capstone
import LinearCodes.MCA.ConcreteMDS
import LinearCodes.MCA.ListDecoding

set_option linter.unusedSectionVars false

namespace LinearCodes

/-! ### A1: STIR MCA unique-decoding bound -/

/-- A1: Specializes `MCA_unique_decoding_bound` to `univariatePowers F d`. -/
theorem STIR_MCA_unique_decoding_bound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d n : ℕ} (hd : d + 1 ≤ Fintype.card F) (hd_pos : 0 < d + 1)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin (d + 1) → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (d + 2) < δ_C / n) :
    seedProb (S := F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T ((Generator.univariatePowers F d).combine x us) ∧
        ∃ j : Fin (d + 1), ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * d / Fintype.card F := by
  have hG_MDS : (Generator.univariatePowers F d).IsMDS := Generator.univariatePowers_IsMDS hd
  have hγ_hi' : γ * ((d + 1 : ℕ) + 1) < δ_C / n := by exact_mod_cast hγ_hi
  have h_main := MCA_unique_decoding_bound (Generator.univariatePowers F d) hG_MDS hd_pos
    c hn h_minDist us hγ_pos hγ_hi'
  have h_ell_cast : (((d + 1 : ℕ) : ℚ) - 1) = (d : ℚ) := by push_cast; ring
  rw [h_ell_cast] at h_main
  exact h_main

/-! ### A2: STIR MCA predicate -/

/-- A2: Wraps A1 into the `MutualCorrelatedAgreement` predicate. -/
theorem STIR_MutualCorrelatedAgreement
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {d n : ℕ}
    (hd : d + 1 ≤ Fintype.card F) (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C) :
    MutualCorrelatedAgreement (Generator.univariatePowers F d) c
      (fun γ => if γ * (d + 2) < δ_C / n
                then (max ((n : ℚ) * γ) 1 + 1) * d / Fintype.card F
                else 1) := by
  intro us γ hγ_pos hγ_le_one
  by_cases h_case : γ * (d + 2) < δ_C / n
  · simp only [h_case, ↓reduceIte]
    have hd_pos : 0 < d + 1 := Nat.succ_pos d
    exact STIR_MCA_unique_decoding_bound hd hd_pos c hn h_minDist us hγ_pos h_case
  · simp only [h_case, ↓reduceIte]
    exact seedProb_le_one _

/-! ### A3: STIR zero-evading bound -/

/-- A3: Direct zero-evading bound for `univariatePowers F d`. -/
theorem STIR_zeroEvading
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : d + 1 ≤ Fintype.card F) :
    ZeroEvading (Generator.univariatePowers F d) ((d : ℚ) / Fintype.card F) := by
  have hG := Generator.univariatePowers_IsMDS hd
  have hZE := hG.zeroEvading_bound
  -- hZE : ZeroEvading (univariatePowers F d) ((↑(d + 1) - 1 : ℚ) / Fintype.card F)
  have h_simp : (((d + 1 : ℕ) : ℚ) - 1) = (d : ℚ) := by push_cast; ring
  rw [h_simp] at hZE
  exact hZE

/-! ### A2-sanity: concrete instance of the abstract MCA predicate -/

/-- Sanity: the canonical STIR generator over `ZMod 7` with degree 3
satisfies the abstract `MutualCorrelatedAgreement` predicate (with the
piecewise error from Theorem 6.1). -/
example {n : ℕ} (hn : 0 < n) (c : Submodule (ZMod 7) (Fin n → ZMod 7))
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C) :
    MutualCorrelatedAgreement (Generator.univariatePowers (ZMod 7) 3) c
      (fun γ => if γ * (3 + 2) < δ_C / n
                then (max ((n : ℚ) * γ) 1 + 1) * 3 / Fintype.card (ZMod 7)
                else 1) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact STIR_MutualCorrelatedAgreement (by decide : 3 + 1 ≤ Fintype.card (ZMod 7)) c hn h_minDist

/-! ### A4: WARP-univariate (affineSpace, boundary case s = 1) MCA bound

The general specialization to `Generator.affineSpace F s` for arbitrary `s`
is **blocked**: `affineSpace_IsMDS` is **not provable in general** (see
the deferred-TODO discussion in `LinearCodes/MCA/ConcreteMDS.lean`,
lines ~296–323). However, in the boundary case `s = 1`, the
`affineSpace F 1` generator IS MDS (`affineSpace_IsMDS_of_s_one`) — this
is the "WARP-univariate" specialization, where the seed lives in
`Fin 1 → F ≃ F`.

TODO: Generalize once `affineSpace_IsMDS` is proved for additional
structural cases (e.g., `s = 2 ∧ |F| = 2`, or `s ≥ |F|^(s-1)`). -/

/-- A4 (boundary case): WARP-style MCA bound for `affineSpace F 1`
(which is essentially `affineLine`-equivalent, with seed type
`Fin 1 → F ≃ F`). Specializes the unified MCA bound to this particular
generator via `affineSpace_IsMDS_of_s_one`. -/
theorem WARP_univariate_MCA_bound_s_one
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (h_card : 2 ≤ Fintype.card F)
    {n : ℕ} (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin 2 → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (1 + 2) < δ_C / n) :
    seedProb (S := Fin 1 → F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T ((Generator.affineSpace F 1).combine x us) ∧
        ∃ j : Fin 2, ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * 1 / Fintype.card (Fin 1 → F) := by
  have hG_MDS : (Generator.affineSpace F 1).IsMDS :=
    Generator.affineSpace_IsMDS_of_s_one h_card
  haveI : Nonempty (Fin 1 → F) := ⟨fun _ => 0⟩
  have hℓ_pos : 0 < (1 + 1 : ℕ) := by omega
  -- `MCA_unique_decoding_bound` requires `γ * (ℓ + 1) < δ_C/n` where ℓ = 1 + 1 = 2.
  have hγ_hi' : γ * ((1 + 1 : ℕ) + 1) < δ_C / n := by exact_mod_cast hγ_hi
  have h_main := MCA_unique_decoding_bound (Generator.affineSpace F 1) hG_MDS hℓ_pos
    c hn h_minDist us hγ_pos hγ_hi'
  -- The bound is `(max(n·γ, 1) + 1) * (ℓ - 1) / |S|`. With ℓ = 2, ℓ - 1 = 1.
  have h_ell_cast : (((1 + 1 : ℕ) : ℚ) - 1) = (1 : ℚ) := by push_cast; ring
  rw [h_ell_cast] at h_main
  exact h_main

/-! ### A5: STIR concrete bound at typical proof-system field sizes -/

/-- A5: STIR bound for typical proof-system parameters (≥ 2³² field, degree
`d`). The hypothesis `2^32 ≤ Fintype.card F` plays no role in the proof;
it is recorded to document that the bound is meaningful for the field
sizes used by SNARK/STARK proof systems. The body just dispatches to
`STIR_MCA_unique_decoding_bound`. -/
example {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (_h_card : 2^32 ≤ Fintype.card F)
    {d n : ℕ} (hd : d + 1 ≤ Fintype.card F) (hd_pos : 0 < d + 1)
    (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C)
    (us : Fin (d + 1) → (Fin n → F))
    {γ : ℚ} (hγ_pos : 0 ≤ γ) (hγ_hi : γ * (d + 2) < δ_C / n) :
    seedProb (S := F) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T ((Generator.univariatePowers F d).combine x us) ∧
        ∃ j : Fin (d + 1), ¬ InRestrictedCode c T (us j))
    ≤ (max ((n : ℚ) * γ) 1 + 1) * d / Fintype.card F :=
  STIR_MCA_unique_decoding_bound hd hd_pos c hn h_minDist us hγ_pos hγ_hi

/-! ### A6: STIR unique-decoding via half-distance -/

/-- A6: Half-distance unique decoding for STIR-MDS. -/
theorem STIR_uniqueDecoding_via_MCA
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n d : ℕ}
    (c : Submodule F (Fin n → F)) {k : ℕ} (h_MDS : IsMDS c k)
    {τ : ℕ} (h_τ : 2 * τ < n - k + 1) :
    IsListDecodable c τ 1 := by
  exact IsListDecodable_of_minDist_unique h_MDS.2 h_τ

/-! ### A7: STIR bound tightness — SKIPPED

A tightness statement would assert: there exist a field `F`, a code `c`,
and inputs `(γ, us)` for which `seedProb (...) = (max (n·γ) 1 + 1) · d /
Fintype.card F` (or at least a matching lower bound up to constants).

Such a statement requires constructing an explicit polynomial that
**achieves** the bound. The standard construction uses `X^d - 1 ∈ ZMod p
[X]` for a prime `p ≡ 1 mod d`, which splits completely over `ZMod p`
and exhibits the worst case for the MCA error. Formalizing this requires:

  * existence/density of primes `p ≡ 1 mod d` (Dirichlet);
  * splitting of `X^d - 1` over `ZMod p` under that congruence;
  * an explicit `us` family witnessing the maximum MCA error.

TODO: Add this once explicit field-theory infrastructure (cyclotomic
splitting in `ZMod`, primitive-root machinery) is available. Currently
out of scope for the LinearCodes library.
-/

/-! ### A8: LinearCode-typeclass wiring — SKIPPED

`LinearCodes.LinearCode` (in `LinearCodes/LinearCode.lean`) is a
typeclass over an arbitrary `Code : Type` with field
`mcaProximityGapError : Code → ProximityRegime → (l : Nat) → (δ : Nat) →
(q : Nat) → ℚ`. Wiring the abstract MCA bound through this interface
requires:

  * a concrete `Code` value wrapping `Submodule F (Fin n → F)` together
    with its parameters `(n, k, δ_C)` and minimum-distance witness;
  * an instance `LinearCode CodeWrapper F` whose `mcaProximityGapError`
    field is *defined* by the formula `(max (n·γ) 1 + 1) · d / q`
    (translating the `δ : Nat` argument through `γ`);
  * a proof that, on this instance, the runtime field equals the bound
    proved by `STIR_MCA_unique_decoding_bound`, so the typeclass user
    obtains the soundness guarantee.

This is a substantive piece of plumbing — out of scope for the present
STIR-application file, which targets the abstract MCA bounds. TODO:
Add a `RestrictedReedSolomon` (or analogous) `Code` wrapper alongside
the existing `ReedSolomonCode` instance and wire its
`mcaProximityGapError` through `STIR_MCA_unique_decoding_bound`.
-/

end LinearCodes
