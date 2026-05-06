/-
# List-decoding agreement / CA domains

Group B of §6.2: predicates and basic properties for list-decoding domains.
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.ListDecoding

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} {n ℓ L : ℕ}

/-! ### B1: List agreement domain -/

/-- B1: `T` is an L-list-agreement domain for `u` and `c` if there are L
distinct codewords agreeing with `u` on every coordinate of `T`. -/
def IsListAgreementDomain (c : Submodule F (Fin n → F)) (u : Fin n → F)
    (T : Finset (Fin n)) (L : ℕ) : Prop :=
  ∃ vs : Fin L → (Fin n → F), (∀ k, vs k ∈ c) ∧
    Function.Injective vs ∧ ∀ k, ∀ i ∈ T, vs k i = u i

/-! ### B2: List CA domain -/

/-- B2: `T` is an L-list-CA domain if for every row `j`, there are L distinct
codewords agreeing with `us j` on `T`. -/
def IsListCADomain (c : Submodule F (Fin n → F)) (us : Fin ℓ → (Fin n → F))
    (T : Finset (Fin n)) (L : ℕ) : Prop :=
  ∀ j : Fin ℓ, IsListAgreementDomain c (us j) T L

/-! ### B3: Monotonicity -/

/-- B3a: `IsListAgreementDomain` is antitone in `T`. -/
theorem IsListAgreementDomain.mono
    {c : Submodule F (Fin n → F)} {u : Fin n → F}
    {T T' : Finset (Fin n)} (hT : T' ⊆ T) {L : ℕ}
    (h : IsListAgreementDomain c u T L) :
    IsListAgreementDomain c u T' L := by
  obtain ⟨vs, h_mem, h_inj, h_agree⟩ := h
  refine ⟨vs, h_mem, h_inj, ?_⟩
  intro k i hi'
  exact h_agree k i (hT hi')

/-- B3b: `IsListCADomain` is antitone in `T`. -/
theorem IsListCADomain.mono
    {c : Submodule F (Fin n → F)} {us : Fin ℓ → (Fin n → F)}
    {T T' : Finset (Fin n)} (hT : T' ⊆ T) {L : ℕ}
    (h : IsListCADomain c us T L) :
    IsListCADomain c us T' L := fun j => (h j).mono hT

/-- B3c: `IsListAgreementDomain` is antitone in `L`. -/
theorem IsListAgreementDomain.mono_L
    {c : Submodule F (Fin n → F)} {u : Fin n → F}
    {T : Finset (Fin n)} {L L' : ℕ} (hL : L' ≤ L)
    (h : IsListAgreementDomain c u T L) :
    IsListAgreementDomain c u T L' := by
  obtain ⟨vs, h_mem, h_inj, h_agree⟩ := h
  refine ⟨vs ∘ Fin.castLE hL, ?_, ?_, ?_⟩
  · intro k; exact h_mem _
  · intro a b hab; exact Fin.castLE_injective hL (h_inj hab)
  · intro k i hi; exact h_agree _ i hi

/-! ### B4: List-CA from list-combine agreement (the heavy stub) -/

/-- B4 specialised to `L = 1`. Reduces to Phase A's
`isCADomain_of_all_combines_agree` (in `LinearCodes/MCA/MaximalDomain.lean`):
since `IsListAgreementDomain c u T 1` is equivalent (via the constant
`Fin 1 → _` family) to `IsAgreementDomain c u T`, we just plug into the
single-codeword theorem. -/
theorem isListCADomain_of_all_combines_agree_one
    [DecidableEq S] [Fintype S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)}
    (us : Fin ℓ → (Fin n → F))
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (T : Finset (Fin n))
    (h_agree : ∀ j, IsAgreementDomain c (G.combine (xs j) us) T) :
    IsListCADomain c us T 1 := by
  -- Phase A gives us a per-row witness codeword.
  have h_CA : IsCADomain c us T :=
    isCADomain_of_all_combines_agree G hG_MDS us xs h_distinct T h_agree
  intro j
  obtain ⟨v, hv_mem, hv_agree⟩ := h_CA j
  refine ⟨fun _ => v, ?_, ?_, ?_⟩
  · intro _; exact hv_mem
  · intro a b _; exact Subsingleton.allEq a b
  · intro _ i hi; exact hv_agree i hi


/-- B4: Analog of `isCADomain_of_all_combines_agree` for list-decoding.

**STRATEGY (not yet formalized — see `LinearCodes/MCA/ListDecodingDomains.lean`).**
Let `vs j : Fin L → (Fin n → F)` be the agreement-list witnesses from
`h_agree j` (codewords agreeing with `G.combine (xs j) us` on `T`, injective in
`Fin L`).

* **Agreement on `T`.** For each `k : Fin L`, set `cs_k j := vs j k` and apply
  `exists_cstars_of_MDS` (or `exists_cstars_list_of_MDS` with the constant
  choice `choose_k j := k`) to obtain `cstars_k : Fin ℓ → (Fin n → F)` with
  `cstars_k j ∈ c` and `G.combine (xs j) cstars_k = vs j k`. Then on `T`,
  `G.combine (xs j) cstars_k i = vs j k i = G.combine (xs j) us i`, so by MDS
  rigidity (`isCADomain_of_combines_agree`), `cstars_k j i = us j i` for all
  `j` and `i ∈ T`. In particular `cstars_k j' i = us j' i` for any `j'`.

* **Injectivity (the hard part).** Define `ws_{j'} k := cstars_k j'`. The
  obstacle is that the projection `k ↦ cstars_k j'` may collapse: a-priori
  it's a fixed `F`-linear functional `∑_j (M⁻¹)_{j' j} • vs_j k` of the family
  `(vs_j k)_j`, where `M_{i j} := G (xs i) j` is the MDS evaluation matrix.
  To force `L` distinct outputs, one must:
  1. Show the `j'`-th row of `M⁻¹` is nonzero (every row of an invertible
     matrix is nonzero), so `(M⁻¹)_{j' j₀} ≠ 0` for some `j₀ = j₀(j')`.
  2. Use the *single-coordinate-varying* construction: instead of
     `cs_k j := vs j k`, set `cs_k j₀ := vs j₀ k` and `cs_k j := vs j 0` for
     `j ≠ j₀`. Apply `exists_cstars_of_MDS` to get `cstars'_k` with
     `cstars'_k j' = (M⁻¹)_{j' j₀} • vs_{j₀} k + (constant in k)`.
  3. Then `k ↦ cstars'_k j'` is injective (since `(M⁻¹)_{j' j₀} ≠ 0` and
     `vs_{j₀}` is injective).

  This requires exposing the `M⁻¹` formula for `cstars`, which is currently
  hidden inside `exists_cstars_of_MDS`. A cleaner formalization would
  refactor `exists_cstars_of_MDS` to expose linearity of `cstars` in `cs`,
  then re-derive injectivity from that.

  Estimated effort: ~80-150 lines of additional infrastructure (matrix-row
  nonvanishing, exposed linearity, the `j₀`-trick construction). -/
theorem isListCADomain_of_all_combines_agree
    [DecidableEq S] [Fintype S]
    (G : Generator F S ℓ) (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)}
    (us : Fin ℓ → (Fin n → F))
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (T : Finset (Fin n)) (L : ℕ)
    (h_agree : ∀ j, IsListAgreementDomain c (G.combine (xs j) us) T L) :
    IsListCADomain c us T L := by
  sorry

/-! ### F2: Cardinality bridge for list-decoding -/

/-- F2: Convert `IsListDecodable c τ L` to a Finset cardinality bound. -/
theorem IsListDecodable.toFinset_card
    [Fintype F]
    {c : Submodule F (Fin n → F)} {τ L : ℕ}
    (h : IsListDecodable c τ L) (u : Fin n → F) :
    {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.ncard ≤ L := h u

end LinearCodes
