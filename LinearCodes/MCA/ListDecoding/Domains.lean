/-
# List-decoding agreement / CA domains

Group B of the BCGM25 §6.2 decomposition. Defines the list-version of the
agreement-domain predicates from `UniqueDecoding.lean` and proves their
basic monotonicity and constructive-equivalence properties.

Key contents:
* `IsListAgreementDomain c u T L` — `T` admits `L` distinct codewords of
  `c` all agreeing with the received word `u` on `T`.
* `IsListCADomain c us T L` — the same, lifted to `ℓ` rows: every column
  `us j` admits `L` distinct codewords agreeing on `T`.
* `IsListAgreementDomain.mono`, `.mono_L`, `IsListCADomain.mono` —
  shrinking `T` or `L` preserves the predicate.
* `isListCADomain_of_all_combines_agree(_one)` — derive an `IsListCADomain`
  from a per-row family of `L` candidates.

Depends on `LinearCodes.MCA.UniqueDecoding`, `LinearCodes.MCA.ListDecoding.Core`,
and `LinearCodes.MCA.Case2.*`.
-/

import LinearCodes.MCA.UniqueDecoding
import LinearCodes.MCA.ListDecoding.Core
import LinearCodes.MCA.Case2.MDSBridge


-- File-level `variable` block is used by most theorems but legitimately
-- unused in a few. Suppression kept rather than narrowing per-theorem.
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

**STRATEGY (not yet formalized — see `LinearCodes/MCA/ListDecoding/Domains.lean`).**
Let `vs j : Fin L → (Fin n → F)` be the agreement-list witnesses from
`h_agree j` (codewords agreeing with `G.combine (xs j) us` on `T`, injective in
`Fin L`).

* **Agreement on `T`.** For each `k : Fin L`, set `cs_k j := vs j k` and apply
  `exists_cstars_of_MDS` to obtain `cstars_k : Fin ℓ → (Fin n → F)` with
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
  classical
  -- Handle the trivial case L = 0 first: every empty function works.
  rcases Nat.eq_zero_or_pos L with hL0 | hL_pos
  · subst hL0
    intro j'
    refine ⟨fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0⟩
    intro a; exact a.elim0
  -- From here on, L ≥ 1, so `(0 : Fin L)` exists as `⟨0, hL_pos⟩`.
  let zeroL : Fin L := ⟨0, hL_pos⟩
  -- Choose, for each row index j, a list `vs j : Fin L → (Fin n → F)` of L
  -- distinct codewords agreeing with `G.combine (xs j) us` on T.
  choose vs hvs_mem hvs_inj hvs_agree using h_agree
  -- The MDS evaluation matrix M_{k j} := G (xs k) j is invertible.
  set M : Matrix (Fin ℓ) (Fin ℓ) F := fun k j => G (xs k) j with hM_def
  -- Step (1): show M is a unit (so that M⁻¹ exists), via MDS rigidity.
  have hM_inj : Function.Injective M.mulVec := by
    intro v w hvw
    have h_diff : v - w = 0 := by
      apply hG_MDS.dotMap_distinct_seeds_eq_zero xs h_distinct
      intro i
      have hM_diff : M.mulVec (v - w) = 0 := by
        rw [Matrix.mulVec_sub, hvw, sub_self]
      have h_at_i : M.mulVec (v - w) i = 0 := by
        rw [hM_diff]; rfl
      have h_unfold : M.mulVec (v - w) i = ∑ j, G (xs i) j * (v j - w j) := by
        show ∑ j, G (xs i) j * (v - w) j = ∑ j, G (xs i) j * (v j - w j)
        refine Finset.sum_congr rfl ?_
        intro j _; rfl
      rw [h_unfold] at h_at_i
      simpa [Generator.dotMap_apply] using h_at_i
    exact sub_eq_zero.mp h_diff
  have hM_unit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdet_unit : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hM_unit
  -- M⁻¹ * M = 1 and M * M⁻¹ = 1.
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet_unit
  have hMinvM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet_unit
  -- Now prove the main goal.
  intro j'
  -- Step (2): find j₀ : Fin ℓ such that (M⁻¹) j' j₀ ≠ 0.
  -- (Every row of M⁻¹ is nonzero because M⁻¹ * M = 1.)
  have h_row_nonzero : ∃ j₀ : Fin ℓ, M⁻¹ j' j₀ ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    -- Then (M⁻¹ * M) j' j' = ∑ j₀, M⁻¹ j' j₀ * M j₀ j' = 0, but should be 1.
    have h_sum_zero : ∑ j₀ : Fin ℓ, M⁻¹ j' j₀ * M j₀ j' = 0 := by
      apply Finset.sum_eq_zero
      intro j₀ _
      rw [h_all j₀, zero_mul]
    have h_one_eq : (M⁻¹ * M) j' j' = (1 : Matrix (Fin ℓ) (Fin ℓ) F) j' j' := by
      rw [hMinvM]
    rw [Matrix.mul_apply] at h_one_eq
    rw [h_sum_zero] at h_one_eq
    rw [Matrix.one_apply_eq] at h_one_eq
    exact (one_ne_zero h_one_eq.symm)
  obtain ⟨j₀, hj₀_ne⟩ := h_row_nonzero
  -- Step (3): construct, for each `k : Fin L`, the witness codeword `w k : Fin n → F`
  -- via MDS-inversion on the input list `cs k : Fin ℓ → (Fin n → F)` defined by
  -- `cs k jₛ := vs j₀ k` if jₛ = j₀, else `cs k jₛ := vs jₛ zeroL`.
  -- The witness codeword `w k` is then `cstars_k j' = ∑ jₛ, M⁻¹ j' jₛ • cs k jₛ`.
  -- Define cs k jₛ explicitly (using `if` so we can compute).
  let cs : Fin L → Fin ℓ → (Fin n → F) :=
    fun k jₛ => if jₛ = j₀ then vs j₀ k else vs jₛ zeroL
  -- Define cstars_k jᵣ := ∑ jₛ, M⁻¹ jᵣ jₛ • cs k jₛ. We only care about jᵣ = j'.
  -- The witness for row j' at list index k:
  let w : Fin L → (Fin n → F) :=
    fun k => ∑ jₛ : Fin ℓ, M⁻¹ j' jₛ • cs k jₛ
  -- Prove agreement on T, injectivity, and codeword membership.
  refine ⟨w, ?_, ?_, ?_⟩
  · -- Codeword membership: each w k is a finite F-linear combination of codewords.
    intro k
    refine Submodule.sum_mem _ ?_
    intro jₛ _
    refine Submodule.smul_mem _ _ ?_
    -- cs k jₛ ∈ c.
    show cs k jₛ ∈ c
    simp only [cs]
    by_cases hjs : jₛ = j₀
    · rw [hjs]; simp [hvs_mem j₀ k]
    · simp [hjs, hvs_mem jₛ zeroL]
  · -- Injectivity: `w` is injective in k.
    -- The map k ↦ w k decomposes as
    --   w k = (M⁻¹ j' j₀) • vs j₀ k + (∑_{jₛ ≠ j₀} M⁻¹ j' jₛ • vs jₛ zeroL)
    -- The second sum is constant in k, and the leading coefficient is nonzero.
    -- So w k₁ = w k₂ ⇒ vs j₀ k₁ = vs j₀ k₂ ⇒ k₁ = k₂.
    intro k₁ k₂ hk
    -- Compute w k₁ - w k₂.
    have h_diff : w k₁ - w k₂ = M⁻¹ j' j₀ • (vs j₀ k₁ - vs j₀ k₂) := by
      simp only [w, cs]
      ext i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.smul_apply]
      -- LHS: ∑ jₛ, M⁻¹ j' jₛ * (if jₛ = j₀ then vs j₀ k₁ i else vs jₛ zeroL i)
      --    - ∑ jₛ, M⁻¹ j' jₛ * (if jₛ = j₀ then vs j₀ k₂ i else vs jₛ zeroL i)
      -- = ∑ jₛ, M⁻¹ j' jₛ * ((if jₛ = j₀ then vs j₀ k₁ i else vs jₛ zeroL i)
      --                    - (if jₛ = j₀ then vs j₀ k₂ i else vs jₛ zeroL i))
      rw [← Finset.sum_sub_distrib]
      -- Push the `i` argument inside the `if`s so each summand is over scalars.
      have h_pull : ∀ x : Fin ℓ,
          (if x = j₀ then vs j₀ k₁ else vs x zeroL) i =
            (if x = j₀ then vs j₀ k₁ i else vs x zeroL i) := by
        intro x; by_cases hx : x = j₀
        · rw [if_pos hx, if_pos hx]
        · rw [if_neg hx, if_neg hx]
      have h_pull' : ∀ x : Fin ℓ,
          (if x = j₀ then vs j₀ k₂ else vs x zeroL) i =
            (if x = j₀ then vs j₀ k₂ i else vs x zeroL i) := by
        intro x; by_cases hx : x = j₀
        · rw [if_pos hx, if_pos hx]
        · rw [if_neg hx, if_neg hx]
      simp_rw [h_pull, h_pull']
      rw [Finset.sum_eq_single j₀]
      · simp; ring
      · intro jₛ _ hjs
        simp [hjs]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hw_eq : w k₁ - w k₂ = 0 := by rw [hk]; simp
    rw [hw_eq] at h_diff
    have hsmul_zero : M⁻¹ j' j₀ • (vs j₀ k₁ - vs j₀ k₂) = 0 := h_diff.symm
    -- M⁻¹ j' j₀ ≠ 0, so vs j₀ k₁ - vs j₀ k₂ = 0, so vs j₀ k₁ = vs j₀ k₂.
    have hvs_eq : vs j₀ k₁ - vs j₀ k₂ = 0 := by
      by_contra hne
      have : M⁻¹ j' j₀ • (vs j₀ k₁ - vs j₀ k₂) ≠ 0 := by
        intro h
        apply hne
        have := smul_eq_zero.mp h
        rcases this with h1 | h2
        · exact (hj₀_ne h1).elim
        · exact h2
      exact this hsmul_zero
    have : vs j₀ k₁ = vs j₀ k₂ := sub_eq_zero.mp hvs_eq
    exact hvs_inj j₀ this
  · -- Agreement on T: w k i = us j' i for all k and i ∈ T.
    -- The cleanest path: use the existing MDS-inversion machinery
    -- via `exists_cstars_of_MDS` + `isCADomain_of_combines_agree`.
    -- For each k, apply `exists_cstars_of_MDS` to the seed-indexed input
    -- `cs k : Fin ℓ → (Fin n → F)` (which lies in c at every coord), get
    -- `cstars_k`. The construction in `exists_cstars_of_MDS` uses the same
    -- formula `cstars_k jᵣ = ∑ jₛ, M⁻¹ jᵣ jₛ • cs k jₛ`, so cstars_k j' = w k.
    intro k i hi
    -- Membership of cs k jₛ in c.
    have h_cs_mem : ∀ jₛ : Fin ℓ, cs k jₛ ∈ c := by
      intro jₛ
      simp only [cs]
      by_cases hjs : jₛ = j₀
      · rw [hjs]; simp [hvs_mem j₀ k]
      · simp [hjs, hvs_mem jₛ zeroL]
    -- Apply exists_cstars_of_MDS.
    obtain ⟨cstars, h_cstars_mem, h_cstars_combine⟩ :=
      exists_cstars_of_MDS hG_MDS xs h_distinct (cs k) h_cs_mem
    -- On T, G.combine (xs jᵣ) cstars = cs k jᵣ = G.combine (xs jᵣ) us.
    -- (At T, every cs k jₛ agrees with G.combine (xs jₛ) us by hvs_agree.)
    have h_combines_eq_at_T : ∀ i' ∈ T, ∀ jᵣ : Fin ℓ,
        G.combine (xs jᵣ) us i' = G.combine (xs jᵣ) cstars i' := by
      intro i' hi' jᵣ
      have h1 : G.combine (xs jᵣ) cstars = cs k jᵣ := h_cstars_combine jᵣ
      rw [h1]
      simp only [cs]
      by_cases hjr : jᵣ = j₀
      · rw [hjr]
        simp only
        exact (hvs_agree j₀ k i' hi').symm
      · simp only [if_neg hjr]
        exact (hvs_agree jᵣ zeroL i' hi').symm
    -- Reorder: we need ∀ i' ∈ T, ∀ jᵣ.  isCADomain_of_combines_agree expects this form.
    have h_combines_eq_at_T' : ∀ i' ∈ T, ∀ jᵣ : Fin ℓ,
        G.combine (xs jᵣ) us i' = G.combine (xs jᵣ) cstars i' := h_combines_eq_at_T
    have h_CA_and_eq :=
      isCADomain_of_combines_agree (G := G) hG_MDS (us := us) (cstars := cstars)
        h_cstars_mem xs h_distinct T h_combines_eq_at_T'
    -- The second component gives: ∀ jᵣ i, i ∈ T → cstars jᵣ i = us jᵣ i.
    have h_cstars_eq_us : ∀ jᵣ i, i ∈ T → cstars jᵣ i = us jᵣ i := h_CA_and_eq.2
    -- It remains to show that w k = cstars j', then plug in.
    -- Both equal `∑ jₛ, M⁻¹ j' jₛ • cs k jₛ`. The cstars from `exists_cstars_of_MDS`
    -- is constructed with this formula but we don't have direct access; we need to
    -- prove it equals using uniqueness.
    -- Easier: show `G.combine (xs jᵣ) (fun jᵣ' => w k₁ ...)` ... actually,
    -- use the explicit formula. The `cstars` from `exists_cstars_of_MDS` is by
    -- definition `fun j => ∑ k, M⁻¹ j k • cs k`, which equals `w k` at j = j'.
    -- But we don't have access to this form. Let's prove `w k = cstars j'`
    -- via the `combine` characterization: if ∀ jᵣ, G.combine (xs jᵣ) (Function.update cstars j' (w k)) = ?,
    -- which is more complex than needed.
    --
    -- Simpler: for our concrete formula, just verify directly using
    -- G.combine (xs k') cstars = cs k k' both for cstars and for the explicit
    -- formula, and use MDS injectivity (all_us_mem...).
    -- Construct the explicit witness array w' jᵣ := ∑ jₛ, M⁻¹ jᵣ jₛ • cs k jₛ.
    let w' : Fin ℓ → (Fin n → F) := fun jᵣ => ∑ jₛ : Fin ℓ, M⁻¹ jᵣ jₛ • cs k jₛ
    -- Each w' jᵣ ∈ c.
    have hw'_mem : ∀ jᵣ, w' jᵣ ∈ c := by
      intro jᵣ
      simp only [w']
      refine Submodule.sum_mem _ ?_
      intro jₛ _
      exact Submodule.smul_mem _ _ (h_cs_mem jₛ)
    -- G.combine (xs k') w' = cs k k' for every k'.
    have hw'_combine : ∀ k' : Fin ℓ, G.combine (xs k') w' = cs k k' := by
      intro k'
      funext i'
      have h_id : ∀ k₂ : Fin ℓ, (∑ jᵣ : Fin ℓ, M k' jᵣ * M⁻¹ jᵣ k₂) =
          if k' = k₂ then (1 : F) else 0 := by
        intro k₂
        have := congrFun (congrFun hMM k') k₂
        simpa [Matrix.mul_apply, Matrix.one_apply, M] using this
      rw [Generator.combine_apply]
      have step1 :
          ∑ jᵣ : Fin ℓ, G (xs k') jᵣ *
              ((∑ jₛ : Fin ℓ, M⁻¹ jᵣ jₛ • cs k jₛ) i') =
            ∑ jᵣ : Fin ℓ, ∑ jₛ : Fin ℓ, M k' jᵣ * (M⁻¹ jᵣ jₛ * cs k jₛ i') := by
        refine Finset.sum_congr rfl ?_
        intro jᵣ _
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rfl
      simp only [w'] at step1 ⊢
      rw [step1, Finset.sum_comm]
      have step2 :
          ∑ jₛ : Fin ℓ, ∑ jᵣ : Fin ℓ, M k' jᵣ * (M⁻¹ jᵣ jₛ * cs k jₛ i') =
            ∑ jₛ : Fin ℓ, (∑ jᵣ : Fin ℓ, M k' jᵣ * M⁻¹ jᵣ jₛ) * cs k jₛ i' := by
        refine Finset.sum_congr rfl ?_
        intro jₛ _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro jᵣ _
        ring
      rw [step2]
      simp_rw [h_id]
      rw [Finset.sum_eq_single k']
      · simp
      · intro k₂ _ hk₂
        rw [if_neg (Ne.symm hk₂)]; ring
      · intro h
        exact (h (Finset.mem_univ _)).elim
    -- Now: G.combine (xs k') w' = cs k k' = G.combine (xs k') cstars.
    -- By all_us_mem... (MDS injectivity), w' = cstars (as functions Fin ℓ → (Fin n → F)).
    -- We use `dotMap_distinct_seeds_eq_zero` per coordinate i.
    have hw'_eq_cstars : w' = cstars := by
      funext jᵣ i'
      -- Define z : Fin ℓ → F by z jᵣ := w' jᵣ i' - cstars jᵣ i'.
      -- Then for all k', ∑ jᵣ, G (xs k') jᵣ * z jᵣ = 0.
      set z : Fin ℓ → F := fun jᵣ => w' jᵣ i' - cstars jᵣ i' with hz_def
      have h_zero : ∀ k', G.dotMap z (xs k') = 0 := by
        intro k'
        have h_eq_at : G.combine (xs k') w' i' = G.combine (xs k') cstars i' := by
          rw [hw'_combine k', h_cstars_combine k']
        have h_split :
            (∑ jᵣ : Fin ℓ, G (xs k') jᵣ * (w' jᵣ i' - cstars jᵣ i')) =
              (∑ jᵣ : Fin ℓ, G (xs k') jᵣ * w' jᵣ i')
                - (∑ jᵣ : Fin ℓ, G (xs k') jᵣ * cstars jᵣ i') := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro jᵣ _; ring
        have h_sum_eq :
            ∑ jᵣ : Fin ℓ, G (xs k') jᵣ * w' jᵣ i' =
            ∑ jᵣ : Fin ℓ, G (xs k') jᵣ * cstars jᵣ i' := by
          have h1 : G.combine (xs k') w' i' = ∑ jᵣ : Fin ℓ, G (xs k') jᵣ * w' jᵣ i' := rfl
          have h2 : G.combine (xs k') cstars i' = ∑ jᵣ : Fin ℓ, G (xs k') jᵣ * cstars jᵣ i' := rfl
          rw [← h1, ← h2]; exact h_eq_at
        have h_sub : ∑ jᵣ : Fin ℓ, G (xs k') jᵣ * (w' jᵣ i' - cstars jᵣ i') = 0 := by
          rw [h_split, h_sum_eq, sub_self]
        simpa [Generator.dotMap_apply, hz_def] using h_sub
      have hz_zero : z = 0 :=
        hG_MDS.dotMap_distinct_seeds_eq_zero xs h_distinct h_zero
      have : z jᵣ = 0 := by simpa using congrFun hz_zero jᵣ
      have : w' jᵣ i' - cstars jᵣ i' = 0 := by simpa [hz_def] using this
      exact sub_eq_zero.mp this
    -- Finally, w k = w' j' = cstars j', so w k i = cstars j' i = us j' i.
    have hwk_eq : w k = w' j' := rfl
    rw [hwk_eq, hw'_eq_cstars]
    exact h_cstars_eq_us j' i hi

/-! ### F2: Cardinality bridge for list-decoding -/

/-- F2: Convert `IsListDecodable c τ L` to a Finset cardinality bound. -/
theorem IsListDecodable.toFinset_card
    [Fintype F]
    {c : Submodule F (Fin n → F)} {τ L : ℕ}
    (h : IsListDecodable c τ L) (u : Fin n → F) :
    {v : Fin n → F | v ∈ c ∧ hammingDistance u v ≤ τ}.ncard ≤ L := h u

end LinearCodes
