/-
# Tensor product of generators

For generators `G : S₁ → F^ℓ₁` and `H : S₂ → F^ℓ₂`, we define their
*tensor product* `G ⊗ H : S₁ × S₂ → F^(ℓ₁ * ℓ₂)` whose induced code is
the tensor product of the two induced codes (in the standard linear-
algebra sense).

The main results are:
* `Generator.tensorProduct` — the tensor-product generator.
* `tensorProduct_dotMap_injective` — injectivity of `dotMap` is preserved
  under tensor product. (No sorry.)
* `tensorProduct_finrank_eq` — wrapper packaging the dimension /
  injectivity preservation in the form expected downstream. (No sorry.)
* `tensorProduct_inducedCode_minDist_at_least` — the classical
  multiplicative bound: the tensor product preserves min-distance
  multiplicatively, `d(G ⊗ H) ≥ d(G) · d(H)`. (Sorry'd; classical proof
  sketched in its docstring.)

## Why no MDS-preservation theorem?

The Singleton-bound MDS property is **not** preserved under tensor
products of arbitrary generators. See the comment block above
`tensorProduct_inducedCode_minDist_at_least` for a counter-example and
discussion. Earlier drafts of this file had a sorry'd
`tensorProduct_IsMDS`; that statement is mathematically false and has
been removed.

This file unblocks the WHIR application, which only requires the
injectivity / dimension half of MDS together with the multiplicative
distance bound.
-/

import LinearCodes.MCA.Examples
import LinearCodes.MCA.ConcreteMDS

set_option linter.unusedSectionVars false

namespace LinearCodes
namespace Generator

/-- Tensor product of two generators. Given `G : S₁ → F^ℓ₁` and
`H : S₂ → F^ℓ₂`, the tensor product is `G ⊗ H : S₁ × S₂ → F^(ℓ₁ * ℓ₂)`
defined coordinate-wise via the canonical equivalence
`Fin ℓ₁ × Fin ℓ₂ ≃ Fin (ℓ₁ * ℓ₂)`. The pair `(s, t)` maps to the function
`k ↦ G(s) j · H(t) i` where `(j, i) = finProdFinEquiv.symm k` (so
`j ∈ Fin ℓ₂` and `i ∈ Fin ℓ₁` after `divNat / modNat`). -/
def tensorProduct {F : Type*} [Field F] {S₁ S₂ : Type*} {ℓ₁ ℓ₂ : ℕ}
    (G : Generator F S₁ ℓ₁) (H : Generator F S₂ ℓ₂) :
    Generator F (S₁ × S₂) (ℓ₁ * ℓ₂) :=
  ⟨fun p k =>
    let p' := finProdFinEquiv.symm k  -- p' : Fin ℓ₁ × Fin ℓ₂
    G p.1 p'.1 * H p.2 p'.2⟩

/-- Pointwise unfold of `tensorProduct`. -/
@[simp] theorem tensorProduct_apply {F : Type*} [Field F]
    {S₁ S₂ : Type*} {ℓ₁ ℓ₂ : ℕ}
    (G : Generator F S₁ ℓ₁) (H : Generator F S₂ ℓ₂)
    (p : S₁ × S₂) (k : Fin (ℓ₁ * ℓ₂)) :
    (G.tensorProduct H) p k =
      G p.1 (finProdFinEquiv.symm k).1 * H p.2 (finProdFinEquiv.symm k).2 := rfl

/-- Reindexing identity: a sum over `Fin (ℓ₁ * ℓ₂)` of a function pulled
back through `finProdFinEquiv.symm` equals the double sum over
`Fin ℓ₁ × Fin ℓ₂`. -/
theorem sum_finProdFinEquiv_symm
    {β : Type*} [AddCommMonoid β] {ℓ₁ ℓ₂ : ℕ}
    (f : Fin ℓ₁ → Fin ℓ₂ → β) :
    ∑ k : Fin (ℓ₁ * ℓ₂), f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      = ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂, f j i := by
  -- Reindex via Fintype.sum_equiv with e := finProdFinEquiv.symm.
  -- This gives: ∑ k, g k = ∑ p, h p where h p = g (finProdFinEquiv p), provided
  -- ∀ k, g k = h (finProdFinEquiv.symm k). With g k = f (..).1 (..).2 and
  -- h p = f p.1 p.2, the witness is `rfl`.
  have h1 : ∑ k : Fin (ℓ₁ * ℓ₂),
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      = ∑ p : Fin ℓ₁ × Fin ℓ₂, f p.1 p.2 := by
    apply Fintype.sum_equiv finProdFinEquiv.symm
    intro k; rfl
  rw [h1, ← Finset.univ_product_univ, Finset.sum_product]

/-- Pointwise expansion of `dotMap` for the tensor product: viewing
`v : Fin (ℓ₁ * ℓ₂) → F` as a matrix `M(j, i) = v(finProdFinEquiv (j, i))`,
the `(s, t)`-th coordinate of `dotMap (G ⊗ H) v` is the bilinear form
`∑ⱼ ∑ᵢ G(s) j · H(t) i · M(j, i)`. -/
theorem tensorProduct_dotMap_apply {F : Type*} [Field F]
    {S₁ S₂ : Type*} {ℓ₁ ℓ₂ : ℕ}
    (G : Generator F S₁ ℓ₁) (H : Generator F S₂ ℓ₂)
    (v : Fin (ℓ₁ * ℓ₂) → F) (p : S₁ × S₂) :
    (G.tensorProduct H).dotMap v p =
      ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂,
        G p.1 j * H p.2 i * v (finProdFinEquiv (j, i)) := by
  rw [Generator.dotMap_apply]
  -- LHS: ∑ k, (G p.1 j_k * H p.2 i_k) * v k where (j_k, i_k) = finProdFinEquiv.symm k.
  -- Step 1: rewrite each summand to make the dependence on `k` go through finProdFinEquiv.symm
  -- explicitly; the `v k = v (finProdFinEquiv (finProdFinEquiv.symm k))` rewrite is needed
  -- so the whole summand is a function of `finProdFinEquiv.symm k`.
  have step1 : ∀ k : Fin (ℓ₁ * ℓ₂),
      (G.tensorProduct H) p k * v k =
        G p.1 (finProdFinEquiv.symm k).1 *
          H p.2 (finProdFinEquiv.symm k).2 *
          v (finProdFinEquiv (finProdFinEquiv.symm k)) := by
    intro k
    rw [tensorProduct_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun k _ => step1 k)]
  -- Now apply the reindexing helper.
  exact sum_finProdFinEquiv_symm
    (fun j i => G p.1 j * H p.2 i * v (finProdFinEquiv (j, i)))

/-! ### Injectivity of the tensor-product `dotMap` -/

/-- If both `G.dotMap` and `H.dotMap` are injective, so is
`(G.tensorProduct H).dotMap`. The proof reshapes a vanishing tensor
combination into "for each `s`, the `H`-combination of the `G`-rows
vanishes", whence the `G`-rows themselves vanish. -/
theorem tensorProduct_dotMap_injective {F : Type*} [Field F]
    {S₁ S₂ : Type*} {ℓ₁ ℓ₂ : ℕ}
    (G : Generator F S₁ ℓ₁) (H : Generator F S₂ ℓ₂)
    (hG : Function.Injective G.dotMap)
    (hH : Function.Injective H.dotMap) :
    Function.Injective (G.tensorProduct H).dotMap := by
  -- Suffices: kernel is trivial.
  rw [dotMap_injective_iff] at hG hH ⊢
  intro v hv
  -- Define the matrix view M(j, i) = v(finProdFinEquiv (j, i)).
  set M : Fin ℓ₁ → Fin ℓ₂ → F := fun j i => v (finProdFinEquiv (j, i)) with hM_def
  -- Reshape hv into the bilinear form via tensorProduct_dotMap_apply.
  have hv' : ∀ p : S₁ × S₂,
      ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂, G p.1 j * H p.2 i * M j i = 0 := by
    intro p
    have hp := hv p
    -- hp : ∑ k, (G.tensorProduct H) p k * v k = 0  (from dotMap_apply unfolding)
    have hexp : (G.tensorProduct H).dotMap v p =
        ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂,
          G p.1 j * H p.2 i * v (finProdFinEquiv (j, i)) :=
      tensorProduct_dotMap_apply G H v p
    -- Reformulate hv at p: rewrite the sum form into the bilinear form.
    have hp' : ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂,
        G p.1 j * H p.2 i * v (finProdFinEquiv (j, i)) = 0 := by
      rw [← hexp]
      simpa [Generator.dotMap_apply] using hp
    -- This is exactly hv' with M unfolded.
    exact hp'
  -- For each s : S₁, define N(s, i) = ∑_j G(s) j * M(j, i).
  set N : S₁ → Fin ℓ₂ → F := fun s i => ∑ j : Fin ℓ₁, G s j * M j i with hN_def
  -- Step 1: For each fixed s, the H-combination of N(s, ·) vanishes for all t.
  have h_NH_zero : ∀ (s : S₁) (t : S₂), ∑ i : Fin ℓ₂, H t i * N s i = 0 := by
    intro s t
    have hp := hv' (s, t)
    -- hp : ∑ j, ∑ i, G s j * H t i * M j i = 0
    -- Want : ∑ i, H t i * (∑ j, G s j * M j i) = 0
    rw [show (∑ i : Fin ℓ₂, H t i * N s i) =
            ∑ i : Fin ℓ₂, ∑ j : Fin ℓ₁, H t i * (G s j * M j i) from ?_]
    · rw [Finset.sum_comm]
      have : ∀ j i, H t i * (G s j * M j i) = G s j * H t i * M j i := by
        intros j i; ring
      simp_rw [this]
      exact hp
    · apply Finset.sum_congr rfl
      intros i _
      rw [hN_def, Finset.mul_sum]
  -- Step 2: By H.dotMap injectivity, N(s, ·) = 0 for each s.
  have h_N_zero : ∀ s : S₁, N s = 0 := by
    intro s
    apply hH
    intro t
    -- Goal: ∑ j, H t j * (N s) j = 0; have h_NH_zero s t exactly says this.
    exact h_NH_zero s t
  -- Step 3: For each i, the G-combination of M(·, i) vanishes for all s.
  have h_GM_zero : ∀ (s : S₁) (i : Fin ℓ₂), ∑ j : Fin ℓ₁, G s j * M j i = 0 := by
    intro s i
    have hN := h_N_zero s
    have := congr_fun hN i
    simpa [hN_def, Pi.zero_apply] using this
  -- Step 4: By G.dotMap injectivity (applied for each fixed i), M(·, i) = 0.
  have h_M_zero : ∀ i : Fin ℓ₂, (fun j => M j i) = 0 := by
    intro i
    apply hG
    intro s
    exact h_GM_zero s i
  -- Step 5: M = 0 entrywise, hence v = 0 entrywise.
  funext k
  obtain ⟨j, i⟩ : Fin ℓ₁ × Fin ℓ₂ := finProdFinEquiv.symm k
  -- Use the reverse equivalence to get k = finProdFinEquiv (j, i).
  have hk : k = finProdFinEquiv (finProdFinEquiv.symm k) := by
    rw [Equiv.apply_symm_apply]
  rw [hk]
  set ji := finProdFinEquiv.symm k with hji_def
  have h_pair : v (finProdFinEquiv ji) = M ji.1 ji.2 := by
    rw [hM_def]
  rw [h_pair]
  have := h_M_zero ji.2
  exact congr_fun this ji.1

/-! ### What the tensor product does (and does NOT) preserve

**Claim (FALSE).** "If `G` and `H` are MDS, so is `G.tensorProduct H`."
This is mathematically *not true* in general, and so we do NOT state
or attempt to prove it.

**Counter-example.** Let `G` and `H` both be `[n, n−1, 2]` MDS codes
(e.g. single parity-check codes; min-distance `n − (n−1) + 1 = 2`).
Their tensor product is a code of length `n²`, dimension `(n−1)²`, and
the actual minimum distance is `d₁ · d₂ = 2 · 2 = 4`. The Singleton
bound for the tensor product would require min-distance at least
`n² − (n−1)² + 1 = (2n − 1) + 1 = 2n`. For any `n ≥ 3`,
`4 < 2n`, so the tensor product fails the Singleton bound and is
**NOT** MDS.

**What is true.** The tensor product preserves:

1. *Dimension / injectivity*: `dim (G ⊗ H).inducedCode = ℓ₁ · ℓ₂`. This
   is captured by `tensorProduct_dotMap_injective` (proved above) and
   re-packaged as `tensorProduct_finrank_eq` below.

2. *Minimum-distance multiplicatively*: if the induced code of `G` has
   min-distance `≥ d₁` and that of `H` has min-distance `≥ d₂`, then
   the induced code of `G ⊗ H` has min-distance `≥ d₁ · d₂`. This is
   `tensorProduct_inducedCode_minDist_at_least`. It is the classical
   tensor-distance theorem; we leave its (multi-page) proof as a
   `sorry` with a detailed proof skeleton in the docstring.

**Migration note.** Earlier versions of this file had a sorry'd
`tensorProduct_IsMDS` theorem. That theorem is provably false; it has
been replaced by the two correct theorems below. Downstream code that
needs MDS-flavoured properties of `G ⊗ H` should:
* use `tensorProduct_dotMap_injective` (or `tensorProduct_finrank_eq`)
  for the dimension half, and
* use `tensorProduct_inducedCode_minDist_at_least` for the (correct,
  multiplicative) distance bound — *not* the Singleton bound.
-/

/-- The tensor product preserves dimension exactly: if `G.dotMap` and
`H.dotMap` are injective, then so is `(G.tensorProduct H).dotMap`,
hence `dim (G ⊗ H).inducedCode = ℓ₁ · ℓ₂`.

This is a packaging wrapper around `tensorProduct_dotMap_injective`.
The existential `φ` in the conclusion is unused (it is supplied as the
zero linear map purely as a convenience for callers that want a
combined "there is a linear-algebraic witness, and dotMap is
injective" form); the genuine content is the injectivity. -/
theorem tensorProduct_finrank_eq
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    {ℓ₁ ℓ₂ : ℕ}
    {G : Generator F S₁ ℓ₁} {H : Generator F S₂ ℓ₂}
    (hG_inj : Function.Injective G.dotMap)
    (hH_inj : Function.Injective H.dotMap) :
    ∃ _φ : (Fin ℓ₁ × Fin ℓ₂ → F) →ₗ[F] (Fin (ℓ₁ * ℓ₂) → F),
      Function.Injective ((G.tensorProduct H).dotMap) :=
  ⟨0, tensorProduct_dotMap_injective G H hG_inj hH_inj⟩

/-- The tensor product preserves min-distance MULTIPLICATIVELY: if `G`
has induced code with min-distance `≥ d₁` and `H` has min-distance
`≥ d₂`, then the tensor-product induced code has min-distance
`≥ d₁ · d₂`. This is the classical *tensor-distance theorem* (NOT the
Singleton bound — for that the tensor would need to be MDS, which it
generally is not; see the comment block above for a counter-example).

**Proof skeleton (classical).** Let `w : S₁ × S₂ → F` be a non-zero
codeword in `(G ⊗ H).inducedCode`. By definition of the induced code
there exists `V : Fin (ℓ₁ * ℓ₂) → F` with `w = (G ⊗ H).dotMap V`.
Define the matrix `M : Fin ℓ₁ → Fin ℓ₂ → F`,
`M j i = V (finProdFinEquiv (j, i))`. By `tensorProduct_dotMap_apply`,

  `w (s, t) = ∑ j ∑ i, G(s) j · H(t) i · M j i`.

Re-bracketing,

  `w (s, t) = ∑ i, H(t) i · (∑ j, G(s) j · M j i) = H.dotMap (μ s) t`,

where `μ s : Fin ℓ₂ → F` is `μ s i := ∑ j, G(s) j · M j i`. So for
each fixed `s`, the *row* `t ↦ w(s, t)` lies in `H.inducedCode`.
Symmetrically, for each fixed `t`, the *column* `s ↦ w(s, t)` is
`G.dotMap (ν t)` for `ν t j := ∑ i, H(t) i · M j i`, hence lies in
`G.inducedCode`.

Step 1. There exists `t₀` such that the column `s ↦ w(s, t₀)` is
non-zero. (Otherwise every entry of `w` would be zero, contradicting
`w ≠ 0`.)

Step 2. The column `s ↦ w(s, t₀)` is a non-zero element of
`G.inducedCode`, so by `hG_dist` it has Hamming weight `≥ d₁`. That
is, `S_row := {s | w(s, t₀) ≠ 0}` has `|S_row| ≥ d₁`.

Step 3. For each `s ∈ S_row`, the row `t ↦ w(s, t)` is non-zero
(witness: `t = t₀`), and lies in `H.inducedCode`, so by `hH_dist` it
has Hamming weight `≥ d₂`. That is, for each `s ∈ S_row`,
`|{t | w(s, t) ≠ 0}| ≥ d₂`.

Step 4. The total support of `w` is the disjoint union over `s` of
`{(s, t) | w(s, t) ≠ 0}`, which has cardinality
`∑_{s ∈ S_row} |{t | w(s, t) ≠ 0}| ≥ |S_row| · d₂ ≥ d₁ · d₂`.

Formalising this requires (a) reindexing `Finset.filter` over
`Fin (ℓ₁ * ℓ₂)` versus `Fin ℓ₁ × Fin ℓ₂` via `finProdFinEquiv`, and
(b) decomposing the support into a disjoint union over rows. Both
steps are routine but verbose; we leave the full Lean proof as
future work. -/
theorem tensorProduct_inducedCode_minDist_at_least
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    {ℓ₁ ℓ₂ : ℕ}
    (G : Generator F S₁ ℓ₁) (H : Generator F S₂ ℓ₂)
    {d₁ d₂ : ℕ}
    (hG_dist : Generator.fnMinDistAtLeast G.inducedCode d₁)
    (hH_dist : Generator.fnMinDistAtLeast H.inducedCode d₂) :
    Generator.fnMinDistAtLeast (G.tensorProduct H).inducedCode (d₁ * d₂) := by
  classical
  intro w hw_mem hw_ne
  -- Extract a coefficient vector V witnessing membership.
  rw [Generator.mem_inducedCode_iff] at hw_mem
  obtain ⟨V, hV⟩ := hw_mem
  -- Define the matrix M(j, i) = V (finProdFinEquiv (j, i)).
  set M : Fin ℓ₁ → Fin ℓ₂ → F := fun j i => V (finProdFinEquiv (j, i)) with hM_def
  -- Express w(s, t) as the bilinear form ∑ⱼ ∑ᵢ G(s) j · H(t) i · M j i.
  have hw_bilinear : ∀ p : S₁ × S₂,
      w p = ∑ j : Fin ℓ₁, ∑ i : Fin ℓ₂, G p.1 j * H p.2 i * M j i := by
    intro p
    have h1 : w p = ∑ k : Fin (ℓ₁ * ℓ₂),
        (G.tensorProduct H) p k * V k := hV p
    rw [h1]
    have step1 : ∀ k : Fin (ℓ₁ * ℓ₂),
        (G.tensorProduct H) p k * V k =
          G p.1 (finProdFinEquiv.symm k).1 *
            H p.2 (finProdFinEquiv.symm k).2 *
            V (finProdFinEquiv (finProdFinEquiv.symm k)) := by
      intro k
      rw [tensorProduct_apply, Equiv.apply_symm_apply]
    rw [Finset.sum_congr rfl (fun k _ => step1 k)]
    have := sum_finProdFinEquiv_symm
      (fun j i => G p.1 j * H p.2 i * V (finProdFinEquiv (j, i)))
    simpa [hM_def] using this
  -- Define μ s : Fin ℓ₂ → F so that the row at fixed s is H.dotMap (μ s).
  set μ : S₁ → Fin ℓ₂ → F := fun s i => ∑ j : Fin ℓ₁, G s j * M j i with hμ_def
  -- Define ν t : Fin ℓ₁ → F so that the column at fixed t is G.dotMap (ν t).
  set ν : S₂ → Fin ℓ₁ → F := fun t j => ∑ i : Fin ℓ₂, H t i * M j i with hν_def
  -- For each fixed s, the row t ↦ w(s,t) is H.dotMap (μ s).
  have h_row : ∀ (s : S₁) (t : S₂), w (s, t) = ∑ i : Fin ℓ₂, H t i * μ s i := by
    intro s t
    rw [hw_bilinear (s, t)]
    -- ∑ j ∑ i, G s j * H t i * M j i = ∑ i, H t i * (∑ j, G s j * M j i)
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros i _
    rw [hμ_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros j _
    ring
  -- For each fixed t, the column s ↦ w(s,t) is G.dotMap (ν t).
  have h_col : ∀ (s : S₁) (t : S₂), w (s, t) = ∑ j : Fin ℓ₁, G s j * ν t j := by
    intro s t
    rw [hw_bilinear (s, t)]
    -- ∑ j ∑ i, G s j * H t i * M j i = ∑ j, G s j * (∑ i, H t i * M j i)
    apply Finset.sum_congr rfl
    intros j _
    rw [hν_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros i _
    ring
  -- Row at fixed s lies in H.inducedCode.
  have h_row_mem : ∀ s : S₁, (fun t => w (s, t)) ∈ H.inducedCode := by
    intro s
    rw [Generator.mem_inducedCode_iff]
    exact ⟨μ s, fun t => h_row s t⟩
  -- Column at fixed t lies in G.inducedCode.
  have h_col_mem : ∀ t : S₂, (fun s => w (s, t)) ∈ G.inducedCode := by
    intro t
    rw [Generator.mem_inducedCode_iff]
    exact ⟨ν t, fun s => h_col s t⟩
  -- Find some (s₀, t₀) with w(s₀, t₀) ≠ 0.
  have h_exist : ∃ p : S₁ × S₂, w p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw_ne (funext h)
  obtain ⟨⟨s₀, t₀⟩, hw0_ne⟩ := h_exist
  -- The column at t₀ is non-zero (witness s₀).
  have h_col_t₀_ne : (fun s => w (s, t₀)) ≠ 0 := by
    intro hzero
    apply hw0_ne
    have := congr_fun hzero s₀
    simpa using this
  -- Apply G's min distance to the column at t₀.
  have h_col_weight :
      d₁ ≤ Generator.fnHammingWeight (fun s => w (s, t₀)) :=
    hG_dist _ (h_col_mem t₀) h_col_t₀_ne
  -- The set of "live rows" (rows where w(s, ·) is non-zero).
  set liveRows : Finset S₁ :=
    Finset.univ.filter (fun s => (fun t => w (s, t)) ≠ 0) with h_liveRows_def
  -- Live rows contain all s with w(s, t₀) ≠ 0.
  have h_col_subset_live :
      (Finset.univ.filter (fun s : S₁ => w (s, t₀) ≠ 0)) ⊆ liveRows := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [h_liveRows_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hrow_zero
    have := congr_fun hrow_zero t₀
    simp at this
    exact hs.2 this
  -- Therefore #liveRows ≥ d₁.
  have h_liveRows_card : d₁ ≤ liveRows.card := by
    have h1 : d₁ ≤ (Finset.univ.filter (fun s : S₁ => w (s, t₀) ≠ 0)).card := by
      have := h_col_weight
      unfold Generator.fnHammingWeight at this
      exact this
    exact h1.trans (Finset.card_le_card h_col_subset_live)
  -- For each live row s, the row at s has weight ≥ d₂.
  have h_row_weight :
      ∀ s ∈ liveRows, d₂ ≤ Generator.fnHammingWeight (fun t => w (s, t)) := by
    intro s hs
    rw [h_liveRows_def, Finset.mem_filter] at hs
    exact hH_dist _ (h_row_mem s) hs.2
  -- Express fnHammingWeight w as the sum over s of row weights.
  -- fnHammingWeight w = #{p : S₁ × S₂ | w p ≠ 0}
  --                   = ∑ s, #{t : S₂ | w (s, t) ≠ 0}
  have h_weight_eq :
      Generator.fnHammingWeight w =
        ∑ s : S₁, Generator.fnHammingWeight (fun t : S₂ => w (s, t)) := by
    unfold Generator.fnHammingWeight
    -- Use card_eq_sum_card_fiberwise on the projection Prod.fst.
    have hmaps : ((Finset.univ.filter fun p : S₁ × S₂ => w p ≠ 0) : Set (S₁ × S₂)).MapsTo
        Prod.fst (Finset.univ : Finset S₁) := by
      intro p _
      exact Finset.mem_univ _
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intros s _
    -- Goal: #{p ∈ filter | p.1 = s} = #{t | w(s, t) ≠ 0}
    -- Use a bijection between {p ∈ filter | p.1 = s} and {t | w(s, t) ≠ 0}.
    apply Finset.card_bij (fun (p : S₁ × S₂) _ => p.2)
    · -- maps_to
      intros p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp_mem, hp_eq⟩ := hp
      rw [Finset.mem_filter] at hp_mem
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hp_eq]
      exact hp_mem.2
    · -- injective
      intros p hp q hq hpq
      rw [Finset.mem_filter] at hp hq
      obtain ⟨_, hp_eq⟩ := hp
      obtain ⟨_, hq_eq⟩ := hq
      ext
      · rw [hp_eq, hq_eq]
      · exact hpq
    · -- surjective
      intros t ht
      rw [Finset.mem_filter] at ht
      refine ⟨(s, t), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht.2⟩
  -- Now bound the sum using live rows.
  rw [h_weight_eq]
  -- Split sum over S₁ into liveRows and its complement.
  have h_sum_split :
      ∑ s : S₁, Generator.fnHammingWeight (fun t : S₂ => w (s, t)) =
        ∑ s ∈ liveRows, Generator.fnHammingWeight (fun t : S₂ => w (s, t)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intros s _ hs_not_live
    -- s ∉ liveRows means (fun t => w(s,t)) = 0
    rw [h_liveRows_def, Finset.mem_filter] at hs_not_live
    push_neg at hs_not_live
    have hrow_zero : (fun t => w (s, t)) = 0 := hs_not_live (Finset.mem_univ _)
    -- fnHammingWeight 0 = 0
    unfold Generator.fnHammingWeight
    have : ∀ t : S₂, (fun t => w (s, t)) t = 0 := fun t => congr_fun hrow_zero t
    simp [this]
  rw [h_sum_split]
  -- Bound: each summand ≥ d₂, count ≥ d₁.
  have h_lower :
      d₁ * d₂ ≤ ∑ s ∈ liveRows, Generator.fnHammingWeight (fun t : S₂ => w (s, t)) := by
    have h_const : ∑ _s ∈ liveRows, d₂ = liveRows.card * d₂ := by
      rw [Finset.sum_const, smul_eq_mul]
    calc d₁ * d₂ ≤ liveRows.card * d₂ := Nat.mul_le_mul_right d₂ h_liveRows_card
      _ = ∑ _s ∈ liveRows, d₂ := h_const.symm
      _ ≤ ∑ s ∈ liveRows, Generator.fnHammingWeight (fun t : S₂ => w (s, t)) :=
          Finset.sum_le_sum h_row_weight
  exact h_lower

end Generator
end LinearCodes
