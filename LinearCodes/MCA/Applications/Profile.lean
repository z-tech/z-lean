/-
# BCGM25 §9 cross-cutting predicates

Cross-cutting predicates connecting concrete generators used by modern
IOP-based SNARKs (STIR, WHIR-univariate, WARP) to the abstract MCA /
CA framework defined in `LinearCodes.MCA.Definitions`. These predicates
let downstream consumers state hypotheses against a single named
"profile" rather than re-deriving the structural facts each time.

Key contents:
* `IsSTIRGenerator G` — predicate asserting that `G` equals
  `Generator.univariatePowers F d` for some `d`, exposing the
  univariate-powers structure to the consumer.
* `IsAffineLineGenerator G` — predicate asserting `G` equals
  `Generator.affineLine F` (the simplest non-trivial WHIR-univariate
  generator).
* `IsRSCombinationGenerator G` — predicate asserting `G` equals
  `Generator.univariatePowers F l` (same shape as STIR but flagged as
  the "RS linear-combination" usage in proximity tests).
* `IsSTIRGenerator.exists_degree` — predicate-level corollary extracting
  the underlying degree.
* `hasMCABound` — predicate stating that a `(generator, code)` pair
  admits *some* MCA error function. Lets clients hide the precise BCGM25
  form behind an existential, while still recovering it on demand.

Sanity theorems verify each predicate is satisfied by the canonical
generator it characterizes.

Depends on `LinearCodes.MCA.Applications.STIR`. Future profiles
(WHIR-univariate, WARP) will be added here as their applications are
formalized.
-/

import LinearCodes.MCA.Applications.STIR


namespace LinearCodes

/-! ### C1: STIR generator predicate -/

/-- C1: A generator is "STIR-style" if it equals `univariatePowers F d` for some `d`. -/
def IsSTIRGenerator {F : Type*} [Field F] {ℓ : ℕ} (G : Generator F F ℓ) : Prop :=
  ∃ d : ℕ, ℓ = d + 1 ∧ HEq G (Generator.univariatePowers F d)

/-- Sanity: the canonical STIR generator satisfies the predicate. -/
theorem univariatePowers_isSTIR {F : Type*} [Field F] (d : ℕ) :
    IsSTIRGenerator (Generator.univariatePowers F d) :=
  ⟨d, rfl, HEq.rfl⟩

/-- C1-corollary: An `IsSTIRGenerator` witness exposes a concrete degree
`d` such that the seed-arity is `d + 1`. Useful for downstream consumers
that want to refer to "the STIR degree" without unfolding the predicate. -/
theorem IsSTIRGenerator.exists_degree {F : Type*} [Field F] {ℓ : ℕ}
    {G : Generator F F ℓ} (hG : IsSTIRGenerator G) :
    ∃ d : ℕ, ℓ = d + 1 := by
  obtain ⟨d, hℓ, _⟩ := hG
  exact ⟨d, hℓ⟩

/-- C1-corollary: From an `IsSTIRGenerator` witness, the seed-arity `ℓ`
is positive (at least 1). -/
theorem IsSTIRGenerator.arity_pos {F : Type*} [Field F] {ℓ : ℕ}
    {G : Generator F F ℓ} (hG : IsSTIRGenerator G) :
    0 < ℓ := by
  obtain ⟨d, hℓ⟩ := hG.exists_degree
  omega

/-! ### C2: Affine-line generator predicate -/

/-- C2: A generator is the "affine-line" generator if it equals
`Generator.affineLine F`. The seed-arity is fixed to `2` here because
`affineLine` has signature `Generator F F 2`. -/
def IsAffineLineGenerator {F : Type*} [Field F] (G : Generator F F 2) : Prop :=
  G = Generator.affineLine F

/-- Sanity (C2): the canonical affine-line generator satisfies the predicate. -/
theorem affineLine_isAffineLineGenerator {F : Type*} [Field F] :
    IsAffineLineGenerator (Generator.affineLine F) := rfl

/-- C2-corollary: an `IsAffineLineGenerator` witness lets us evaluate the
zeroth coordinate to `1` on any input. -/
theorem IsAffineLineGenerator.coord_zero {F : Type*} [Field F]
    {G : Generator F F 2} (hG : IsAffineLineGenerator G) (x : F) :
    G x 0 = 1 := by
  rw [hG]; rfl

/-- C2-corollary: an `IsAffineLineGenerator` witness lets us evaluate the
first coordinate to the input on any seed. -/
theorem IsAffineLineGenerator.coord_one {F : Type*} [Field F]
    {G : Generator F F 2} (hG : IsAffineLineGenerator G) (x : F) :
    G x 1 = x := by
  rw [hG]; rfl

/-! ### C3: RS-combination generator predicate -/

/-- C3: A generator is an "RS linear-combination" generator if it equals
`univariatePowers F l` (with seed-arity `l + 1`). Structurally identical
to `IsSTIRGenerator` but flagged separately to mark the BCGM25 §9
RS linear-combination usage (the `Generator.combine` of a seed against
`(u₀, …, u_l)` produces `∑ x^i · u_i`, a univariate RS combination). -/
def IsRSCombinationGenerator {F : Type*} [Field F] {l : ℕ}
    (G : Generator F F (l + 1)) : Prop :=
  G = Generator.univariatePowers F l

/-- Sanity (C3): the canonical univariate-powers generator satisfies the
RS-combination predicate. -/
theorem univariatePowers_isRSCombination {F : Type*} [Field F] (l : ℕ) :
    IsRSCombinationGenerator (Generator.univariatePowers F l) := rfl

/-- C3-corollary: any `IsRSCombinationGenerator` is also an
`IsSTIRGenerator` (the two predicates pin the same underlying generator
shape; this is the canonical bridge). -/
theorem IsRSCombinationGenerator.isSTIRGenerator {F : Type*} [Field F]
    {l : ℕ} {G : Generator F F (l + 1)} (hG : IsRSCombinationGenerator G) :
    IsSTIRGenerator G := by
  rw [hG]
  exact univariatePowers_isSTIR l

/-! ### C4: MCA-bound existence predicate -/

/-- C4: A `(generator, code)` pair `(G, c)` *has an MCA bound* if there
exists some error function `εMCA : ℚ → ℚ` for which the abstract
`MutualCorrelatedAgreement` predicate holds. This is the existential
form of the BCGM25 MCA hypothesis (Definition 3.14): clients that
only need to assume "an MCA bound exists" can use this predicate
without committing to its precise functional form. -/
def hasMCABound {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F)) : Prop :=
  ∃ εMCA : ℚ → ℚ, MutualCorrelatedAgreement G c εMCA

/-- Sanity (C4): the STIR generator over any field with `d + 1 ≤ |F|`
admits an MCA bound for any code with a known minimum-distance witness.
This wraps `STIR_MutualCorrelatedAgreement` into the existential form. -/
theorem STIR_hasMCABound
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {d n : ℕ}
    (hd : d + 1 ≤ Fintype.card F) (c : Submodule F (Fin n → F)) (hn : 0 < n)
    {δ_C : ℕ} (h_minDist : MinDistAtLeast c δ_C) :
    hasMCABound (Generator.univariatePowers F d) c :=
  ⟨_, STIR_MutualCorrelatedAgreement hd c hn h_minDist⟩

/-- C4-corollary: From `hasMCABound G c`, we recover *some* concrete
error function realizing the predicate. This is the eliminator: clients
holding a `hasMCABound` witness can bind the underlying function and
reason about it abstractly. -/
theorem hasMCABound.exists_εMCA {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)}
    (h : hasMCABound G c) :
    ∃ εMCA : ℚ → ℚ, MutualCorrelatedAgreement G c εMCA := h

/-- C4-corollary: `hasMCABound` is preserved when we replace the error
function in a `MutualCorrelatedAgreement` witness; in particular, given
*any* concrete MCA proof, we obtain `hasMCABound`. -/
theorem MutualCorrelatedAgreement.hasMCABound {F : Type*} [Field F]
    [DecidableEq F] {S : Type*} [Fintype S] {n ℓ : ℕ}
    {G : Generator F S ℓ} {c : Submodule F (Fin n → F)} {εMCA : ℚ → ℚ}
    (h : MutualCorrelatedAgreement G c εMCA) :
    LinearCodes.hasMCABound G c :=
  ⟨εMCA, h⟩

end LinearCodes
