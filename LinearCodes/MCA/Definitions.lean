/-
# Generators and mutual correlated agreement

Structural definitions from §3.2–3.3 of BCGM25:

* `Generator F S ℓ` — a function from a seed type to `F^ℓ`.
* `Generator.combine` — linear combination of `ℓ` vectors using
  generator coefficients.
* `seedProb P` — probability of `P` over a uniform-random seed (`ℚ`).
* `ZeroEvading G ε` — Definition 3.11: bound on prob. that `G(x) · v = 0`.
* `CorrelatedAgreement G c εCA` — Definition 3.21.
* `MutualCorrelatedAgreement G c εMCA` — Definition 3.14, the strong
  form, expressed via `InRestrictedCode`.

The MCA bad event (per BCGM25): there exists a shared agreement set
`T ⊆ [n]` of size at least `n(1−γ)` such that `(G(x)·U)|T ∈ c|T` but
some `uⱼ|T ∉ c|T`. We bound its probability by `εMCA γ`.
-/

import LinearCodes.Algebraic.Code
import LinearCodes.Algebraic.Restriction
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Order.Field.Basic

namespace LinearCodes

/-! ### Generator -/

/-- A *generator* with output size `ℓ` over field `F` is a function from
some seed type `S` to `F^ℓ`. -/
structure Generator (F : Type*) [Field F] (S : Type*) (ℓ : ℕ) where
  toFun : S → (Fin ℓ → F)

instance {F : Type*} [Field F] {S : Type*} {ℓ : ℕ} :
    CoeFun (Generator F S ℓ) (fun _ => S → (Fin ℓ → F)) := ⟨Generator.toFun⟩

/-- The linear combination of `ℓ` vectors using the coefficients produced
by the generator on seed `x`: `(G(x) · u)ᵢ = ∑ⱼ G(x)ⱼ · uⱼᵢ`. -/
def Generator.combine {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (us : Fin ℓ → (Fin n → F)) :
    Fin n → F :=
  fun i => ∑ j : Fin ℓ, G x j * us j i

/-! ### Probability over a finite seed set -/

/-- The fraction of seeds in a finite type `S` for which the predicate `P`
holds, expressed as a rational. Uses classical decidability so the
caller does not have to supply a `DecidablePred` instance. -/
noncomputable def seedProb {S : Type*} [Fintype S] (P : S → Prop) : ℚ :=
  letI : DecidablePred P := Classical.decPred P
  (Finset.univ.filter P).card / (Fintype.card S : ℚ)

/-! ### Properties of `seedProb` -/

/-- The seed-probability is always non-negative. -/
theorem seedProb_nonneg {S : Type*} [Fintype S] (P : S → Prop) :
    0 ≤ seedProb P := by
  unfold seedProb
  exact div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)

/-- The seed-probability is always at most one. -/
theorem seedProb_le_one {S : Type*} [Fintype S] [Nonempty S] (P : S → Prop) :
    seedProb P ≤ 1 := by
  unfold seedProb
  letI : DecidablePred P := Classical.decPred P
  have h_pos : (0 : ℚ) < (Fintype.card S : ℚ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_one h_pos]
  exact_mod_cast (Finset.card_filter_le Finset.univ P).trans_eq Finset.card_univ.symm

/-! ### Properties of `Generator.combine` -/

/-- Combining the all-zero family of vectors gives the zero vector. -/
theorem Generator.combine_zero_us {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) :
    G.combine x (fun _ => (0 : Fin n → F)) = 0 := by
  ext i
  simp [Generator.combine]

/-- Pointwise unfold: the `i`-th coordinate of the combined vector is
the explicit weighted sum. -/
theorem Generator.combine_apply {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (us : Fin ℓ → (Fin n → F)) (i : Fin n) :
    G.combine x us i = ∑ j : Fin ℓ, G x j * us j i := rfl

/-! ### More `seedProb` properties -/

/-- The probability of the always-true predicate is one (over a nonempty
seed set). -/
theorem seedProb_const_true {S : Type*} [Fintype S] [Nonempty S] :
    seedProb (fun _ : S => True) = 1 := by
  unfold seedProb
  simp only [Finset.filter_true, Finset.card_univ]
  have : (Fintype.card S : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact div_self this

/-- The probability of the always-false predicate is zero. -/
theorem seedProb_const_false {S : Type*} [Fintype S] :
    seedProb (fun _ : S => False) = 0 := by
  unfold seedProb
  simp

/-! ### More `Generator.combine` properties -/

/-- The linear combination is additive in the input vector family. -/
theorem Generator.combine_add {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (us vs : Fin ℓ → (Fin n → F)) :
    G.combine x (us + vs) = G.combine x us + G.combine x vs := by
  ext i
  simp only [Generator.combine, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-- The linear combination is homogeneous in the input vector family. -/
theorem Generator.combine_smul {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (α : F) (us : Fin ℓ → (Fin n → F)) :
    G.combine x (α • us) = α • G.combine x us := by
  ext i
  simp only [Generator.combine, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-- If the seed gives the zero coefficient vector, the combination is zero. -/
theorem Generator.combine_zero_seed {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (h : G x = 0) (us : Fin ℓ → (Fin n → F)) :
    G.combine x us = 0 := by
  ext i
  simp only [Generator.combine, h, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The linear combination respects negation in the input vector family. -/
theorem Generator.combine_neg {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (us : Fin ℓ → (Fin n → F)) :
    G.combine x (-us) = -(G.combine x us) := by
  ext i
  simp only [Generator.combine, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- The linear combination distributes over subtraction in the input vector family. -/
theorem Generator.combine_sub {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (us vs : Fin ℓ → (Fin n → F)) :
    G.combine x (us - vs) = G.combine x us - G.combine x vs := by
  ext i
  simp only [Generator.combine, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-- Combining `(v j • u)_j` (each input is `v j • u` for the same `u`) gives
`(∑ j, G x j * v j) • u`. This is the key bridge between `seed-dotted-with-v`
and the MCA bad-event construction in BCGM25 Lemma 3.18. -/
theorem Generator.combine_smul_const {F : Type*} [Field F] {S : Type*} {ℓ n : ℕ}
    (G : Generator F S ℓ) (x : S) (v : Fin ℓ → F) (u : Fin n → F) :
    G.combine x (fun j => v j • u) = (∑ j, G x j * v j) • u := by
  ext i
  simp only [Generator.combine, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-! ### Distance-preservation predicates -/

/-- A generator is *zero-evading* with error `ε` if for every nonzero
`v ∈ F^ℓ`, the probability over a random seed that the inner product
`G(x) · v` is zero is at most `ε`. -/
def ZeroEvading {F : Type*} [Field F] {S : Type*} [Fintype S] {ℓ : ℕ}
    (G : Generator F S ℓ) (ε : ℚ) : Prop :=
  ∀ v : Fin ℓ → F, v ≠ 0 →
    seedProb (S := S) (fun x => ∑ j, G x j * v j = 0) ≤ ε

/-- A generator has *mutual correlated agreement* (MCA) for code `c` with
error function `εMCA` iff, for every collection of vectors `u₁,…,u_ℓ`
and every `γ ∈ [0,1]`, the bad event has probability at most `εMCA(γ)`.
The bad event: there exists a shared agreement set `T ⊆ [n]` of size
`≥ n(1−γ)` such that `(G(x)·U)|T ∈ c|T` while some `uⱼ|T ∉ c|T`. -/
def MutualCorrelatedAgreement {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (εMCA : ℚ → ℚ) : Prop :=
  ∀ (us : Fin ℓ → (Fin n → F)) (γ : ℚ), 0 ≤ γ → γ ≤ 1 →
    seedProb (S := S) (fun x =>
      ∃ T : Finset (Fin n), (T.card : ℚ) ≥ n * (1 - γ) ∧
        InRestrictedCode c T (G.combine x us) ∧
        ∃ j : Fin ℓ, ¬ InRestrictedCode c T (us j))
    ≤ εMCA γ

/-- A generator has *correlated agreement* (CA) for code `c` with error
function `εCA(e, t)` iff, for every set of words `U` whose row-wise
distance from `c` is at least `e`, the probability that the linear
combination is `(e − t)`-close to `c` is at most `εCA(e, t)`. -/
def CorrelatedAgreement {F : Type*} [Field F] [DecidableEq F]
    {S : Type*} [Fintype S] {n ℓ : ℕ}
    (G : Generator F S ℓ) (c : Submodule F (Fin n → F))
    (εCA : ℕ → ℕ → ℚ) : Prop :=
  ∀ (e t : ℕ), 1 ≤ t → t < e → e ≤ n →
    ∀ (us : Fin ℓ → (Fin n → F)),
      (∀ i : Fin ℓ, ∀ codeword ∈ c, e ≤ hammingDistance (us i) codeword) →
      seedProb (S := S) (fun x =>
        ∃ codeword ∈ c, hammingDistance (G.combine x us) codeword ≤ e - t)
      ≤ εCA e t

end LinearCodes
