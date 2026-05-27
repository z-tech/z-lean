import CompPoly.Multivariate.Rename
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.MvPolyEquiv

import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Src.Prover
import SumcheckProtocol.Src.EvalForm

/-!
# Variable-ordering convention layer for sumcheck

The honest prover/verifier in `SumcheckProtocol/Src/Prover.lean` uses an LSB-style
variable-binding order: at round `i : Fin n`, variable position `i` is the one
being summed against the partial-challenge prefix. This is the convention
used by Lean as the oracle for the Rust `effsc` library.

External callers (in particular `multilinear_sumcheck.rs`) bind variables in
the *opposite* order: high-order position first, i.e. position `n-1` at round
`0`, position `n-2` at round `1`, ..., position `0` at round `n-1`. We call
this MSB.

The two conventions agree on the underlying mathematics — they only differ
by a permutation of the variable indices of `p`. Concretely, `reverseFin`
swaps `i ↔ n-1-i`, and:

  MSB sumcheck on `p` at round `i`
  = LSB sumcheck on `CMvPolynomial.rename reverseFin p` at round `i`.

The round index does *not* need to be reversed: composing `p` with
`reverseFin` already shuffles the variable positions so that LSB binding of
position `i` of `rename reverseFin p` is MSB binding of position `n-1-i`
of `p`. This file makes the convention an explicit parameter and proves the
equivalence so downstream users can pick one and not silently disagree with
the oracle.
-/

namespace SumcheckProtocol

/-- Which variable ordering convention is in force. -/
inductive Convention
  | MSB
  | LSB
deriving DecidableEq

/-- The index-reversing involution on `Fin n`: `i ↦ n-1-i`. -/
def reverseFin {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by
    have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hle : n - 1 - i.val ≤ n - 1 := Nat.sub_le _ _
    exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hpos Nat.one_pos)⟩

@[simp] lemma reverseFin_val {n : ℕ} (i : Fin n) :
    (reverseFin i).val = n - 1 - i.val := rfl

/-- `reverseFin` is an involution. -/
@[simp] lemma reverseFin_reverseFin {n : ℕ} (i : Fin n) :
    reverseFin (reverseFin i) = i := by
  apply Fin.ext
  simp only [reverseFin_val]
  have hi : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
  omega

lemma reverseFin_involutive {n : ℕ} : Function.Involutive (reverseFin (n := n)) :=
  reverseFin_reverseFin

/-- `reverseFin` is a bijection (it's an involution). -/
lemma reverseFin_bijective {n : ℕ} : Function.Bijective (reverseFin (n := n)) :=
  reverseFin_involutive.bijective

/-- `reverseFin` packaged as a self-equivalence on `Fin n`. -/
def reverseFinEquiv (n : ℕ) : Fin n ≃ Fin n :=
  Function.Involutive.toPerm reverseFin reverseFin_involutive

@[simp] lemma reverseFinEquiv_apply {n : ℕ} (i : Fin n) :
    reverseFinEquiv n i = reverseFin i := rfl

@[simp] lemma reverseFinEquiv_symm_apply {n : ℕ} (i : Fin n) :
    (reverseFinEquiv n).symm i = reverseFin i := rfl

/-! ### `eval` of a renamed polynomial: the small bonus lemma. -/

/-- Evaluating `rename f p` at a point `vs` is the same as evaluating `p`
    at `vs ∘ f`. This is the `CMvPolynomial`-level analogue of
    `MvPolynomial.eval_rename`, transferred via `fromCMvPolynomial`. -/
lemma eval_rename
    {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → Fin m) (p : CPoly.CMvPolynomial n R) (vs : Fin m → R) :
    CPoly.CMvPolynomial.eval vs (CPoly.CMvPolynomial.rename f p)
      = CPoly.CMvPolynomial.eval (vs ∘ f) p := by
  rw [CPoly.eval_equiv, CPoly.fromCMvPolynomial_rename,
      MvPolynomial.eval_rename, ← CPoly.eval_equiv]

/-! ### Convention-parameterised honest-prover message. -/

/-- The honest prover round-`i` message under either convention.

    * `LSB`: the existing `honestProverMessageAt` on `p`.
    * `MSB`: `honestProverMessageAt` on `CPoly.CMvPolynomial.rename reverseFin p`,
      with the same round index. The reversal of `p`'s variable indices is
      enough; no round-index translation is required. -/
def honestProverMessageAtConv
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ}
    (conv : Convention)
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  match conv with
  | Convention.LSB =>
      honestProverMessageAt (𝔽 := 𝔽) domain p i challenges
  | Convention.MSB =>
      honestProverMessageAt (𝔽 := 𝔽) domain
        (CPoly.CMvPolynomial.rename reverseFin p) i challenges

/-- Definitional unfolding for the LSB branch. -/
@[simp] lemma honestProverMessageAtConv_LSB
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) :
    honestProverMessageAtConv Convention.LSB domain p i challenges
      = honestProverMessageAt domain p i challenges := rfl

/-- Definitional unfolding for the MSB branch. -/
@[simp] lemma honestProverMessageAtConv_MSB
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) :
    honestProverMessageAtConv Convention.MSB domain p i challenges
      = honestProverMessageAt domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges := rfl

/-! ### The convention-equivalence theorem. -/

/-- **Convention equivalence.** The MSB round-`i` message on `p` equals the
    LSB round-`i` message on `CPoly.CMvPolynomial.rename reverseFin p`.

    This is the only "content" of the LSB↔MSB distinction at the polynomial
    level; downstream users can pick a convention and translate freely. -/
theorem honestProverMessageAtConv_MSB_eq_LSB_rename
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) :
    honestProverMessageAtConv Convention.MSB domain p i challenges
      = honestProverMessageAtConv Convention.LSB domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges := rfl

/-- Symmetric form: the LSB message on `p` equals the MSB message on
    `rename reverseFin p`. Useful when one already has an LSB statement and
    wants an MSB witness. Uses involutivity of `reverseFin`. -/
theorem honestProverMessageAtConv_LSB_eq_MSB_rename
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) :
    honestProverMessageAtConv Convention.LSB domain p i challenges
      = honestProverMessageAtConv Convention.MSB domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges := by
  show honestProverMessageAt domain p i challenges
        = honestProverMessageAt domain
            (CPoly.CMvPolynomial.rename reverseFin
              (CPoly.CMvPolynomial.rename reverseFin p)) i challenges
  rw [CPoly.rename_rename]
  have hcomp : (reverseFin (n := n)) ∘ (reverseFin (n := n)) = id := by
    funext i; exact reverseFin_reverseFin i
  rw [hcomp, CPoly.rename_id]

/-! ### Convention-parameterised eval-form prover message.

Mirror of `honestProverMessageAtConv` for the eval-form prover. Lets the
multilinear evaluation-table prover (which is natively MSB, matching
`effsc`'s `MultilinearProver`) bridge to the symbolic spec without
ad-hoc renaming at every call site. -/

/-- Eval-form honest prover round-`i` message at point `c`, parameterised
    by convention. Same dispatch logic as `honestProverMessageAtConv`. -/
def honestProverMessageEvalsAtConv
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ}
    (conv : Convention)
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    (c : 𝔽) : 𝔽 :=
  match conv with
  | Convention.LSB =>
      honestProverMessageEvalsAt (𝔽 := 𝔽) domain p i challenges c
  | Convention.MSB =>
      honestProverMessageEvalsAt (𝔽 := 𝔽) domain
        (CPoly.CMvPolynomial.rename reverseFin p) i challenges c

@[simp] lemma honestProverMessageEvalsAtConv_LSB
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (c : 𝔽) :
    honestProverMessageEvalsAtConv Convention.LSB domain p i challenges c
      = honestProverMessageEvalsAt domain p i challenges c := rfl

@[simp] lemma honestProverMessageEvalsAtConv_MSB
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (c : 𝔽) :
    honestProverMessageEvalsAtConv Convention.MSB domain p i challenges c
      = honestProverMessageEvalsAt domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges c := rfl

/-- **Eval-form convention equivalence.** MSB at round `i` on `p` equals
    LSB at round `i` on `rename reverseFin p`. -/
theorem honestProverMessageEvalsAtConv_MSB_eq_LSB_rename
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (c : 𝔽) :
    honestProverMessageEvalsAtConv Convention.MSB domain p i challenges c
      = honestProverMessageEvalsAtConv Convention.LSB domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges c := rfl

/-- Symmetric form via involutivity of `reverseFin`. -/
theorem honestProverMessageEvalsAtConv_LSB_eq_MSB_rename
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ} (domain : List 𝔽) (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n) (challenges : Fin i.val → 𝔽) (c : 𝔽) :
    honestProverMessageEvalsAtConv Convention.LSB domain p i challenges c
      = honestProverMessageEvalsAtConv Convention.MSB domain
          (CPoly.CMvPolynomial.rename reverseFin p) i challenges c := by
  show honestProverMessageEvalsAt domain p i challenges c
        = honestProverMessageEvalsAt domain
            (CPoly.CMvPolynomial.rename reverseFin
              (CPoly.CMvPolynomial.rename reverseFin p)) i challenges c
  rw [CPoly.rename_rename]
  have hcomp : (reverseFin (n := n)) ∘ (reverseFin (n := n)) = id := by
    funext i; exact reverseFin_reverseFin i
  rw [hcomp, CPoly.rename_id]

end SumcheckProtocol
