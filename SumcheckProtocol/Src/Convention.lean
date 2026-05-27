import CompPoly.Multivariate.Rename
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.MvPolyEquiv

import SumcheckProtocol.Src.CMvPolynomial
import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Src.Prover
import SumcheckProtocol.Src.EvalForm

/-!
# MSB variable-ordering wrapper for sumcheck

The honest prover/verifier in `SumcheckProtocol/Src/Prover.lean` binds
variables in **LSB** order: at round `i : Fin n`, variable position `i` is
the one being summed against the partial-challenge prefix.

External callers (in particular `multilinear_sumcheck.rs`) bind variables in
the *opposite* order — high-order position first, i.e. position `n-1` at
round `0`, position `n-2` at round `1`, ..., position `0` at round `n-1`.
We call this MSB.

The two orderings differ only by a permutation of variable indices:
`reverseFin` swaps `i ↔ n-1-i`, and

  MSB sumcheck on `p` at round `i`
  = LSB sumcheck on `CMvPolynomial.rename reverseFin p` at round `i`.

This file defines MSB wrappers (`honestProverMessageAtMSB`,
`honestProverMessageEvalsAtMSB`) so MSB-side callers don't have to repeat
the `rename reverseFin` at every site. The round index is not reversed;
composing `p` with `reverseFin` already shuffles positions so that LSB
binding of position `i` of `rename reverseFin p` matches MSB binding of
position `n-1-i` of `p`.
-/

namespace SumcheckProtocol

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

/-! ### MSB wrappers for the honest prover. -/

/-- MSB honest prover round-`i` message: the LSB honest prover applied to
    `CPoly.CMvPolynomial.rename reverseFin p`, with the same round index.
    The reversal of `p`'s variable indices is enough; no round-index
    translation is required. -/
def honestProverMessageAtMSB
    {𝔽 : Type _} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ}
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽) : CPoly.CMvPolynomial 1 𝔽 :=
  honestProverMessageAt (𝔽 := 𝔽) domain
    (CPoly.CMvPolynomial.rename reverseFin p) i challenges

/-- MSB eval-form honest prover round-`i` message at point `c`: the LSB
    eval-form prover applied to `rename reverseFin p`. -/
def honestProverMessageEvalsAtMSB
    {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    {n : ℕ}
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    (c : 𝔽) : 𝔽 :=
  honestProverMessageEvalsAt (𝔽 := 𝔽) domain
    (CPoly.CMvPolynomial.rename reverseFin p) i challenges c

end SumcheckProtocol
