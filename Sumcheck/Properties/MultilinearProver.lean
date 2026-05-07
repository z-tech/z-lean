import Sumcheck.Src.MultilinearProver

/-!
# Phase 2: Multilinear evaluation-table prover — correctness

This file states correctness of the eval-table prover defined in
`Sumcheck/Src/MultilinearProver.lean` against the symbolic spec.

## Scope of this file

The full Phase 2 plan asks for three correctness theorems:

  (a) `compute_correctness`: `computeS0S1_msb (toEvalTable p)` matches the
      symbolic eval-form prover's messages at the Boolean nodes 0 and 1.
  (b) `fold_correctness`: `toEvalTable (substRound0 w p) = fold_msb_succ w (toEvalTable p)`.
  (c) `multi_round_correctness`: end-to-end transcript equivalence by induction
      on `n`.

What is fully proved here, against the eval-table operations defined in
`Src/MultilinearProver.lean`:

* `computeS0S1_msb_succ_def` — exact `Finset.sum`-form unfolding of
  `computeS0S1_msb` at successor arity, expressed as sums over the low/high
  halves of the table.
* `getElem_toEvalTable` — `(toEvalTable p)[i]` is `eval (boolPoint_msb i) p`.
* `getElem_fold_msb_succ` — pointwise algebraic content of `fold_msb_succ`:
  `(fold_msb_succ w t)[k] = t[lo] + (t[hi] - t[lo]) * w`.
* `compute_correctness_table` (theorem (a) — narrowed). The eval-form prover's
  messages, expressed directly in terms of the table entries (not the symbolic
  prover), are exactly `computeS0S1_msb (toEvalTable p)`. Concretely:

      `computeS0S1_msb (toEvalTable p) =`
      `   (∑ k : Fin (2^n), eval (boolPoint_msb ⟨k.val, _⟩) p,`
      `    ∑ k : Fin (2^n), eval (boolPoint_msb ⟨2^n + k.val, _⟩) p)`.

  Bridging this to `honestProverMessageEvalsAt … 0` and `… 1` is purely a
  spec-rewrite at MSB↔LSB layer (`Convention.lean`) plus the standard fact
  that the boolean hypercube sum equals the bool-domain `sumOverDomainRecursive`
  with `domain = [0,1]`. We document that bridge here as a comment but do not
  formalise it: it requires bit-decomposition lemmas connecting
  `boolPoint_msb (Fin.castAdd k)` to `Fin.cases 0 (boolPoint_msb k)` and the
  matching unfolding of `sumOverDomainRecursive`. See "Deferred bridge" below.

* `fold_msb_succ_eq_lerp` (theorem (b) — narrowed). The pointwise algebraic
  identity that *would* be the content of `fold_correctness` once
  `substRound0` is defined: under the multilinear interpretation of an
  evaluation table, `fold_msb_succ` is the linear interpolation
  `lerp w lo hi = lo + (hi - lo) * w`. The full statement
  `toEvalTable (substRound0 w p) = fold_msb_succ w (toEvalTable p)` requires
  the multilinear-substitution lemma `MLE_substitute_x0`, which is not
  available in this codebase yet (the `substRound0` operation itself is
  not defined here — see the "Deferred" notes below). We capture the algebraic
  invariant that the substitution would have to satisfy.

* `multi_round_correctness_skeleton` (theorem (c) — narrowed). The end-to-end
  transcript-equivalence theorem reduces to the conjunction of (a) and (b)
  applied at every round. Without (b)'s symbolic statement we cannot phrase
  the full inductive equivalence to `honestProverMessageEvalsAt`-derived
  transcripts here. We state the *eval-table-internal* induction: the prover
  output list has the right length and round-0 message matches `computeS0S1_msb`
  on the input table.

## Deferred bridge to the symbolic spec

The remaining content (proving (b) and (c) against the symbolic prover) needs:

1. A definition of `substRound0 : 𝔽 → CMvPolynomial n 𝔽 → CMvPolynomial (n-1) 𝔽`
   that substitutes the round-0 (i.e. MSB) variable with `w` and re-indexes.
   This is the analogue of `MvPolynomial.eval₂` on a single variable but at
   the `CMvPolynomial`-level; CompPoly does not currently expose this directly.

2. The multilinearity lemma `MLE_substitute_x0`:
   `(substRound0 w p).eval b = (1 - w) * p.eval(0, b) + w * p.eval(1, b)`.
   For multilinear `p` this follows from `MvPolynomial.restrictDegree`
   reasoning, but the bridge lives in `CompPoly/Multilinear/Equiv.lean`
   in symbolic terms; transferring to `CMvPolynomial.eval` is a non-trivial
   additional bridge.

3. The MSB↔LSB bridge of Phase 3, which we already have at the *symbolic*
   prover level (`honestProverMessageAtConv`), but not at the eval-form level.
   A small helper `honestProverMessageEvalsAtConv` analogous to the symbolic
   one would tie this together. We do not introduce it here because (1) and
   (2) are the load-bearing missing pieces.

These are listed for the next phase. -/

namespace Sumcheck.MultilinearProver

open CompPoly

variable {𝔽 : Type _}

/-! ### Direct lookups -/

@[simp] theorem getElem_toEvalTable
    [CommSemiring 𝔽]
    {n : ℕ} (p : CPoly.CMvPolynomial n 𝔽) (i : Fin (2^n)) :
    (toEvalTable p)[i] = CPoly.CMvPolynomial.eval (boolPoint_msb (𝔽 := 𝔽) i) p := by
  simp [toEvalTable]

/-! ### `computeS0S1_msb` unfolding -/

/-- The successor-arity unfolding of `computeS0S1_msb`, in clean
    `Finset.sum` form. -/
theorem computeS0S1_msb_succ_def
    [AddCommMonoid 𝔽]
    {n : ℕ} (t : EvalTable (n+1) 𝔽) :
    computeS0S1_msb t =
      ( (∑ k : Fin (2^n),
          t[(⟨k.val, by
             have := k.isLt
             -- 2^n ≤ 2^(n+1) follows from pow_succ ≤ omega
             omega⟩ : Fin (2^(n+1)))]),
        (∑ k : Fin (2^n),
          t[(⟨2^n + k.val, by
             have := k.isLt
             show 2^n + k.val < 2^(n+1)
             rw [pow_succ]; omega⟩ : Fin (2^(n+1)))]) ) := by
  rfl

/-! ### `fold_msb_succ` pointwise lookup -/

/-- The defining algebraic identity for `fold_msb_succ`: each entry of the
    folded table is the linear interpolation `lo + (hi - lo) * w` of the
    corresponding low/high half pair. -/
theorem getElem_fold_msb_succ
    [CommRing 𝔽]
    {m : ℕ} (w : 𝔽) (t : EvalTable (m+1) 𝔽) (k : Fin (2^m)) :
    (fold_msb_succ w t)[k] =
      let lo := t[(⟨k.val, by
        have := k.isLt
        -- 2^m ≤ 2^(m+1) follows from pow_succ ≤ omega
        omega⟩ : Fin (2^(m+1)))]
      let hi := t[(⟨2^m + k.val, by
        have := k.isLt
        show 2^m + k.val < 2^(m+1)
        rw [pow_succ]; omega⟩ : Fin (2^(m+1)))]
      lo + (hi - lo) * w := by
  simp [fold_msb_succ]

/-! ### Theorem (a) — narrowed `compute_correctness` -/

/-- **Theorem (a) — narrowed (table-internal form).**

    `computeS0S1_msb (toEvalTable p)` is the pair of sums of `p` over the
    low/high halves of the Boolean hypercube under MSB indexing.

    Bridging this to `honestProverMessageEvalsAt domain p ⟨0,_⟩ Fin.elim0 0`
    and `… 1` from `Sumcheck/Src/EvalForm.lean` is a spec-rewrite step that
    consumes the MSB↔LSB convention layer (`Sumcheck/Src/Convention.lean`).
    We capture the table-side equality cleanly here; the spec-side rewrite
    is deferred (see file-level "Deferred bridge"). -/
theorem compute_correctness_table
    [CommSemiring 𝔽]
    {n : ℕ} (p : CPoly.CMvPolynomial (n+1) 𝔽) :
    computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p) =
      ( (∑ k : Fin (2^n),
          CPoly.CMvPolynomial.eval
            (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
              (⟨k.val, by
                have := k.isLt
                -- 2^n ≤ 2^(n+1) follows from pow_succ ≤ omega
                omega⟩ : Fin (2^(n+1)))) p),
        (∑ k : Fin (2^n),
          CPoly.CMvPolynomial.eval
            (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
              (⟨2^n + k.val, by
                have := k.isLt
                show 2^n + k.val < 2^(n+1)
                rw [pow_succ]; omega⟩ : Fin (2^(n+1)))) p) ) := by
  rw [computeS0S1_msb_succ_def]
  refine Prod.ext ?_ ?_
  · simp only [getElem_toEvalTable]
  · simp only [getElem_toEvalTable]

/-! ### Theorem (b) — narrowed `fold_correctness` -/

/-- **Theorem (b) — narrowed (algebraic invariant).**

    The pointwise identity that any correct round-0 substitution operator
    `substRound0 : 𝔽 → CMvPolynomial (n+1) 𝔽 → CMvPolynomial n 𝔽` satisfying
    `(substRound0 w p).eval b = (1-w) * p.eval(0, b) + w * p.eval(1, b)`
    must produce when materialised as an evaluation table. Concretely, every
    entry of `fold_msb_succ w (toEvalTable p)` is the linear interpolation of
    the eval at the corresponding boolean points with the high-order variable
    fixed to `0` vs `1`.

    The full Phase 2 statement
    `toEvalTable (substRound0 w p) = fold_msb_succ w (toEvalTable p)`
    requires the `substRound0` definition and the multilinear `MLE_substitute_x0`
    lemma (see "Deferred bridge"). The form below is the algebraic content
    of the equation — it is exactly what one obtains by unfolding both sides
    and using `MLE_substitute_x0`. -/
theorem fold_msb_succ_lerp_form
    [CommRing 𝔽]
    {n : ℕ} (w : 𝔽) (p : CPoly.CMvPolynomial (n+1) 𝔽) (k : Fin (2^n)) :
    (fold_msb_succ w (toEvalTable (𝔽 := 𝔽) p))[k] =
      let lo := CPoly.CMvPolynomial.eval
        (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
          (⟨k.val, by
            have := k.isLt
            -- 2^n ≤ 2^(n+1) follows from pow_succ ≤ omega
            omega⟩ : Fin (2^(n+1)))) p
      let hi := CPoly.CMvPolynomial.eval
        (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
          (⟨2^n + k.val, by
            have := k.isLt
            show 2^n + k.val < 2^(n+1)
            rw [pow_succ]; omega⟩ : Fin (2^(n+1)))) p
      lo + (hi - lo) * w := by
  rw [getElem_fold_msb_succ]
  simp only [getElem_toEvalTable]

/-! ### Theorem (c) — narrowed `multi_round_correctness` -/

/-- **Theorem (c) — narrowed (round count and round-0 message).**

    The eval-form prover produces exactly `n` `(s0, s1)` messages when run on
    an `EvalTable n 𝔽`, and the round-0 message is exactly
    `computeS0S1_msb` of the input table. Inducting this to a full transcript
    equivalence with `honestProverMessageEvalsAt` is deferred (it consumes
    theorem (b) to relate the recursive call's input table — `fold_msb_succ r t`
    — to the round-1 symbolic state `substRound0 r p`). -/
theorem multilinearProverEvalForm_length_and_head
    [CommRing 𝔽]
    {n : ℕ} (challenges : Fin n → 𝔽) (t : EvalTable n 𝔽) :
    (multilinearProverEvalForm challenges t).length = n
    ∧ (∀ _ : 0 < n,
        (multilinearProverEvalForm challenges t).head?
          = some (computeS0S1_msb t)) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · rfl
      · intro hpos; exact absurd hpos (lt_irrefl _)
  | succ m ih =>
      refine ⟨?_, ?_⟩
      · -- length is m + 1
        show (computeS0S1_msb t ::
              multilinearProverEvalForm
                (fun j : Fin m => challenges ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                (fold_msb_succ (challenges ⟨0, Nat.succ_pos m⟩) t)).length = m + 1
        rw [List.length_cons]
        congr 1
        exact (ih (fun j : Fin m => challenges ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                 (fold_msb_succ (challenges ⟨0, Nat.succ_pos m⟩) t)).1
      · intro _
        rfl

/-- The eval-table prover is well-defined for all `n` and produces a list of
    the right length. (Companion sanity check, follows from the previous.) -/
theorem multilinearProverEvalForm_length
    [CommRing 𝔽]
    {n : ℕ} (challenges : Fin n → 𝔽) (t : EvalTable n 𝔽) :
    (multilinearProverEvalForm challenges t).length = n :=
  (multilinearProverEvalForm_length_and_head challenges t).1

end Sumcheck.MultilinearProver
