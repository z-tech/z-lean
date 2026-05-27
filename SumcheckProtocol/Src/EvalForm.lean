import SumcheckProtocol.Src.Hypercube
import SumcheckProtocol.Src.Prover

/-!
# Evaluation-form honest prover (Phase 1, definition)

This file is purely additive: it adds the definition of the eval-form
honest sumcheck prover round message, alongside the existing symbolic
path in `SumcheckProtocol/Src/Prover.lean`. Nothing in `Src/Prover.lean`,
`Src/Verifier.lean`, or `Properties/**` is touched.

* `honestProverMessageEvalsAt` is the value of round `i`'s polynomial at
  a field point `c`, computed as a sum over `domain^(numOpenVars i)`
  (i.e. the representation `effsc` ships its round polys in).

The consistency lemma between this and the symbolic prover, and the
Lagrange-interpolation corollary, live in
`SumcheckProtocol/Properties/EvalForm.lean` because their proofs depend on
`Properties/Lemmas/HonestRoundProofs` (which itself depends on
`SumcheckProtocol.IP.Statement`, which depends on `SumcheckProtocol.Src` — a cycle if
those proofs lived inside `Src/`).
-/

/-- Length-`numOpenVars i` arithmetic identity used by the `Fin.snoc`
form: `(i.val + 1) + numOpenVars i = n`. -/
lemma snoc_split_eq {n : ℕ} (i : Fin n) :
    (i.val + 1) + numOpenVars (n := n) i = n := by
  classical
  set m : ℕ := numOpenVars (n := n) i with hm
  have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  simp [m, numOpenVars, Nat.add_sub_of_le hle]

/--
Eval-form honest prover round message. At round `i`, with prior
challenges `challenges`, the value of the round polynomial at field
point `c` equals the sum of `p` over the residual `numOpenVars i =
n - i - 1` open variables, with positions `0..i-1` fixed to
`challenges`, position `i` fixed to `c`, and positions `i+1..n-1`
ranging over `domain`.

Defined on top of `residualSumWithOpenVars` per the Phase 1 spec — no
new sum-over-hypercube primitive.
-/
def honestProverMessageEvalsAt
  {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
  {n : ℕ}
  (domain : List 𝔽)
  (p : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (c : 𝔽) : 𝔽 :=
  residualSumWithOpenVars (𝔽 := 𝔽)
    (k := i.val + 1) (n := n)
    domain
    (openVars := numOpenVars (n := n) i)
    (hn := snoc_split_eq (n := n) i)
    (ch := Fin.snoc challenges c)
    (p := p)
