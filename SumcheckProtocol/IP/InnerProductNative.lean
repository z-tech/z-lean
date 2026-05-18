import SumcheckProtocol.IP.InnerProduct
import SumcheckProtocol.IP.EvalForm
import SumcheckProtocol.Properties.EvalForm
import SumcheckProtocol.Properties.Lemmas.Hypercube

/-!
# Native two-oracle inner-product sumcheck (Phase 5(a))

A *native* eval-form inner-product sumcheck: at round `i`, with prior
challenges `chs`, the prover sends a tuple `Fin 3 → 𝔽` whose `k`-th
entry is

```
qEvals k = ∑_{x ∈ domain^(numOpenVars i)} f(point) · g(point)
```

where `point` extends `Fin.snoc chs (evalPoints k)` over the hypercube
`x`. Crucially this is `Σ a · b`, **not** `(Σ a) · (Σ b)` — the two
disagree in general, so we walk the hypercube once and multiply
*inside* the sum.

The point of going native is to avoid materialising the (potentially
huge) symbolic product `f * g` in the prover's hot path. The verifier
side and the corresponding instance plumbing are free to reuse the
existing eval-form infrastructure (Phase 4) on the symbolic product;
the equivalence proven here lets us swap the prover at will without
disturbing the surrounding protocol.

## Key declarations

* `residualSumPair` — hypercube walker that multiplies `f.eval pt` by
  `g.eval pt` per summand.
* `nativeHonestMessageEvalsAt` — the native prover's per-round value at
  a single field point `c`.
* `InnerProduct.NativeStatement` — bundle of `f`, `g`, a domain, the
  three evaluation nodes, multilinearity, and `Valid`.
* `nativeHonestMessageEvalsAt_eq_thinWrapper` — the equivalence to the
  thin-wrapper honest prover applied to `f * g`. The proof uses
  `CMvPolynomial.eval_mul` per summand, then `sum_over_domain_recursive_congr`.
-/

open CPoly

namespace InnerProduct

/--
Two-oracle hypercube walker. Same shape as `residualSumWithOpenVars`,
except each summand is the **product** `f.eval point · g.eval point`,
not the value of a single polynomial.

This is the prover's native primitive: it never materialises `f * g` as
a `CMvPolynomial`. Definitionally
`Σ_{x} f(point(x)) · g(point(x))`.
-/
def residualSumPair
  {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
  {k n : ℕ}
  (domain : List 𝔽)
  (openVars : ℕ)
  (hn : k + openVars = n)
  (ch : Fin k → 𝔽)
  (f g : CPoly.CMvPolynomial n 𝔽) : 𝔽 :=
  sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
    domain (· + ·) 0 (m := openVars)
    (fun x =>
      let point : Fin n → 𝔽 := fun i => addCasesFun ch x (Fin.cast hn.symm i)
      CPoly.CMvPolynomial.eval point f * CPoly.CMvPolynomial.eval point g)

/--
Native eval-form honest prover message for the inner-product sumcheck.

At round `i` with prior challenges `challenges`, the value of the round
polynomial at field point `c` is
`Σ_{x ∈ domain^(numOpenVars i)} f(point(x)) · g(point(x))`,
where `point` fixes positions `0..i-1` to `challenges`, position `i` to
`c`, and lets positions `i+1..n-1` range over `domain`.

Mirror of `honestProverMessageEvalsAt` but for the inner-product sum
without materialising `f * g`.
-/
def nativeHonestMessageEvalsAt
  {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
  {n : ℕ}
  (domain : List 𝔽)
  (f g : CPoly.CMvPolynomial n 𝔽)
  (i : Fin n)
  (challenges : Fin i.val → 𝔽)
  (c : 𝔽) : 𝔽 :=
  residualSumPair (𝔽 := 𝔽)
    (k := i.val + 1) (n := n)
    domain
    (openVars := numOpenVars (n := n) i)
    (hn := snoc_split_eq (n := n) i)
    (ch := Fin.snoc challenges c)
    (f := f) (g := g)

/-! ## Native statement -/

/-- Native two-oracle inner-product statement.

Bundles the two polynomials `f, g`, the summation domain, the claim,
and the three eval-form nodes used by the eval-form verifier. The
multilinearity bounds `f.degreeOf i ≤ 1` and `g.degreeOf i ≤ 1` make
the product `f * g` have individual degree `≤ 2`, matching the
`Fin 3` (i.e. `Fin (2 + 1)`) eval-tuple width. -/
structure NativeStatement
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) where
  domain          : List 𝔽
  claim           : 𝔽
  f               : CMvPolynomial n 𝔽
  g               : CMvPolynomial n 𝔽
  evalPoints      : Fin 3 → 𝔽
  evalPoints_inj  : Function.Injective evalPoints
  domain_sub      : ∀ x ∈ domain, ∃ k, evalPoints k = x
  domain_nodup    : domain.Nodup
  f_multilinear   : ∀ i : Fin n, f.degreeOf i ≤ 1
  g_multilinear   : ∀ i : Fin n, g.degreeOf i ≤ 1

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/-- Forget the multilinearity / eval-points data and view the native
statement as a thin-wrapper inner-product statement. -/
def NativeStatement.toInnerProduct {n : ℕ}
    (S : NativeStatement 𝔽 n) : InnerProductStatement 𝔽 n :=
  { domain := S.domain
    claim := S.claim
    f := S.f
    g := S.g
    domain_nodup := S.domain_nodup }

/-- A native statement is *valid* exactly when its thin-wrapper image
is — i.e. the claim equals the honest inner-product sum. -/
def NativeStatement.Valid {n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) : Prop :=
  S.toInnerProduct.Valid

/-! ## Per-summand and per-round equivalence to the thin wrapper -/

omit [DecidableEq 𝔽] in
/-- Per-point identity: `(f * g).eval pt = f.eval pt · g.eval pt`.
A direct restatement of `CMvPolynomial.eval_mul`, used internally by
the sum-level equivalence proof. -/
private lemma eval_mul_pt {n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (f g : CMvPolynomial n 𝔽) (pt : Fin n → 𝔽) :
    CMvPolynomial.eval pt (f * g)
      = CMvPolynomial.eval pt f * CMvPolynomial.eval pt g :=
  CPoly.eval_mul (p := f) (q := g) (vals := pt)

/-- `residualSumPair` agrees with `residualSumWithOpenVars` on the
product polynomial: walking the hypercube while multiplying inside
gives the same value as walking it on the symbolic product. -/
lemma residualSumPair_eq_residualSumWithOpenVars_mul
    {k n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (domain : List 𝔽)
    (openVars : ℕ)
    (hn : k + openVars = n)
    (ch : Fin k → 𝔽)
    (f g : CMvPolynomial n 𝔽) :
    residualSumPair (𝔽 := 𝔽) (k := k) (n := n)
        domain openVars hn ch f g
      =
    residualSumWithOpenVars (𝔽 := 𝔽) (k := k) (n := n)
        domain openVars hn ch (f * g) := by
  classical
  unfold residualSumPair residualSumWithOpenVars
  apply sum_over_domain_recursive_congr
  intro x
  exact (eval_mul_pt (n := n) f g
    (fun i => addCasesFun ch x (Fin.cast hn.symm i))).symm

/-- **Native ↔ thin-wrapper equivalence.**

The native eval-form prover message at round `i` and field point `c`
agrees with the thin-wrapper eval-form prover message obtained by
running `honestProverMessageEvalsAt` on the symbolic product `f * g`.

The proof folds through `residualSumPair_eq_residualSumWithOpenVars_mul`
followed by the definitional `honestProverMessageEvalsAt = residualSumWithOpenVars`.
-/
theorem nativeHonestMessageEvalsAt_eq_thinWrapper
    {n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (domain : List 𝔽)
    (f g : CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    (c : 𝔽) :
    nativeHonestMessageEvalsAt (𝔽 := 𝔽)
        domain f g i challenges c
      =
    honestProverMessageEvalsAt (𝔽 := 𝔽)
        domain (f * g) i challenges c := by
  unfold nativeHonestMessageEvalsAt honestProverMessageEvalsAt
  exact residualSumPair_eq_residualSumWithOpenVars_mul
    (𝔽 := 𝔽) (k := i.val + 1) (n := n)
    domain (numOpenVars (n := n) i)
    (snoc_split_eq (n := n) i)
    (Fin.snoc challenges c) f g

/-- Per-eval-node corollary: the three-tuple `qEvals` produced natively
agrees pointwise with the thin-wrapper eval tuple. -/
theorem nativeHonestMessageEvalsAt_tuple_eq_thinWrapper
    {n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (domain : List 𝔽)
    (f g : CMvPolynomial n 𝔽)
    (i : Fin n)
    (challenges : Fin i.val → 𝔽)
    (evalPoints : Fin 3 → 𝔽) :
    (fun k =>
      nativeHonestMessageEvalsAt (𝔽 := 𝔽)
        domain f g i challenges (evalPoints k))
      =
    (fun k =>
      honestProverMessageEvalsAt (𝔽 := 𝔽)
        domain (f * g) i challenges (evalPoints k)) := by
  funext k
  exact nativeHonestMessageEvalsAt_eq_thinWrapper
    (𝔽 := 𝔽) domain f g i challenges (evalPoints k)

/-! ## Eval-form bridge

When we want to plug a native statement into the eval-form
`PublicCoinProtocol`, we compose with `(f * g)` and feed the
multilinearity bounds through `degreeOf_mul_le_c` to discharge the
`degree_le` field for `d := 2`.
-/

omit [DecidableEq 𝔽] in
/-- Product of two multilinears has individual degree `≤ 2` in every
variable: `(f * g).degreeOf i ≤ f.degreeOf i + g.degreeOf i ≤ 1 + 1`. -/
private lemma indDegreeK_mul_multilinear_le
    {n : ℕ} [BEq 𝔽] [LawfulBEq 𝔽]
    (f g : CMvPolynomial n 𝔽)
    (hf : ∀ i : Fin n, f.degreeOf i ≤ 1)
    (hg : ∀ i : Fin n, g.degreeOf i ≤ 1)
    (i : Fin n) :
    indDegreeK (f * g) i ≤ 2 := by
  have hmul : (f * g).degreeOf i ≤ f.degreeOf i + g.degreeOf i :=
    SharpSAT.degreeOf_mul_le_c f g i
  exact le_trans hmul (Nat.add_le_add (hf i) (hg i))

/-- Lift a native inner-product statement to a `SumcheckProtocolStatementEvalForm`
on the symbolic product `f * g` with global degree bound `d := 2`. The
multilinearity bounds discharge `degree_le` via
`indDegreeK_mul_multilinear_le`. -/
def NativeStatement.toEvalFormStatement {n : ℕ}
    [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) :
    SumcheckProtocolStatementEvalForm 𝔽 n 2 :=
  { domain := S.domain
    claim := S.claim
    polynomial := S.f * S.g
    evalPoints := S.evalPoints
    evalPoints_inj := S.evalPoints_inj
    domain_sub := S.domain_sub
    domain_nodup := S.domain_nodup
    degree_le :=
      indDegreeK_mul_multilinear_le
        (𝔽 := 𝔽) (n := n) S.f S.g S.f_multilinear S.g_multilinear }

@[simp] lemma NativeStatement.toEvalFormStatement_domain
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) :
    S.toEvalFormStatement.domain = S.domain := rfl

@[simp] lemma NativeStatement.toEvalFormStatement_claim
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) :
    S.toEvalFormStatement.claim = S.claim := rfl

@[simp] lemma NativeStatement.toEvalFormStatement_polynomial
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) :
    S.toEvalFormStatement.polynomial = S.f * S.g := rfl

@[simp] lemma NativeStatement.toEvalFormStatement_evalPoints
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) :
    S.toEvalFormStatement.evalPoints = S.evalPoints := rfl

/-! ## Native completeness via Phase 4 ext

The IP framework's `Prover` is statement-keyed by `SumcheckProtocolStatementEvalForm`,
which carries a single `polynomial`. The "native" two-oracle algorithm is
therefore an *implementation* of the same mathematical object —
`sumcheckHonestProverEvalForm` applied to `S.toEvalFormStatement` produces
the same eval-form values as `nativeHonestMessageEvalsAt` on `(S.f, S.g)`,
without ever materialising `S.f * S.g` in the prover hot path. We pin
this equivalence and use Phase 4 ext's
`sumcheck_hasPerfectCompleteness_evalForm` to lift native completeness.

Soundness is **not** lifted here for the same reason Phase 4 ext deferred
its own soundness lift: the eval-form verifier's degree bound is uniform
`d`, while the symbolic verifier's bound is per-round `indDegreeK p i`,
and the lift through `liftEvalProverToSymbolic` loses information when
those differ. -/

/-- Validity in the native bundle implies validity of the lifted
`SumcheckProtocolStatementEvalForm`. By construction this is just `rfl` modulo
the simp lemmas on `toEvalFormStatement`. -/
theorem NativeStatement.toEvalFormStatement_claim_isCorrect
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) (h : S.Valid) :
    sumcheckClaimIsCorrectEvalForm S.toEvalFormStatement := by
  -- `sumcheckClaimIsCorrectEvalForm S.toEvalFormStatement` unfolds to
  -- `S.toEvalFormStatement.claim = honestClaim … S.toEvalFormStatement.polynomial`
  -- which by the simp lemmas equals `S.claim = honestClaim S.domain (S.f * S.g)`,
  -- which is definitionally `S.toInnerProduct.Valid = S.Valid`.
  exact h

/-- The IP-framework honest prover, evaluated on a native-derived
statement, agrees pointwise with the native algorithm. The only "work"
is `nativeHonestMessageEvalsAt_eq_thinWrapper` plus the simp lemmas on
`toEvalFormStatement`. -/
theorem sumcheckHonestProverEvalForm_respond_native
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) (i : Fin n) (chs : Fin i.val → 𝔽)
    (k : Fin 3) :
    (sumcheckHonestProverEvalForm (𝔽 := 𝔽) (n := n) (d := 2)).respond
        S.toEvalFormStatement i chs k
      =
    nativeHonestMessageEvalsAt (𝔽 := 𝔽) S.domain S.f S.g i chs (S.evalPoints k) := by
  show honestProverMessageEvalsAt S.toEvalFormStatement.domain
        S.toEvalFormStatement.polynomial i chs (S.toEvalFormStatement.evalPoints k)
      = nativeHonestMessageEvalsAt S.domain S.f S.g i chs (S.evalPoints k)
  rw [NativeStatement.toEvalFormStatement_domain,
      NativeStatement.toEvalFormStatement_polynomial,
      NativeStatement.toEvalFormStatement_evalPoints]
  exact (nativeHonestMessageEvalsAt_eq_thinWrapper
    (𝔽 := 𝔽) S.domain S.f S.g i chs (S.evalPoints k)).symm

/-- **Native two-oracle inner-product completeness.** For every valid
`NativeStatement`, the eval-form sumcheck (running on the bridged
`SumcheckProtocolStatementEvalForm` over `f * g`) accepts the honest prover with
probability 1.

Proof: direct lift through `sumcheck_hasPerfectCompleteness_evalForm`
from Phase 4 ext, using `toEvalFormStatement_claim_isCorrect` to turn
the native validity into eval-form correctness. -/
theorem nativeInnerProduct_perfectCompleteness
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n) (h : S.Valid) :
    probAccept
      (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := 2))
      S.toEvalFormStatement
      sumcheckHonestProverEvalForm = 1 :=
  sumcheck_hasPerfectCompleteness_evalForm S.toEvalFormStatement
    (S.toEvalFormStatement_claim_isCorrect h)

/-! ## Native soundness via Phase 4 conditional soundness

Phase 4 ext provides `sumcheck_hasSoundnessError_evalForm_uniform`:
under `UniformDegreePoly d st.polynomial` (every variable's individual
degree of the statement polynomial equals `d`), any eval-form adversary's
accept probability is bounded by `d·n/|𝔽|`. For native two-oracle
inner-product the statement polynomial is `f * g` and `d = 2`, so the
hypothesis becomes `∀ i, (f*g).degreeOf i = 2`.

**Caveat on applicability**: the uniform hypothesis is restrictive — it
requires every variable to appear non-trivially in *both* `f` and `g`
(so that `(f*g).degreeOf i = f.degreeOf i + g.degreeOf i = 2`). The
caller must establish this; we provide the lifted statement and let the
caller discharge `UniformDegreeMul` for the specific `(f, g)` pair at
hand. For arbitrary multilinear `(f, g)` without the uniform property,
soundness still holds with the looser symbolic bound
`maxIndDegree (f * g) · n / |𝔽| ≤ 2 · n / |𝔽|`, but the lift through
the IP-framework eval-form instance requires this hypothesis. -/

/-- **Native two-oracle inner-product soundness.** Under uniform-d=2 on
`f * g`, every prover (honest or adversarial) is bounded by `2·n/|𝔽|`. -/
theorem nativeInnerProduct_soundness
    {n : ℕ} [Fintype 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]
    (S : NativeStatement 𝔽 n)
    (hUniMul : UniformDegreePoly 2 (S.f * S.g))
    (P : Prover (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := 2)))
    (hFalse : ¬ S.Valid) :
    probAccept
      (sumcheckProtocolEvalForm (𝔽 := 𝔽) (n := n) (d := 2))
      S.toEvalFormStatement
      P
      ≤ (n : ℚ) * 2 / (fieldSize (𝔽 := 𝔽) : ℚ) := by
  -- `S.toEvalFormStatement.polynomial = S.f * S.g`, so uniform-d on the
  -- product transports directly. `hFalse` (¬ S.Valid) transports to
  -- (¬ sumcheckClaimIsCorrectEvalForm S.toEvalFormStatement) by the
  -- definitional bridge in `toEvalFormStatement_claim_isCorrect` (modus
  -- tollens of its forward direction).
  have hUni : UniformDegreePoly 2 S.toEvalFormStatement.polynomial := by
    intro i
    rw [NativeStatement.toEvalFormStatement_polynomial]
    exact hUniMul i
  have hClaim_false : ¬ sumcheckClaimIsCorrectEvalForm S.toEvalFormStatement := by
    intro hC
    -- sumcheckClaimIsCorrectEvalForm S.toEvalFormStatement is definitionally S.Valid
    exact hFalse hC
  have hbnd := sumcheck_hasSoundnessError_evalForm_uniform
    (𝔽 := 𝔽) (n := n) (d := 2)
    S.toEvalFormStatement hUni P hClaim_false
  -- The Phase 4 bound is `(n : ℚ) * (d : ℚ) / |𝔽|` with `d = 2`; same shape.
  simpa using hbnd

end InnerProduct
