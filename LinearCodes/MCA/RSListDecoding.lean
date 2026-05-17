/-
# Reed-Solomon → `IsListDecodable` bridge (GS-sharpened RS layer)

Connects the `Array F`-flavoured Reed-Solomon infrastructure
(`LinearCodes/ReedSolomon.lean`, `LinearCodes/ReedSolomonProperties.lean`)
to the abstract `Submodule F (Fin n → F)`-flavoured MCA framework
(`LinearCodes/MCA/`). This is the bridge that lets the Guruswami-Sudan
sharpened correlated-agreement bounds in `MCA/JohnsonBound.lean` and
`MCA/ListDecodingMCA.lean` flow back into RS-specific results.

## Submodule reformulation of the RS code

* `funMessagePoly` — `(Fin k → F) → Polynomial F` (function-form of `messagePoly`).
* `reedSolomonLinearMap` — the encoder as a `LinearMap`
  `(Fin k → F) →ₗ[F] (Fin n → F)`.
* `reedSolomonSubmodule` — its range, an `F`-submodule of `Fin n → F`.
* `reedSolomonSubmodule_isMDS` — the submodule is MDS with
  `Module.finrank = messageLength` and min-distance `≥ codeLength −
  messageLength + 1`.
* `reedSolomonSubmodule_isListDecodable_johnson` — squared-Johnson
  list-decoding bound for the RS code at the abstract layer (immediate
  application of `IsListDecodable_squared_johnson_MDS`).

## Array ↔ Fin function bridge

* `arrayToFun` — pointwise lift `Array F → (Fin n → F)` via `getD`.
* `reedSolomonEncode_eq_linearMap` /
  `arrayEncoded_mem_reedSolomonSubmodule` — match the Array-layer
  `reedSolomonEncode` codewords with the submodule layer.
* `combine_eq_linComb_funForm` / `linComb_arrayToFun_eq_combine` —
  identify the Array-layer `linComb` with the abstract
  `Generator.combine`.

## RS combination generator (GS Phase 1)

* `rsGenerator F l` — alias for `Generator.univariatePowers F l`, exposing
  `G(α) = (1, α, α², …, αˡ)` under the RS-specific name used by the
  FRI / STIR / WHIR family of proximity tests.
* `rsGenerator_apply` — `(rsGenerator F l) α i = α ^ i.val`.
* `rsGenerator_IsMDS` — alias of `Generator.univariatePowers_IsMDS`,
  giving the MDS witness for `rsGenerator F l` over fields of size
  `≥ l + 1`.

## RS-specialized list-decoding MCA bound (GS Phase 3)

* `rs_MCA_list_decoding_bound` — instantiation of the abstract
  `MCA_list_decoding_bound` (in `MCA/ListDecodingMCA.lean`) with the RS
  submodule, the squared-Johnson list-size `n²`, and the
  `Generator.univariatePowers F l` generator. The conclusion is the
  RS-flavoured seed-probability bound
  `n² · (max(n·γ, 1) + 1) · l / |F|`.
* `rs_some_alpha_evades_bad_event` — combines
  `rs_MCA_list_decoding_bound` with the field-size implication
  (`field_size_implies_some_alpha_witness`) to obtain the existence of a
  "good" seed `α` for which the MCA bad event fails. This is the
  RS-specific existence-of-good-seed statement consumed by FRI-family
  proximity tests.

## Case-(a) MCA for Reed-Solomon

`rs_MCA_caseA` is the canonical case-(a) MCA
statement for Reed-Solomon: under the case-(a) hypothesis (every `α`
gives a δ-close combination), it concludes `mcaAgreementWitness` for
field sizes `|𝔽| > O((l + 1) · n²)`. The bound uses the abstract
`(ℓ + 1) · n²` Johnson list-size from `MCA/JohnsonBound.lean` bridged
through the submodule infrastructure above.
-/

import LinearCodes.ReedSolomonProperties
import LinearCodes.MCA.JohnsonBound
import LinearCodes.MCA.Examples
import LinearCodes.MCA.ConcreteMDS
import LinearCodes.MCA.ListDecodingMCA

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type} [Field F]

/-! ### Step 1: Function-form messagePoly -/

/-- The polynomial associated with a `Fin k → F`-message:
`Σᵢ mᵢ · X^i`. -/
noncomputable def funMessagePoly {k : ℕ} (m : Fin k → F) : Polynomial F :=
  ∑ i : Fin k, Polynomial.C (m i) * Polynomial.X ^ (i : ℕ)

/-- `funMessagePoly` is additive. -/
theorem funMessagePoly_add {k : ℕ} (m1 m2 : Fin k → F) :
    funMessagePoly (m1 + m2) = funMessagePoly m1 + funMessagePoly m2 := by
  unfold funMessagePoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply, Polynomial.C_add, add_mul]

/-- `funMessagePoly` is homogeneous. -/
theorem funMessagePoly_smul {k : ℕ} (c : F) (m : Fin k → F) :
    funMessagePoly (c • m) = Polynomial.C c * funMessagePoly m := by
  unfold funMessagePoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, Polynomial.C_mul, mul_assoc]

/-- The natDegree of `funMessagePoly` is at most `k - 1`. -/
theorem funMessagePoly_natDegree_lt {k : ℕ} (m : Fin k → F)
    (h : funMessagePoly m ≠ 0) :
    (funMessagePoly m).natDegree < k := by
  refine (Polynomial.natDegree_lt_iff_degree_lt h).2 ?_
  unfold funMessagePoly
  exact Polynomial.degree_sum_fin_lt (n := k) (f := fun i : Fin k => m i)

/-- Coefficient extraction: `(funMessagePoly m).coeff i.val = m i`. -/
theorem funMessagePoly_coeff {k : ℕ} (m : Fin k → F) (i : Fin k) :
    (funMessagePoly m).coeff i.val = m i := by
  unfold funMessagePoly
  have hsum : (∑ x : Fin k, if i = x then m x else 0) = m i :=
    Fintype.sum_ite_eq i (fun x : Fin k => m x)
  simpa [Polynomial.coeff_C_mul_X_pow, Fin.ext_iff] using hsum

/-- High-coefficient vanishing. -/
theorem funMessagePoly_coeff_of_le {k : ℕ} (m : Fin k → F) (i : ℕ)
    (hi : k ≤ i) :
    (funMessagePoly m).coeff i = 0 := by
  by_cases hp0 : funMessagePoly m = 0
  · simp [hp0]
  · have hdeg : (funMessagePoly m).natDegree < k := funMessagePoly_natDegree_lt m hp0
    have h_lt : (funMessagePoly m).natDegree < i := lt_of_lt_of_le hdeg hi
    exact Polynomial.coeff_eq_zero_of_natDegree_lt h_lt

/-- `funMessagePoly` is the zero polynomial iff its message is zero. -/
theorem funMessagePoly_eq_zero_iff {k : ℕ} (m : Fin k → F) :
    funMessagePoly m = 0 ↔ m = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    funext i
    have hc : (funMessagePoly m).coeff i.val = 0 := by rw [h, Polynomial.coeff_zero]
    rw [funMessagePoly_coeff] at hc
    exact hc
  · intro h
    unfold funMessagePoly
    simp [h]

/-! ### Step 2: The encoder LinearMap and its range submodule -/

/-- The Reed-Solomon encoder, as a `LinearMap` from `Fin k → F` to
`Fin n → F` (with `k = messageLength`, `n = codeLength`), by polynomial
evaluation at the domain points. -/
noncomputable def reedSolomonLinearMap (cfg : ReedSolomonConfig F) :
    (Fin cfg.messageLength → F) →ₗ[F] (Fin cfg.codeLength → F) where
  toFun m := fun j : Fin cfg.codeLength =>
    (funMessagePoly m).eval (cfg.domain.getD j.val 0)
  map_add' m1 m2 := by
    funext j
    simp [funMessagePoly_add, Polynomial.eval_add]
  map_smul' c m := by
    funext j
    simp [funMessagePoly_smul, Polynomial.eval_mul, Polynomial.eval_C]

/-- Pointwise expansion of `reedSolomonLinearMap`. -/
@[simp] theorem reedSolomonLinearMap_apply (cfg : ReedSolomonConfig F)
    (m : Fin cfg.messageLength → F) (j : Fin cfg.codeLength) :
    reedSolomonLinearMap cfg m j =
      (funMessagePoly m).eval (cfg.domain.getD j.val 0) := rfl

/-- The Reed-Solomon code as a submodule of `Fin n → F` — the range of
the encoder linear map. -/
noncomputable def reedSolomonSubmodule (cfg : ReedSolomonConfig F) :
    Submodule F (Fin cfg.codeLength → F) :=
  LinearMap.range (reedSolomonLinearMap cfg)

/-- Membership in the RS submodule: a vector is a codeword iff it is the
evaluation of some message polynomial at the domain. -/
theorem mem_reedSolomonSubmodule_iff (cfg : ReedSolomonConfig F)
    (w : Fin cfg.codeLength → F) :
    w ∈ reedSolomonSubmodule cfg ↔
      ∃ m : Fin cfg.messageLength → F,
        ∀ j : Fin cfg.codeLength, w j =
          (funMessagePoly m).eval (cfg.domain.getD j.val 0) := by
  unfold reedSolomonSubmodule
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [← hm]
    rfl
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    funext j
    rw [reedSolomonLinearMap_apply]
    exact (hm j).symm

/-! ### Step 3: Min-distance bound for `reedSolomonSubmodule`

A nonzero codeword `w = encode m` (with `m ≠ 0`) has Hamming weight at
least `codeLength - messageLength + 1`. -/

/-- Helper: the domain points lifted as a `Fin codeLength → F` map are
injective if the underlying domain has distinct entries. -/
private theorem domain_injective_aux [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0) :
    Function.Injective (fun j : Fin cfg.codeLength => cfg.domain.getD j.val 0) := by
  intro i j hij
  have hi : i.val < cfg.domain.size := by simp [h_dom_size]
  have hj : j.val < cfg.domain.size := by simp [h_dom_size]
  by_contra h_ne
  have h_ne_fin : (⟨i.val, hi⟩ : Fin cfg.domain.size) ≠ ⟨j.val, hj⟩ := by
    intro h
    apply h_ne
    apply Fin.ext
    have := congrArg Fin.val h
    simpa using this
  exact h_distinct ⟨i.val, hi⟩ ⟨j.val, hj⟩ h_ne_fin hij

/-- Min-distance bound for the RS submodule. -/
theorem reedSolomonSubmodule_minDist [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0) :
    MinDistAtLeast (reedSolomonSubmodule cfg)
      (cfg.codeLength - cfg.messageLength + 1) := by
  intro w hw_mem hw_ne
  rw [mem_reedSolomonSubmodule_iff] at hw_mem
  rcases hw_mem with ⟨m, hm⟩
  -- m ≠ 0 because w ≠ 0.
  have hm_ne : m ≠ 0 := by
    intro hm_zero
    apply hw_ne
    funext j
    rw [hm j, hm_zero]
    have hzz : funMessagePoly (0 : Fin cfg.messageLength → F) = 0 :=
      (funMessagePoly_eq_zero_iff (0 : Fin cfg.messageLength → F)).mpr rfl
    rw [hzz, Polynomial.eval_zero]
    rfl
  -- If messageLength = 0, m : Fin 0 → F must equal 0 (only one inhabitant).
  have hk_pos : 0 < cfg.messageLength := by
    by_contra h_zero
    push_neg at h_zero
    have hk0 : cfg.messageLength = 0 := Nat.le_zero.mp h_zero
    apply hm_ne
    funext i
    exact (Fin.elim0 (hk0 ▸ i))
  set p : Polynomial F := funMessagePoly m with hp_def
  have hp_ne : p ≠ 0 := fun h_zero => hm_ne ((funMessagePoly_eq_zero_iff m).mp h_zero)
  have hp_deg : p.natDegree < cfg.messageLength := funMessagePoly_natDegree_lt m hp_ne
  -- Set of indices where w is zero corresponds to roots of p.
  set Z : Finset (Fin cfg.codeLength) :=
    Finset.univ.filter (fun j => w j = 0) with hZ_def
  have hZ_card_le : Z.card ≤ cfg.messageLength - 1 := by
    let evalAt : Fin cfg.codeLength → F := fun j => cfg.domain.getD j.val 0
    have h_inj := domain_injective_aux cfg h_dom_size h_distinct
    -- The image Z.image evalAt: distinct indices give distinct field
    -- elements, all of which are roots of p.
    have h_img_subset : (Z.image evalAt).val ⊆ p.roots := by
      intro x hx
      have hx_in : x ∈ Z.image evalAt := hx
      rcases Finset.mem_image.mp hx_in with ⟨j, hjZ, hjx⟩
      have hwj : w j = 0 := (Finset.mem_filter.mp hjZ).2
      have hp_root_at_x : p.eval x = 0 := by
        rw [← hjx]
        show p.eval (cfg.domain.getD j.val 0) = 0
        rw [hp_def, ← hm j]
        exact hwj
      exact (Polynomial.mem_roots hp_ne).2 hp_root_at_x
    have h_card_image : (Z.image evalAt).card = Z.card :=
      Finset.card_image_of_injective Z h_inj
    have h_card_le_deg : (Z.image evalAt).card ≤ p.natDegree :=
      Polynomial.card_le_degree_of_subset_roots h_img_subset
    have h_le : Z.card ≤ p.natDegree := by rw [← h_card_image]; exact h_card_le_deg
    omega
  -- Partition: |{w ≠ 0}| + |Z| = codeLength.
  have h_partition :
      (Finset.univ.filter (fun j : Fin cfg.codeLength => w j ≠ 0)).card +
        Z.card = cfg.codeLength := by
    have h_split := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin cfg.codeLength)))
        (p := fun j : Fin cfg.codeLength => w j ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin] at h_split
    have hZ_eq : Z = Finset.univ.filter (fun j : Fin cfg.codeLength => ¬ (w j ≠ 0)) := by
      apply Finset.ext
      intro j
      simp [Z]
    rw [hZ_eq]; exact h_split
  -- weight ≥ 1 because w ≠ 0 (some coordinate is nonzero).
  have h_weight_ge_one :
      1 ≤ (Finset.univ.filter (fun j : Fin cfg.codeLength => w j ≠ 0)).card := by
    apply Finset.card_pos.mpr
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    apply hw_ne
    funext j
    by_contra h_wj_ne
    have : j ∈ Finset.univ.filter (fun j : Fin cfg.codeLength => w j ≠ 0) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h_wj_ne⟩
    rw [h_empty] at this
    exact absurd this (Finset.notMem_empty _)
  unfold hammingWeight
  omega

/-! ### Step 4: Injectivity and dimension -/

/-- The encoder is injective when the domain is well-formed and big
enough (`messageLength ≤ codeLength`). Proof: a nonzero message yields
`funMessagePoly m ≠ 0` of degree `< messageLength`, hence with at most
`messageLength - 1` roots; but if `encode m = 0`, every domain point is
a root, giving `codeLength ≥ messageLength` distinct roots — too many. -/
theorem reedSolomonLinearMap_injective [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_le : cfg.messageLength ≤ cfg.codeLength) :
    Function.Injective (reedSolomonLinearMap cfg) := by
  rw [injective_iff_map_eq_zero]
  intro m h_zero
  by_contra hm_ne
  -- Establish polynomial structure: p := funMessagePoly m is nonzero.
  set p : Polynomial F := funMessagePoly m with hp_def
  have hp_ne : p ≠ 0 := fun h => hm_ne ((funMessagePoly_eq_zero_iff m).mp h)
  have hp_deg : p.natDegree < cfg.messageLength := funMessagePoly_natDegree_lt m hp_ne
  -- From h_zero: every domain point evaluates to 0.
  have h_eval_zero : ∀ j : Fin cfg.codeLength,
      p.eval (cfg.domain.getD j.val 0) = 0 := by
    intro j
    have := congr_fun h_zero j
    rw [reedSolomonLinearMap_apply] at this
    show p.eval (cfg.domain.getD j.val 0) = 0
    rw [hp_def]; exact this
  -- The image of evalAt over Finset.univ : Finset (Fin codeLength) gives codeLength
  -- distinct field elements, all roots of p.
  let evalAt : Fin cfg.codeLength → F := fun j => cfg.domain.getD j.val 0
  have h_inj := domain_injective_aux cfg h_dom_size h_distinct
  let imgSet : Finset F := (Finset.univ : Finset (Fin cfg.codeLength)).image evalAt
  have h_imgcard : imgSet.card = cfg.codeLength := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ, Fintype.card_fin]
  have h_subset : imgSet.val ⊆ p.roots := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, hjx⟩
    refine (Polynomial.mem_roots hp_ne).2 ?_
    show p.eval x = 0
    rw [← hjx]; exact h_eval_zero j
  have h_card_le_deg : imgSet.card ≤ p.natDegree :=
    Polynomial.card_le_degree_of_subset_roots h_subset
  rw [h_imgcard] at h_card_le_deg
  omega

/-- The dimension of the RS submodule is `messageLength`. -/
theorem reedSolomonSubmodule_finrank [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_le : cfg.messageLength ≤ cfg.codeLength) :
    Module.finrank F (reedSolomonSubmodule cfg) = cfg.messageLength := by
  unfold reedSolomonSubmodule
  rw [LinearMap.finrank_range_of_inj
      (reedSolomonLinearMap_injective cfg h_dom_size h_distinct h_le)]
  rw [Module.finrank_fin_fun]

/-! ### Step 5: `reedSolomonSubmodule` is MDS -/

/-- The Reed-Solomon submodule is MDS. -/
theorem reedSolomonSubmodule_isMDS [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_le : cfg.messageLength ≤ cfg.codeLength) :
    IsMDS (reedSolomonSubmodule cfg) cfg.messageLength :=
  ⟨reedSolomonSubmodule_finrank cfg h_dom_size h_distinct h_le,
   reedSolomonSubmodule_minDist cfg h_dom_size h_distinct⟩

/-! ### Step 6: Squared-Johnson list-decoding for RS -/

/-- The Reed-Solomon submodule is `(τ, n²)`-list-decodable whenever
`(n - τ)² > n · k`. -/
theorem reedSolomonSubmodule_isListDecodable_johnson
    [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_le : cfg.messageLength ≤ cfg.codeLength)
    {τ : ℕ}
    (h_johnson : (cfg.codeLength - τ) * (cfg.codeLength - τ) >
                 cfg.codeLength * cfg.messageLength) :
    IsListDecodable (reedSolomonSubmodule cfg) τ
      (JohnsonListSize cfg.codeLength) :=
  IsListDecodable_squared_johnson_MDS
    (reedSolomonSubmodule_isMDS cfg h_dom_size h_distinct h_le)
    h_johnson

/-! ### Step 7: Bridge between `Array F` codewords and the submodule -/

/-- The `Fin codeLength → F` view of an `Array F`. -/
def arrayToFun {n : ℕ} (a : Array F) : Fin n → F :=
  fun j => a.getD j.val 0

/-- The function-form of an `Array F` Reed-Solomon-encoded codeword
agrees with the LinearMap encoder applied to the function-form of the
message. -/
theorem reedSolomonEncode_eq_linearMap [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (msg : Array F) (h_size : msg.size = cfg.messageLength) :
    arrayToFun (n := cfg.codeLength) (reedSolomonEncode cfg msg) =
      reedSolomonLinearMap cfg
        (fun i : Fin cfg.messageLength => msg.getD i.val 0) := by
  funext j
  unfold arrayToFun
  rw [reedSolomonLinearMap_apply]
  -- LHS = evalPoly msg (cfg.domain.getD j.val 0).
  have h_jval : j.val < cfg.domain.size := by simp [h_dom_size]
  rw [reedSolomonEncode_getD (cfg := cfg) (msg := msg) (i := ⟨j.val, h_jval⟩)]
  rw [← messagePoly_eval]
  -- RHS = (funMessagePoly (·)).eval (cfg.domain.getD j.val 0).
  -- Show messagePoly msg = funMessagePoly (fun i => msg.getD i.val 0).
  have h_poly_eq :
      messagePoly msg =
        funMessagePoly (fun i : Fin cfg.messageLength => msg.getD i.val 0) := by
    apply Polynomial.ext
    intro n
    by_cases hn : n < cfg.messageLength
    · have hn_msg : n < msg.size := by rw [h_size]; exact hn
      have h_lhs : (messagePoly msg).coeff n = msg[n]'hn_msg :=
        messagePoly_coeff_fin msg ⟨n, hn_msg⟩
      have h_rhs : (funMessagePoly (fun i : Fin cfg.messageLength =>
            msg.getD i.val 0)).coeff n =
          (fun i : Fin cfg.messageLength => msg.getD i.val 0) ⟨n, hn⟩ :=
        funMessagePoly_coeff (fun i : Fin cfg.messageLength => msg.getD i.val 0) ⟨n, hn⟩
      rw [h_lhs, h_rhs]
      simp only
      rw [Array.getElem_eq_getD (xs := msg) (i := n) (h := hn_msg) (fallback := 0)]
    · push_neg at hn
      have h_lhs : (messagePoly msg).coeff n = 0 := by
        by_cases hp0 : messagePoly msg = 0
        · simp [hp0]
        · have hdeg : (messagePoly msg).natDegree < msg.size :=
            messagePoly_natDegree_lt_of_nonzero msg hp0
          rw [h_size] at hdeg
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hn)
      have h_rhs : (funMessagePoly (fun i : Fin cfg.messageLength =>
            msg.getD i.val 0)).coeff n = 0 :=
        funMessagePoly_coeff_of_le _ n hn
      rw [h_lhs, h_rhs]
  rw [h_poly_eq]

/-- The function-form of an Array-encoded codeword lies in the
`reedSolomonSubmodule`. -/
theorem arrayEncoded_mem_reedSolomonSubmodule [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (msg : Array F) (h_size : msg.size = cfg.messageLength) :
    arrayToFun (n := cfg.codeLength) (reedSolomonEncode cfg msg) ∈
      reedSolomonSubmodule cfg := by
  rw [reedSolomonEncode_eq_linearMap cfg h_dom_size msg h_size]
  unfold reedSolomonSubmodule
  exact ⟨_, rfl⟩

/-! ### Step 8: Johnson list-size as a `ncard` bound

Re-state the Johnson list-decoding result as an `ncard` bound on
the set of close codewords — useful as a staging lemma for future
sharpening of case-(a) MCA theorems. -/

/-- The number of RS codewords (in submodule form) within Hamming
distance `τ` of any received word `u` is at most `n²`, given the
Johnson hypothesis. Direct restatement of
`reedSolomonSubmodule_isListDecodable_johnson` unfolded to the
underlying `ncard`. -/
theorem reedSolomonSubmodule_johnson_ncard
    [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_le : cfg.messageLength ≤ cfg.codeLength)
    {τ : ℕ}
    (h_johnson : (cfg.codeLength - τ) * (cfg.codeLength - τ) >
                 cfg.codeLength * cfg.messageLength)
    (u : Fin cfg.codeLength → F) :
    {v : Fin cfg.codeLength → F |
        v ∈ reedSolomonSubmodule cfg ∧ hammingDistance u v ≤ τ}.ncard ≤
      cfg.codeLength ^ 2 := by
  have h := reedSolomonSubmodule_isListDecodable_johnson
    cfg h_dom_size h_distinct h_le h_johnson u
  rwa [JohnsonListSize_eq] at h

/-! ### Step 9: Bridge to the abstract `Generator` framework

Sub-target 1.1 (alias), Sub-target 1.2 (`combine` ↔ `linComb`),
Sub-target 1.3 (`IsMDS` alias). These connect the `Array F`-flavoured
RS proximity-test infrastructure (`linComb` from
`ReedSolomonProperties.lean`) with the abstract MCA framework
(`Generator F F (l+1)` from `MCA/Examples.lean`), so that
`MCA_list_decoding_bound` (in `MCA/ListDecodingMCA.lean`) can be applied
to RS list-decoding situations. -/

/-- The "RS combination generator": `G(α) = (1, α, α², …, αˡ)` viewed as
a `Generator F F (l + 1)`. This is the standard univariate-powers
generator used by the FRI-family proximity tests, specialised to the
Reed-Solomon list-decoding setting. -/
def rsGenerator (F : Type*) [Field F] (l : ℕ) : Generator F F (l + 1) :=
  Generator.univariatePowers F l

/-- The `i`-th coordinate of `rsGenerator F l` at seed `α` is `αⁱ`. -/
@[simp] theorem rsGenerator_apply {F : Type*} [Field F] {l : ℕ} (α : F)
    (i : Fin (l + 1)) :
    (rsGenerator F l) α i = α ^ i.val := rfl

/-! #### Sub-target 1.2: `combine` ↔ `linComb` bridge

`linComb cfg.codeLength fs α` (the `Array F` view) and
`(rsGenerator F l).combine α (arrayToFun ∘ fs)` (the abstract Generator
view) compute the same vector when `fs : Fin (l + 1) → Array F` and each
`fs i` has size `cfg.codeLength`.

The technical hurdle is that `linComb`'s definition in
`ReedSolomonProperties.lean` uses a `List.foldl` over `List.finRange l`,
while `Generator.combine` uses a `Finset.sum` over `Fin ℓ`. We pass via
`linComb_getD` and `finRange_foldl_eq_sum` to reconcile. -/

/-- Pointwise equality: the `j`-th coordinate of `linComb n fs α` (as a
function on `Fin n` via `arrayToFun`) equals the `j`-th coordinate of
`(rsGenerator F l).combine α (arrayToFun ∘ fs)`. -/
theorem combine_eq_linComb_funForm
    (cfg : ReedSolomonConfig F) {l : ℕ} (fs : Fin (l + 1) → Array F)
    (α : F) :
    (rsGenerator F l).combine α
        (fun i : Fin (l + 1) => arrayToFun (n := cfg.codeLength) (fs i)) =
      arrayToFun (n := cfg.codeLength) (linComb cfg.codeLength fs α) := by
  funext j
  -- LHS unfolds to the Finset.sum form.
  rw [Generator.combine_apply]
  -- RHS unfolds to the foldl form, then to the Finset.sum form via
  -- `finRange_foldl_eq_sum`.
  unfold arrayToFun
  rw [linComb_getD cfg.codeLength fs α j]
  rw [finRange_foldl_eq_sum
      (g := fun i : Fin (l + 1) => α ^ i.val * (fs i).getD j.val 0)]
  -- Both sides are now `∑ i : Fin (l+1), α ^ i.val * (fs i).getD j.val 0`.
  apply Finset.sum_congr rfl
  intro i _
  rw [rsGenerator_apply]

/-- Function-form bridge: when each `fs i` has size `cfg.codeLength`, the
`combine` of their `arrayToFun` representations equals the `arrayToFun`
of `linComb cfg.codeLength fs α`. (Same as `combine_eq_linComb_funForm`,
restated symmetrically for downstream use where `linComb` is on the
RHS.) -/
theorem linComb_arrayToFun_eq_combine
    (cfg : ReedSolomonConfig F) {l : ℕ} (fs : Fin (l + 1) → Array F)
    (α : F) :
    arrayToFun (n := cfg.codeLength) (linComb cfg.codeLength fs α) =
      (rsGenerator F l).combine α
        (fun i : Fin (l + 1) => arrayToFun (n := cfg.codeLength) (fs i)) :=
  (combine_eq_linComb_funForm cfg fs α).symm

/-! #### Sub-target 1.3: `IsMDS` for the RS combination generator

A direct alias of `Generator.univariatePowers_IsMDS` from
`MCA/ConcreteMDS.lean`, exposed under the `rsGenerator` name. -/

/-- The RS combination generator is MDS over fields with at least
`l + 1` elements. This is exactly `Generator.univariatePowers_IsMDS`
specialised to the Reed-Solomon list-decoding context. -/
theorem rsGenerator_IsMDS {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {l : ℕ} (h_card : l + 1 ≤ Fintype.card F) :
    (rsGenerator F l).IsMDS :=
  Generator.univariatePowers_IsMDS h_card

/-! ### Step 10: GS Phase 3 — list-decoding MCA bound for Reed-Solomon

The technical heart of the GS application. Three sub-targets:

* Sub-target 3.1 (`rs_MCA_list_decoding_bound`) — instantiate
  `MCA_list_decoding_bound` with the RS submodule, recovering the
  RS-flavoured bound `n²·(max(n·γ,1) + 1)·l / |F|`.
* Sub-target 3.2 (`field_size_implies_some_alpha_witness`) — pass from a
  `seedProb ≤ B/|F|` bound and `|F| > B` to the existence of a "good"
  seed (one for which the bad event fails).
* Sub-target 3.3 (`gamma_johnson_implies_hi`,
  `n_one_minus_gamma_eq_n_sub_delta`) — γ ↔ δ arithmetic relating the
  list-decoding γ-form to the RS distance δ. -/

/-! #### Sub-target 3.3a: the substitution `γ = δ / n` -/

/-- Arithmetic helper: with `γ = δ / n` and `n > 0`,
`n * (1 - γ) = n - δ` (in ℚ). -/
theorem n_one_minus_gamma_eq_n_sub_delta
    {n δ : ℕ} (hn : 0 < n) :
    (n : ℚ) * (1 - (δ : ℚ) / n) = (n : ℚ) - δ := by
  have hn_q : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  field_simp

/-- Arithmetic helper (Sub-target 3.3): the unique-decoding distance
`δ = n - k + 1` (in ℕ) is at most `n + 1`. -/
theorem rs_delta_le_codeLength
    (cfg : ReedSolomonConfig F) :
    cfg.codeLength - cfg.messageLength + 1 ≤ cfg.codeLength + 1 := by
  omega

/-- Arithmetic helper (Sub-target 3.3, ℕ form): from `h_johnson_τ`,
derive `messageLength ≤ codeLength`. The proof is a Nat
manipulation: from `(n - τ)² > n*k`, the LHS is `≤ n*n`, so `n*k < n*n`,
hence (for `n > 0`) `k < n`. We don't need `n > 0` as a hypothesis
because if `n = 0` then `(0 - τ)*(0 - τ) = 0` and `0 * k = 0`, but the
inequality `0 > 0` is impossible — so `n > 0` is implicit. -/
theorem rs_messageLength_le_codeLength_of_johnson
    (cfg : ReedSolomonConfig F)
    {τ : ℕ}
    (h_johnson : (cfg.codeLength - τ) * (cfg.codeLength - τ) >
                 cfg.codeLength * cfg.messageLength) :
    cfg.messageLength ≤ cfg.codeLength := by
  set n := cfg.codeLength
  set k := cfg.messageLength
  -- From (n - τ)² > n*k and (n - τ)² ≤ n*(n - τ) ≤ n*n, we get n*k < n*n.
  have hnt_le : n - τ ≤ n := Nat.sub_le _ _
  have h_sq_le : (n - τ) * (n - τ) ≤ n * (n - τ) := Nat.mul_le_mul_right _ hnt_le
  have h_sq_le' : n * (n - τ) ≤ n * n := Nat.mul_le_mul_left _ hnt_le
  have h_chain : n * k < n * n := lt_of_lt_of_le h_johnson (le_trans h_sq_le h_sq_le')
  -- n > 0, so we can cancel.
  have h_lt : k < n := by
    rcases Nat.lt_or_ge k n with h | h
    · exact h
    · exfalso
      have : n * n ≤ n * k := Nat.mul_le_mul_left _ h
      omega
  exact Nat.le_of_lt h_lt

/-! #### Sub-target 3.1: RS-specialized list-decoding MCA bound -/

/-- Sub-target 3.1: Instantiate `MCA_list_decoding_bound` for the RS
submodule with the squared-Johnson list-size `n²` and the
`Generator.univariatePowers F l` generator.

* `c = reedSolomonSubmodule cfg ...`
* `δ_C = n - k + 1` (from `reedSolomonSubmodule_minDist`)
* `L = n²` (from `reedSolomonSubmodule_isListDecodable_johnson`, given
  the Johnson hypothesis `(n - τ)² > n · k`)
* `G = Generator.univariatePowers F l`

The conclusion: the MCA bad event has seed-probability at most
`(n² · (max(n·γ, 1) + 1) · l) / |F|`. -/
theorem rs_MCA_list_decoding_bound
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F) (h_dom : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
        cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (hn : 0 < cfg.codeLength)
    {l : ℕ} (hl : 0 < l + 1)
    (h_field : l + 1 ≤ Fintype.card F)
    (us : Fin (l + 1) → (Fin cfg.codeLength → F))
    {τ : ℕ} (h_johnson_τ : (cfg.codeLength - τ) * (cfg.codeLength - τ) >
                          cfg.codeLength * cfg.messageLength)
    {γ : ℚ} (hγ_pos : 0 ≤ γ)
    (hγ_hi : γ * (l + 2) <
             ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) /
               cfg.codeLength)
    (h_radius : (cfg.codeLength : ℚ) * γ ≤ (τ : ℚ)) :
    seedProb (S := F) (fun α =>
      ∃ T : Finset (Fin cfg.codeLength), (T.card : ℚ) ≥ cfg.codeLength * (1 - γ) ∧
        InRestrictedCode (reedSolomonSubmodule cfg) T
          ((Generator.univariatePowers F l).combine α us) ∧
        ∃ j : Fin (l + 1), ¬ InRestrictedCode
          (reedSolomonSubmodule cfg) T (us j))
    ≤ (((cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * γ) 1 + 1) * ((l + 1 : ℕ) - 1 : ℚ)) /
          Fintype.card F) := by
  -- Derive auxiliary facts.
  have h_le : cfg.messageLength ≤ cfg.codeLength :=
    rs_messageLength_le_codeLength_of_johnson cfg h_johnson_τ
  -- Generator MDS hypothesis.
  have hG_MDS : (Generator.univariatePowers F l).IsMDS :=
    Generator.univariatePowers_IsMDS h_field
  -- Min-distance witness for the RS submodule.
  have h_minDist :
      MinDistAtLeast (reedSolomonSubmodule cfg)
        (cfg.codeLength - cfg.messageLength + 1) :=
    reedSolomonSubmodule_minDist cfg h_dom h_distinct
  -- List-decoding witness for the RS submodule (tight `n²` form).
  have h_LD :
      IsListDecodable (reedSolomonSubmodule cfg) τ
        (JohnsonListSize cfg.codeLength) :=
    reedSolomonSubmodule_isListDecodable_johnson cfg h_dom h_distinct h_le
      h_johnson_τ
  -- Unfold `JohnsonListSize cfg.codeLength = cfg.codeLength^2` for the
  -- bound's display form.
  have h_LD' :
      IsListDecodable (reedSolomonSubmodule cfg) τ
        (cfg.codeLength ^ 2) := by
    rw [← JohnsonListSize_eq]; exact h_LD
  -- The hypothesis hγ_hi already matches the ℕ-form δ_C / n once we
  -- recast `(l + 2)` as `((l+1) + 1)`.
  have hγ_hi' :
      γ * (((l + 1 : ℕ) : ℚ) + 1) <
        ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) / cfg.codeLength := by
    have h_eq : (((l + 1 : ℕ) : ℚ) + 1) = ((l + 2 : ℕ) : ℚ) := by push_cast; ring
    rw [h_eq]
    have h_eq2 : ((l + 2 : ℕ) : ℚ) = (l : ℚ) + 2 := by push_cast; ring
    rw [h_eq2]
    exact hγ_hi
  -- Apply MCA_list_decoding_bound.
  have h_main :=
    MCA_list_decoding_bound (Generator.univariatePowers F l) hG_MDS hl
      (reedSolomonSubmodule cfg) hn h_minDist h_LD' us hγ_pos hγ_hi' h_radius
  -- Massage the conclusion: shape `(L * (max ((n:ℚ)*γ) 1 + 1) * (ℓ - 1)) / |F|`.
  -- `L = n^2`, `ℓ = l + 1`, so `ℓ - 1 = l`. Need to align the
  -- multiplication order: theorem gives L * factor * (ℓ-1), we want
  -- n² * factor * (l+1-1). The two cast forms are equal in ℚ.
  have h_eq :
      ((cfg.codeLength ^ 2 : ℕ) : ℚ) *
        (max ((cfg.codeLength : ℚ) * γ) 1 + 1) *
        (((l + 1 : ℕ) : ℚ) - 1) =
      ((cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * γ) 1 + 1) *
        (((l + 1 : ℕ) - 1 : ℚ))) := by
    push_cast; ring
  rw [h_eq] at h_main
  exact h_main

/-! #### Sub-target 3.2: from `seedProb ≤ B/|F|` to existence of good seed -/

/-- Sub-target 3.2 (general): if every seed satisfies a predicate `P`,
then `seedProb P = 1`. The contrapositive form: if `seedProb P < 1`, then
some seed does *not* satisfy `P`. -/
theorem seedProb_lt_one_iff_exists_not
    {S : Type*} [Fintype S] [Nonempty S] (P : S → Prop) :
    seedProb P < 1 ↔ ∃ x : S, ¬ P x := by
  classical
  letI : DecidablePred P := Classical.decPred P
  unfold seedProb
  have hN_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  rw [div_lt_one hN_pos]
  constructor
  · intro h_lt
    -- filter.card < |S| means filter ≠ univ.
    have h_card_lt : ((Finset.univ : Finset S).filter P).card <
                      (Finset.univ : Finset S).card := by
      rw [Finset.card_univ]
      exact_mod_cast h_lt
    have h_ne : (Finset.univ : Finset S).filter P ≠ (Finset.univ : Finset S) := by
      intro h_eq
      rw [h_eq] at h_card_lt
      exact lt_irrefl _ h_card_lt
    -- Some x ∉ filter, hence ¬ P x.
    by_contra h_all
    push_neg at h_all
    apply h_ne
    apply Finset.ext
    intro x
    simp [h_all x]
  · rintro ⟨x, hx⟩
    have h_x_not_in : x ∉ (Finset.univ : Finset S).filter P := by
      simp [hx]
    have h_subset : (Finset.univ : Finset S).filter P ⊂ (Finset.univ : Finset S) := by
      refine ⟨Finset.subset_univ _, ?_⟩
      intro h_ss
      exact h_x_not_in (h_ss (Finset.mem_univ x))
    have h_card_lt :
        ((Finset.univ : Finset S).filter P).card < (Finset.univ : Finset S).card :=
      Finset.card_lt_card h_subset
    rw [Finset.card_univ] at h_card_lt
    exact_mod_cast h_card_lt

/-- Sub-target 3.2: if `seedProb P ≤ B / |S|` and `|S| > B`, then
`seedProb P < 1`, hence some seed does not satisfy `P`. -/
theorem field_size_implies_some_alpha_witness
    {S : Type*} [Fintype S] [Nonempty S] (P : S → Prop)
    {B : ℚ} (h_bound : seedProb P ≤ B / Fintype.card S)
    (h_field_large : (B : ℚ) < Fintype.card S) :
    ∃ x : S, ¬ P x := by
  rw [← seedProb_lt_one_iff_exists_not]
  have hS_pos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have h_div_lt : B / (Fintype.card S : ℚ) < 1 := by
    rw [div_lt_one hS_pos]
    exact h_field_large
  exact lt_of_le_of_lt h_bound h_div_lt

/-- Sub-target 3.2 (ℕ form): if `seedProb P ≤ N / |S|` for an ℕ bound
`N` and `|S| > N`, then some seed does not satisfy `P`. -/
theorem field_size_implies_some_alpha_witness_nat
    {S : Type*} [Fintype S] [Nonempty S] (P : S → Prop)
    {N : ℕ} (h_bound : seedProb P ≤ (N : ℚ) / Fintype.card S)
    (h_field_large : N < Fintype.card S) :
    ∃ x : S, ¬ P x :=
  field_size_implies_some_alpha_witness P h_bound (by exact_mod_cast h_field_large)

/-! #### Sub-target 3.3: γ ↔ δ arithmetic for the Johnson regime

When choosing `γ = δ/n` with `δ` the unique-decoding distance, the
Johnson hypothesis `(n - δ)² > n·k` (over the abstract MCA framework)
implies `γ * (l + 2) < δ_C / n` for `δ_C = n - k + 1`, provided the
`(l+2)` is small enough. The arithmetic is delicate because we are
mixing ℕ and ℚ subtractions; we expose only the cleanest version. -/

/-- Arithmetic helper (Sub-target 3.3): given the strict Johnson-style
inequality `δ * (l + 2) < n - k + 1` (in ℕ), conclude the
ℚ-form `γ * (l + 2) < (n - k + 1 : ℕ : ℚ) / n` with `γ = δ / n`. -/
theorem gamma_johnson_implies_hi
    {n k l δ : ℕ} (hn : 0 < n)
    (h_arith : δ * (l + 2) < n - k + 1) :
    ((δ : ℚ) / n) * ((l : ℚ) + 2) <
      ((n - k + 1 : ℕ) : ℚ) / n := by
  have hn_q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hn_q]
  have h_cast : (δ : ℚ) * ((l : ℚ) + 2) = ((δ * (l + 2) : ℕ) : ℚ) := by
    push_cast; ring
  rw [h_cast]
  exact_mod_cast h_arith

/-- Sub-target 3.3 sanity: with `γ = δ / n`, the agreement-set lower
bound `n * (1 - γ) = n - δ` (in ℚ; assumes `n > 0` to make division
well-defined). -/
theorem rs_gamma_to_agreement_size
    {n δ : ℕ} (hn : 0 < n) :
    (n : ℚ) * (1 - (δ : ℚ) / n) = (n : ℚ) - δ :=
  n_one_minus_gamma_eq_n_sub_delta hn

/-! #### Sub-target 3 capstone: combined RS list-decoding witness

Combining sub-targets 3.1 + 3.2 + 3.3: from the Johnson hypothesis on
`τ`, the field-size hypothesis `|F| > n²·(n+1)·l + 1`-ish (the explicit
threshold needed to make the bound `< 1`), and the small-γ regime, we
obtain the existence of a "good" seed `α` for which the bad event fails.

For sharpness, we take `γ = δ/n` with `δ` adapted to `h_johnson_τ`. The
exact inequality the user wants to feed into the bound is captured in
`gamma_johnson_implies_hi`. -/

/-- Sub-target 3 (capstone): combining the list-decoding MCA bound
(Sub-target 3.1) with the field-size implication (Sub-target 3.2),
whenever the field is large enough relative to the bound, some seed
makes the bad event fail. -/
theorem rs_some_alpha_evades_bad_event
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F) (h_dom : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
        cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (hn : 0 < cfg.codeLength)
    {l : ℕ} (hl : 0 < l + 1)
    (h_field : l + 1 ≤ Fintype.card F)
    (us : Fin (l + 1) → (Fin cfg.codeLength → F))
    {τ : ℕ} (h_johnson_τ : (cfg.codeLength - τ) * (cfg.codeLength - τ) >
                          cfg.codeLength * cfg.messageLength)
    {γ : ℚ} (hγ_pos : 0 ≤ γ)
    (hγ_hi : γ * (l + 2) <
             ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) /
               cfg.codeLength)
    (h_radius : (cfg.codeLength : ℚ) * γ ≤ (τ : ℚ))
    (h_field_large :
      (cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * γ) 1 + 1) * ((l + 1 : ℕ) - 1 : ℚ) <
      Fintype.card F) :
    ∃ α : F, ¬ (∃ T : Finset (Fin cfg.codeLength),
        (T.card : ℚ) ≥ cfg.codeLength * (1 - γ) ∧
        InRestrictedCode (reedSolomonSubmodule cfg) T
          ((Generator.univariatePowers F l).combine α us) ∧
        ∃ j : Fin (l + 1), ¬ InRestrictedCode
          (reedSolomonSubmodule cfg) T (us j)) := by
  -- The field is non-empty since |F| ≥ l + 1 ≥ 1.
  haveI : Nonempty F := by
    have h_card_pos : 0 < Fintype.card F := lt_of_lt_of_le hl h_field
    exact Fintype.card_pos_iff.mp h_card_pos
  -- Apply the Sub-target 3.1 bound.
  have h_bound :=
    rs_MCA_list_decoding_bound cfg h_dom h_distinct hn hl h_field us
      h_johnson_τ hγ_pos hγ_hi h_radius
  -- Apply Sub-target 3.2.
  exact field_size_implies_some_alpha_witness _ h_bound h_field_large

/-! ### Step 11: GS Phase 2 — submodule reformulation of `mcaGoodScalar`

The Array-form `mcaGoodScalar cfg fs δ α` says: there exists a message
`m` and a Reed-Solomon codeword `reedSolomonEncode cfg m` within
Hamming distance `δ` of the linear combination `linComb cfg.codeLength
fs α`. This step lifts that to its abstract function-form analogue
(Sub-target 2.1) and translates the case-A hypothesis
`∀ α, mcaGoodScalar cfg fs δ α` into the BCGM25 MCA bad-event template
suitable for combination with `MCA_list_decoding_bound` (Sub-target
2.2). -/

/-! #### Helpers: sizes and the `Array F` ↔ `Fin n → F` Hamming bridge -/

/-- The output of `linComb n fs α` always has size `n`. -/
@[simp] theorem linComb_size {n l : ℕ} (fs : Fin l → Array F) (α : F) :
    (linComb n fs α).size = n := by
  simp [linComb]

/-- Pointwise unfolding: `arrayToFun a i = a.getD i.val 0`. -/
@[simp] theorem arrayToFun_apply {n : ℕ} (a : Array F) (i : Fin n) :
    arrayToFun (n := n) a i = a.getD i.val 0 := rfl

/-- Hamming-distance bridge between the `Array F` form and the
`Fin n → F` form. Whenever `a, b` have size `n`, the `Array`-flavoured
`hammingDist a b` equals the abstract `hammingDistance` between their
`arrayToFun` images. -/
theorem hammingDist_eq_hammingDistance_arrayToFun [DecidableEq F]
    {n : ℕ} (a b : Array F) (ha : a.size = n) (hb : b.size = n) :
    hammingDist a b =
      hammingDistance (arrayToFun (n := n) a) (arrayToFun (n := n) b) := by
  classical
  -- Rewrite the Array form to `n - card{i // a.getD i.val 0 = b.getD i.val 0}`.
  have h_arr := hammingDist_eq_codeLength_sub_agreements a b n ha hb
  -- Convert `Fintype.card subtype` to `Finset.filter card`.
  have h_card_eq :
      Fintype.card {i : Fin n // a.getD i.val 0 = b.getD i.val 0} =
        (Finset.univ.filter
          (fun i : Fin n => a.getD i.val 0 = b.getD i.val 0)).card := by
    rw [Fintype.card_subtype]
  -- Express the abstract Hamming distance via the agreement set.
  have h_set_eq :
      agreementSet (arrayToFun (n := n) a) (arrayToFun (n := n) b) =
        Finset.univ.filter
          (fun i : Fin n => a.getD i.val 0 = b.getD i.val 0) := by
    apply Finset.ext
    intro i
    simp [agreementSet, arrayToFun]
  have h_fun :
      hammingDistance (arrayToFun (n := n) a) (arrayToFun (n := n) b) =
        n - (Finset.univ.filter
              (fun i : Fin n => a.getD i.val 0 = b.getD i.val 0)).card := by
    rw [hammingDistance_eq_n_sub_agreementSet, h_set_eq]
  rw [h_arr, h_card_eq, ← h_fun]

/-! #### Recovering an `Array F` from a `Fin k → F` message -/

/-- Build an `Array F` of size `k` from a function `Fin k → F`. -/
private noncomputable def funToArray {k : ℕ} (m : Fin k → F) : Array F :=
  Array.ofFn m

private theorem funToArray_size {k : ℕ} (m : Fin k → F) :
    (funToArray m).size = k := by
  simp [funToArray]

private theorem funToArray_getD {k : ℕ} (m : Fin k → F) (i : Fin k) :
    (funToArray m).getD i.val 0 = m i := by
  unfold funToArray
  have hi : i.val < (Array.ofFn m).size := by
    simp [Array.size_ofFn, i.isLt]
  rw [← Array.getElem_eq_getD (xs := Array.ofFn m) (i := i.val)
      (h := hi) (fallback := 0)]
  rw [Array.getElem_ofFn]

/-- Encoding the `funToArray` of a message function reproduces the
linear-map encoder applied to that function (in the `arrayToFun` view). -/
private theorem reedSolomonEncode_funToArray_eq_linearMap [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (m : Fin cfg.messageLength → F) :
    arrayToFun (n := cfg.codeLength)
      (reedSolomonEncode cfg (funToArray m)) =
        reedSolomonLinearMap cfg m := by
  rw [reedSolomonEncode_eq_linearMap cfg h_dom_size (funToArray m)
      (funToArray_size m)]
  congr 1
  funext i
  exact funToArray_getD m i

/-! #### Sub-target 2.1: Submodule reformulation of `mcaGoodScalar` -/

/-- **Sub-target 2.1**: Submodule reformulation of `mcaGoodScalar`.

The Array-form predicate `mcaGoodScalar cfg fs δ α` (∃ a message `m`
such that `reedSolomonEncode cfg m` is within Hamming distance `δ` of
`linComb cfg.codeLength fs α`) is equivalent to its abstract
function-form: ∃ a codeword `v ∈ reedSolomonSubmodule cfg` within
Hamming distance `δ` of the `arrayToFun` of
`linComb cfg.codeLength fs α`.

This is the bridge to plug into `MCA_list_decoding_bound`, which
operates entirely in the `Submodule F (Fin n → F)` framework. -/
theorem mcaGoodScalar_iff_submodule_close
    [DecidableEq F]
    (cfg : ReedSolomonConfig F) (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ) (α : F) :
    mcaGoodScalar cfg fs δ α ↔
      ∃ v ∈ reedSolomonSubmodule cfg,
        hammingDistance (arrayToFun (n := cfg.codeLength)
          (linComb cfg.codeLength fs α)) v ≤ δ := by
  constructor
  · -- Forward: pick `v = arrayToFun (reedSolomonEncode cfg m)`.
    rintro ⟨m, hm_size, hclose⟩
    refine ⟨arrayToFun (n := cfg.codeLength) (reedSolomonEncode cfg m),
            arrayEncoded_mem_reedSolomonSubmodule cfg h_dom_size m hm_size,
            ?_⟩
    have h_lin_size : (linComb cfg.codeLength fs α).size = cfg.codeLength :=
      linComb_size fs α
    have h_enc_size : (reedSolomonEncode cfg m).size = cfg.codeLength :=
      encode_size cfg h_dom_size m
    have h_bridge :=
      hammingDist_eq_hammingDistance_arrayToFun
        (linComb cfg.codeLength fs α) (reedSolomonEncode cfg m)
        h_lin_size h_enc_size
    rw [← h_bridge]
    exact hclose
  · -- Reverse: extract `m_fun : Fin messageLength → F` from `v ∈ rsSubmodule`,
    -- and let `m := funToArray m_fun`.
    rintro ⟨v, hv_mem, hclose⟩
    rw [mem_reedSolomonSubmodule_iff] at hv_mem
    rcases hv_mem with ⟨m_fun, hm_eq⟩
    refine ⟨funToArray m_fun, funToArray_size m_fun, ?_⟩
    have h_v_eq : v = arrayToFun (n := cfg.codeLength)
        (reedSolomonEncode cfg (funToArray m_fun)) := by
      rw [reedSolomonEncode_funToArray_eq_linearMap cfg h_dom_size m_fun]
      funext j
      rw [reedSolomonLinearMap_apply]
      exact (hm_eq j)
    have h_lin_size : (linComb cfg.codeLength fs α).size = cfg.codeLength :=
      linComb_size fs α
    have h_enc_size : (reedSolomonEncode cfg (funToArray m_fun)).size =
        cfg.codeLength :=
      encode_size cfg h_dom_size (funToArray m_fun)
    have h_bridge :=
      hammingDist_eq_hammingDistance_arrayToFun
        (linComb cfg.codeLength fs α)
        (reedSolomonEncode cfg (funToArray m_fun))
        h_lin_size h_enc_size
    rw [h_bridge, ← h_v_eq]
    exact hclose

/-! #### Sub-target 2.2: Bad-event statement under the case-A hypothesis -/

/-- Helper: any codeword `v ∈ c` close to `u` (within Hamming distance
`δ`) yields an agreement set `T = agreementSet u v` of size `≥ n - δ`
on which `u` lies in the restricted code. -/
private theorem inRestrictedCode_of_close [DecidableEq F]
    {n : ℕ} (c : Submodule F (Fin n → F))
    {u v : Fin n → F} (hv : v ∈ c) (δ : ℕ)
    (h : hammingDistance u v ≤ δ) :
    ∃ T : Finset (Fin n), n - δ ≤ T.card ∧ InRestrictedCode c T u := by
  classical
  refine ⟨agreementSet u v, ?_, ?_⟩
  · -- |agreement| + dist = n, dist ≤ δ ⟹ |agreement| ≥ n - δ.
    have h_eq := agreementSet_card_add_hammingDistance u v
    omega
  · refine ⟨v, hv, ?_⟩
    intro i hi
    -- `i ∈ agreementSet u v` means `u i = v i`, so `v i = u i`.
    exact (mem_agreementSet.mp hi).symm

/-- Arithmetic helper: cast the `(codeLength - δ : ℕ) ≤ T.card` bound
into the `ℚ` form `(codeLength : ℚ) * (1 - δ/codeLength) ≤ T.card`. -/
private theorem nat_card_to_rat_card
    {n δ : ℕ} (h_δ_le : δ ≤ n)
    {T_card : ℕ} (hT : n - δ ≤ T_card) :
    (T_card : ℚ) ≥ (n : ℚ) * (1 - (δ : ℚ) / n) := by
  by_cases hn : n = 0
  · -- n = 0: RHS simplifies to 0; `(T_card : ℚ) ≥ 0` is trivial.
    simp [hn]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
    have hn_q_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_q
    have h_cast : ((n - δ : ℕ) : ℚ) = (n : ℚ) - (δ : ℚ) := by
      rw [Nat.cast_sub h_δ_le]
    have hT_card_q : ((n : ℚ) - (δ : ℚ)) ≤ (T_card : ℚ) := by
      have : ((n - δ : ℕ) : ℚ) ≤ (T_card : ℚ) := by exact_mod_cast hT
      rw [h_cast] at this
      exact this
    have h_rw : (n : ℚ) * (1 - (δ : ℚ) / n) = (n : ℚ) - (δ : ℚ) := by
      field_simp
    rw [h_rw]
    exact hT_card_q

/-- **Sub-target 2.2**: From the case-A hypothesis `∀ α, mcaGoodScalar
cfg fs δ α` together with a per-α witness of a row failing the
restricted-code property, we get the BCGM25-style "every α makes the
bad event happen" statement: for every `α : F` there is a large
agreement set `T` such that the (function-form of the) linear
combination is in the restricted code on `T`, but some `fs j` is not.

The seedProb of this set is `1`, which combined with the upper bound
from `MCA_list_decoding_bound` (Sub-target 3.1) yields a contradiction
unless `|F|` is bounded by the list-size factor.

The "∃ j, ¬ InRestrictedCode" half is supplied as a hypothesis
(`h_bad_witness`): the eventual GS argument derives it from a
non-list-decodability assumption on the input rows. We state the
result with `fs : Fin (l + 1) → Array F` so that the `rsGenerator F l :
Generator F F (l + 1)` view aligns with `linComb` via
`combine_eq_linComb_funForm`. -/
theorem caseA_implies_bad_event_universal
    [DecidableEq F]
    (cfg : ReedSolomonConfig F) (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin (l + 1) → Array F)
    (δ : ℕ) (h_δ_le : δ ≤ cfg.codeLength)
    (h_caseA : ∀ α : F, mcaGoodScalar cfg fs δ α)
    (h_bad_witness : ∀ α : F,
      ∀ T : Finset (Fin cfg.codeLength),
        (cfg.codeLength - δ) ≤ T.card →
        InRestrictedCode (reedSolomonSubmodule cfg) T
          (arrayToFun (n := cfg.codeLength)
            (linComb cfg.codeLength fs α)) →
        ∃ j : Fin (l + 1),
          ¬ InRestrictedCode (reedSolomonSubmodule cfg) T
            (arrayToFun (n := cfg.codeLength) (fs j))) :
    ∀ α : F, ∃ T : Finset (Fin cfg.codeLength),
      (T.card : ℚ) ≥ cfg.codeLength * (1 - (δ : ℚ) / cfg.codeLength) ∧
      InRestrictedCode (reedSolomonSubmodule cfg) T
        ((rsGenerator F l).combine α
          (fun i : Fin (l + 1) =>
            arrayToFun (n := cfg.codeLength) (fs i))) ∧
      ∃ j : Fin (l + 1), ¬ InRestrictedCode (reedSolomonSubmodule cfg) T
        (arrayToFun (n := cfg.codeLength) (fs j)) := by
  intro α
  -- Step 1: extract submodule-form witness from `mcaGoodScalar`.
  have h_sub :=
    (mcaGoodScalar_iff_submodule_close (F := F) cfg h_dom_size fs δ α).mp
      (h_caseA α)
  rcases h_sub with ⟨v, hv_mem, hv_close⟩
  -- Step 2: build the agreement set `T` and the `linComb ∈ c|T` witness.
  rcases inRestrictedCode_of_close (reedSolomonSubmodule cfg) hv_mem δ hv_close
    with ⟨T, hT_card, hT_in⟩
  -- Step 3: harvest the failing-row index from `h_bad_witness`.
  obtain ⟨j, hj_nin⟩ := h_bad_witness α T hT_card hT_in
  -- Step 4: rewrite `arrayToFun (linComb …)` to `Generator.combine …`.
  have h_combine := combine_eq_linComb_funForm (F := F) cfg fs α
  refine ⟨T, ?_, ?_, j, hj_nin⟩
  · exact nat_card_to_rat_card h_δ_le hT_card
  · rw [h_combine]
    exact hT_in

/-- Variant of Sub-target 2.2: rather than expressing the bad event in
`(rsGenerator F l).combine` form, this flavour states it directly in
terms of `arrayToFun (linComb cfg.codeLength fs α)`. The two forms are
interchangeable via `combine_eq_linComb_funForm`. This form does not
require `fs` to be a `Fin (l + 1)`-family. -/
theorem caseA_implies_bad_event_universal_linComb
    [DecidableEq F]
    (cfg : ReedSolomonConfig F) (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ) (h_δ_le : δ ≤ cfg.codeLength)
    (h_caseA : ∀ α : F, mcaGoodScalar cfg fs δ α)
    (h_bad_witness : ∀ α : F,
      ∀ T : Finset (Fin cfg.codeLength),
        (cfg.codeLength - δ) ≤ T.card →
        InRestrictedCode (reedSolomonSubmodule cfg) T
          (arrayToFun (n := cfg.codeLength)
            (linComb cfg.codeLength fs α)) →
        ∃ j : Fin l,
          ¬ InRestrictedCode (reedSolomonSubmodule cfg) T
            (arrayToFun (n := cfg.codeLength) (fs j))) :
    ∀ α : F, ∃ T : Finset (Fin cfg.codeLength),
      (T.card : ℚ) ≥ cfg.codeLength * (1 - (δ : ℚ) / cfg.codeLength) ∧
      InRestrictedCode (reedSolomonSubmodule cfg) T
        (arrayToFun (n := cfg.codeLength) (linComb cfg.codeLength fs α)) ∧
      ∃ j : Fin l, ¬ InRestrictedCode (reedSolomonSubmodule cfg) T
        (arrayToFun (n := cfg.codeLength) (fs j)) := by
  intro α
  have h_sub :=
    (mcaGoodScalar_iff_submodule_close (F := F) cfg h_dom_size fs δ α).mp
      (h_caseA α)
  rcases h_sub with ⟨v, hv_mem, hv_close⟩
  rcases inRestrictedCode_of_close (reedSolomonSubmodule cfg) hv_mem δ hv_close
    with ⟨T, hT_card, hT_in⟩
  obtain ⟨j, hj_nin⟩ := h_bad_witness α T hT_card hT_in
  refine ⟨T, ?_, hT_in, j, hj_nin⟩
  exact nat_card_to_rat_card h_δ_le hT_card

/-! ### Step 12: Case-(a) form of MCA for RS

The canonical RS case-(a) MCA theorem, with the `O(n²)` Johnson
threshold matching BCGM25 Theorem 9.2 / BCIKS18 Theorem 1.2.

Strategy:

1. Apply `rs_some_alpha_evades_bad_event` (with `γ = δ/n`) to find a
   single seed `α*` for which the bad event does NOT occur.
2. The case-A hypothesis applied to `α*` gives (via
   `mcaGoodScalar_iff_submodule_close` + `inRestrictedCode_of_close`)
   a set `T` of size `≥ n - δ` such that
   `linComb (fs) α* ∈ (reedSolomonSubmodule cfg)|T`.
3. The negation of the bad event for `α*` (specialised to this `T`)
   says: ¬∃ j, ¬ InRestrictedCode (us j). Push negation inward:
   every row `arrayToFun (fs j) ∈ (reedSolomonSubmodule cfg)|T`.
4. For each row `j`, use `mem_reedSolomonSubmodule_iff` on the
   restricting codeword to extract a `Fin messageLength → F`
   message, package it as an `Array F` via `funToArray`, and verify
   the agreement on `T` using `reedSolomonEncode_funToArray_eq_linearMap`.
5. Cast the resulting `Finset (Fin codeLength)` witness to package
   it as an `mcaAgreementWitness`.

This file location is forced by import direction: the GS-sharpened
list-decoding bound (`rs_some_alpha_evades_bad_event`) lives here,
downstream of `ReedSolomonProperties.lean`, so the tight case-(a)
form must live here too. -/

open scoped BigOperators in
/-- **Maximum Correlated Agreement (case-(a) form for Reed-Solomon).**

The canonical case-(a) MCA theorem for RS, with the `O((l + 1) · n²)`
Johnson field-size threshold matching BCGM25 Theorem 9.2 / BCIKS18
Theorem 1.2. The hypothesis `h_field_size` matches the bound furnished by
`rs_some_alpha_evades_bad_event`, which uses the squared-Johnson
list-size `n²` rather than the `2^n` pigeonhole codomain count. -/
theorem rs_MCA_caseA
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F) (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
        cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (hn : 0 < cfg.codeLength)
    {l : ℕ} (fs : Fin (l + 1) → Array F)
    (_h_sizes : ∀ i : Fin (l + 1), (fs i).size = cfg.codeLength)
    (δ : ℕ) (h_δ_le : δ ≤ cfg.codeLength)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_field_lower : l + 1 ≤ Fintype.card F)
    (h_field_size :
      (cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * ((δ : ℚ) / cfg.codeLength)) 1 + 1) *
        ((l + 1 : ℕ) - 1 : ℚ) <
      Fintype.card F)
    (h_gamma_hi :
      ((δ : ℚ) / cfg.codeLength) * (l + 2) <
        ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) / cfg.codeLength)
    (h_caseA : ∀ α : F, mcaGoodScalar cfg fs δ α) :
    mcaAgreementWitness cfg fs δ := by
  classical
  -- The function-form view of the input rows.
  set us : Fin (l + 1) → (Fin cfg.codeLength → F) :=
    fun i => arrayToFun (n := cfg.codeLength) (fs i) with hus_def
  -- γ = δ/n is non-negative.
  have hγ_pos : (0 : ℚ) ≤ (δ : ℚ) / cfg.codeLength := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact_mod_cast Nat.zero_le _
  -- BCGM25 §6.2 semantic pin `n·γ ≤ τ`: with τ := δ and γ := δ/n,
  -- n·γ = n·(δ/n) = δ ≤ δ, discharged by `div_mul_cancel`.
  have h_radius_caseA :
      (cfg.codeLength : ℚ) * ((δ : ℚ) / cfg.codeLength) ≤ (δ : ℚ) := by
    have hn_q : (cfg.codeLength : ℚ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp hn
    rw [mul_comm, div_mul_cancel₀ _ hn_q]
  -- Step 1: apply `rs_some_alpha_evades_bad_event` with γ = δ/n.
  obtain ⟨α_star, h_no_bad⟩ :=
    rs_some_alpha_evades_bad_event cfg h_dom_size h_distinct hn
      (Nat.succ_pos l) h_field_lower us h_johnson hγ_pos h_gamma_hi
      h_radius_caseA h_field_size
  -- Step 2: case-A says α_star is good — extract the T witness.
  have h_α_good := h_caseA α_star
  -- Lift mcaGoodScalar to submodule form.
  have h_sub :=
    (mcaGoodScalar_iff_submodule_close (F := F) cfg h_dom_size fs δ α_star).mp h_α_good
  rcases h_sub with ⟨v_lc, hv_lc_mem, hv_lc_close⟩
  -- Get the agreement set T and the linComb-in-restricted-code witness.
  rcases inRestrictedCode_of_close (reedSolomonSubmodule cfg) hv_lc_mem δ hv_lc_close
    with ⟨T, hT_card_nat, hT_lin_in⟩
  -- Cast T-card bound to the ℚ form expected by the no-bad-event statement.
  have hT_card_rat :
      (T.card : ℚ) ≥ (cfg.codeLength : ℚ) * (1 - (δ : ℚ) / cfg.codeLength) :=
    nat_card_to_rat_card h_δ_le hT_card_nat
  -- The linComb (in `Generator.combine` form) is in the restricted code on T.
  have h_combine_eq := combine_eq_linComb_funForm (F := F) cfg fs α_star
  have hT_combine_in :
      InRestrictedCode (reedSolomonSubmodule cfg) T
        ((Generator.univariatePowers F l).combine α_star us) := by
    rw [show (Generator.univariatePowers F l) = rsGenerator F l from rfl]
    rw [hus_def]
    rw [h_combine_eq]
    exact hT_lin_in
  -- Step 3: ¬(bad event for α_star) means: NO T satisfies all three. So for
  -- our T, since the first two clauses hold, we cannot have ∃ j, ¬ InRestrictedCode.
  -- Push that negation inward.
  have h_all_rows :
      ∀ j : Fin (l + 1),
        InRestrictedCode (reedSolomonSubmodule cfg) T (us j) := by
    intro j
    by_contra hj_not
    apply h_no_bad
    refine ⟨T, hT_card_rat, hT_combine_in, j, hj_not⟩
  -- Step 4: convert each row's restricted-code membership into a per-row
  -- `Array F` message witness.
  -- T : Finset (Fin cfg.codeLength). domain.size = codeLength, so we can
  -- transport T to a Finset (Fin cfg.domain.size) and then back.
  -- Alternatively, build mcaAgreementWitness directly.
  refine ⟨T, ?_, ?_⟩
  · -- T.card-largeness: codeLength - T.card ≤ δ.
    have : cfg.codeLength - δ ≤ T.card := hT_card_nat
    omega
  · intro i
    -- Extract the codeword v_i ∈ reedSolomonSubmodule that agrees with fs i on T.
    obtain ⟨v_i, hv_i_mem, hv_i_agree⟩ := h_all_rows i
    -- Convert v_i to a message function via `mem_reedSolomonSubmodule_iff`.
    rw [mem_reedSolomonSubmodule_iff] at hv_i_mem
    rcases hv_i_mem with ⟨m_fun, hm_eq⟩
    refine ⟨funToArray m_fun, funToArray_size m_fun, ?_⟩
    intro j hjT
    -- Show: (fs i).getD j.val 0 = (reedSolomonEncode cfg (funToArray m_fun)).getD j.val 0.
    -- Use that v_i j = (fs i) j on T (i.e., for j ∈ T) via hv_i_agree, and
    -- v_i j = (funMessagePoly m_fun).eval (domain[j]) via hm_eq, and
    -- (reedSolomonEncode cfg (funToArray m_fun)).getD j.val 0 = same via
    -- `reedSolomonEncode_funToArray_eq_linearMap` + `reedSolomonLinearMap_apply`.
    have h_v_i_at_j : v_i j = (fs i).getD j.val 0 := by
      have := hv_i_agree j hjT
      -- this : v_i j = us i j
      rw [hus_def] at this
      simpa [arrayToFun] using this
    -- v_i j = (funMessagePoly m_fun).eval (cfg.domain.getD j.val 0)
    have h_v_i_eval : v_i j = (funMessagePoly m_fun).eval (cfg.domain.getD j.val 0) :=
      hm_eq j
    -- (reedSolomonEncode cfg (funToArray m_fun)).getD j.val 0
    --   = (funMessagePoly m_fun).eval (cfg.domain.getD j.val 0)
    have h_enc_eval :
        (reedSolomonEncode cfg (funToArray m_fun)).getD j.val 0 =
          (funMessagePoly m_fun).eval (cfg.domain.getD j.val 0) := by
      have h_atf :=
        reedSolomonEncode_funToArray_eq_linearMap (F := F) cfg h_dom_size m_fun
      -- arrayToFun (encode) = reedSolomonLinearMap (m_fun)
      have h_pt := congrFun h_atf j
      -- LHS: (encode (funToArray m_fun)).getD j.val 0
      -- RHS: reedSolomonLinearMap cfg m_fun j
      --    = (funMessagePoly m_fun).eval (cfg.domain.getD j.val 0)
      rw [reedSolomonLinearMap_apply] at h_pt
      simpa [arrayToFun] using h_pt
    -- Combine: (fs i).getD j.val 0 = v_i j = (funMessagePoly m_fun).eval ... =
    --   (encode (funToArray m_fun)).getD j.val 0.
    rw [← h_v_i_at_j, h_v_i_eval, ← h_enc_eval]

/-! ### Sanity checks: concrete instances of the new RS-MCA API -/

section SanityChecks

/-- Sanity 1: the RS combination generator `rsGenerator (ZMod 7) 2`
(univariate powers `(1, α, α²)`) is MDS, since `Fintype.card (ZMod 7) = 7
≥ 2 + 1 = 3`. Exercises `rsGenerator_IsMDS`. -/
example : (rsGenerator (ZMod 7) 2).IsMDS :=
  rsGenerator_IsMDS (by decide : 2 + 1 ≤ Fintype.card (ZMod 7))

/-- Sanity 2: the RS combination generator over `ZMod 5` with `l = 1`
(linear combiner `(1, α)`) is MDS. -/
example : (rsGenerator (ZMod 5) 1).IsMDS :=
  rsGenerator_IsMDS (by decide : 1 + 1 ≤ Fintype.card (ZMod 5))

/-- Sanity 3: the `rsGenerator_apply` simp lemma computes correctly.
At seed `α = 3` over `ZMod 7`, the second coordinate (index `2`) of the
`l = 2` univariate-powers generator equals `3 ^ 2 = 9 = 2`. -/
example : (rsGenerator (ZMod 7) 2) (3 : ZMod 7) ⟨2, by decide⟩ = 2 := by
  rw [rsGenerator_apply]
  decide

/-- Sanity 4: the γ ↔ δ arithmetic helper `n_one_minus_gamma_eq_n_sub_delta`
applies concretely at `n = 7`, `δ = 3`, giving `7 * (1 - 3/7) = 4`. -/
example : (7 : ℚ) * (1 - (3 : ℚ) / 7) = (7 : ℚ) - 3 :=
  n_one_minus_gamma_eq_n_sub_delta (n := 7) (δ := 3) (by decide)

/-! #### Sanity for `rs_MCA_caseA`

Concrete `ReedSolomonConfig F` values are awkward to construct as
constants (they require an `Array F` `domain` plus distinct-element
proofs), so the smoke tests below thread the config in as a hypothesis
and merely exercise the type signature and hypothesis structure of the
tight case-(a) RS-MCA theorem. These are pure API regression tests:
they catch signature drift rather than testing numerical content. -/

-- `ZMod 7` and `ZMod 11` need `Fact (Nat.Prime _)` to be a `Field`.
-- `local` keeps the instance scoped to this section; `private` does NOT
-- hide instances from typeclass unification, so the `local` form is what
-- actually limits the smoke-test fact to this file.
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Sanity 5: the tight case-(a) RS-MCA theorem applies over `ZMod 7`.
We feed in a `ReedSolomonConfig (ZMod 7)` and the matching Johnson +
field-size hypotheses, and check that we get back an
`mcaAgreementWitness`. This exercises end-to-end type elaboration of
`rs_MCA_caseA` over a concrete prime field. -/
example
    (cfg : ReedSolomonConfig (ZMod 7))
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
        cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (hn : 0 < cfg.codeLength)
    {l : ℕ} (fs : Fin (l + 1) → Array (ZMod 7))
    (h_sizes : ∀ i : Fin (l + 1), (fs i).size = cfg.codeLength)
    (δ : ℕ) (h_δ_le : δ ≤ cfg.codeLength)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_field_lower : l + 1 ≤ Fintype.card (ZMod 7))
    (h_field_size :
      (cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * ((δ : ℚ) / cfg.codeLength)) 1 + 1) *
        ((l + 1 : ℕ) - 1 : ℚ) <
      Fintype.card (ZMod 7))
    (h_gamma_hi :
      ((δ : ℚ) / cfg.codeLength) * (l + 2) <
        ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) / cfg.codeLength)
    (h_caseA : ∀ α : ZMod 7, mcaGoodScalar cfg fs δ α) :
    mcaAgreementWitness cfg fs δ :=
  rs_MCA_caseA cfg h_dom_size h_distinct hn fs
    h_sizes δ h_δ_le h_johnson h_field_lower h_field_size h_gamma_hi
    h_caseA

/-- Sanity 6: the tight case-(a) RS-MCA theorem applies with a fixed
`l = 1` (the minimum nontrivial linear-combiner regime, two rows
combined as `f₀ + α · f₁`) over `ZMod 7`. Checks that the
`Fin (l + 1) = Fin 2` row indexing elaborates and the
`((l + 1 : ℕ) - 1 : ℚ)` factor in the field-size hypothesis stays
well-typed at this boundary. -/
example
    (cfg : ReedSolomonConfig (ZMod 7))
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
        cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (hn : 0 < cfg.codeLength)
    (fs : Fin 2 → Array (ZMod 7))
    (h_sizes : ∀ i : Fin 2, (fs i).size = cfg.codeLength)
    (δ : ℕ) (h_δ_le : δ ≤ cfg.codeLength)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_field_size :
      (cfg.codeLength : ℚ) ^ 2 *
        (max ((cfg.codeLength : ℚ) * ((δ : ℚ) / cfg.codeLength)) 1 + 1) *
        ((1 + 1 : ℕ) - 1 : ℚ) <
      Fintype.card (ZMod 7))
    (h_gamma_hi :
      ((δ : ℚ) / cfg.codeLength) * (1 + 2) <
        ((cfg.codeLength - cfg.messageLength + 1 : ℕ) : ℚ) / cfg.codeLength)
    (h_caseA : ∀ α : ZMod 7, mcaGoodScalar cfg fs δ α) :
    mcaAgreementWitness cfg fs δ :=
  rs_MCA_caseA (l := 1) cfg h_dom_size h_distinct
    hn fs h_sizes δ h_δ_le h_johnson
    (by decide : 1 + 1 ≤ Fintype.card (ZMod 7)) h_field_size h_gamma_hi
    h_caseA

end SanityChecks

end LinearCodes
