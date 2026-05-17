/-
# Reed-Solomon as a `Submodule F (Fin n → F)`

The submodule reformulation of the Reed-Solomon code, supplying the
abstract-MCA framework with the right shape:

* Step 1 — Function-form `messagePoly` for `Fin k → F` messages.
* Step 2 — The encoder `LinearMap` and its range `reedSolomonSubmodule`.
* Step 3 — Min-distance bound via Lagrange (`reedSolomonSubmodule_minDist`).
* Step 4 — Injectivity and dimension (`reedSolomonLinearMap_injective`,
  `reedSolomonSubmodule_finrank`).
* Step 5 — `reedSolomonSubmodule_isMDS`.
* Step 6 — Squared-Johnson list-decodability for RS
  (`reedSolomonSubmodule_isListDecodable_johnson`).

This is the "pure submodule" layer; the array-bridge to the `Array F`
encoder lives in `MCA/RS/ArrayBridge.lean`, and the MCA bound itself in
`MCA/RS/MCABound.lean`. (Formerly the head of
`LinearCodes/MCA/RS/`, extracted as part of the P2
file-split refactor.)
-/

import LinearCodes.ReedSolomonProperties
import LinearCodes.MCA.JohnsonBound
import LinearCodes.MCA.Generators
import LinearCodes.MCA.ConcreteMDS
import LinearCodes.MCA.ListDecoding.MCA

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F]

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
    rcases Finset.mem_image.mp (Finset.mem_val.mp hx) with ⟨j, _, hjx⟩
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


end LinearCodes
