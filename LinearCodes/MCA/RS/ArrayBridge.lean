/-
# Reed-Solomon: `Array F` ↔ `Submodule F (Fin n → F)` bridge

The plumbing connecting the `Array F`-flavoured Reed-Solomon
implementation (`ReedSolomon.lean`, `ReedSolomonProperties.lean`) to
the function/submodule view used by the BCGM25 MCA framework:

* Step 7 — `arrayEncoded_mem_reedSolomonSubmodule` (Array-form codewords
  live in the submodule) and `reedSolomonEncode_eq_linearMap`
  (`Array F` encoder agrees with the submodule `LinearMap`).
* Step 8 — `reedSolomonSubmodule_johnson_ncard` (concrete `ncard ≤ n²`
  bound on the Johnson radius set).
* Step 9 — Bridge to the abstract `Generator` framework: `rsGenerator`
  alias of `Generator.univariatePowers`, the `combine ↔ linComb`
  identity, and the MDS structural alias.

(Formerly the middle section of `LinearCodes/MCA/RS/`,
extracted as part of the P2 file-split refactor.)
-/

import LinearCodes.MCA.RS.Submodule

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F]

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
(`Generator F F (l+1)` from `MCA/Generators.lean`), so that
`MCA_list_decoding_bound` (in `MCA/ListDecoding/MCA.lean`) can be applied
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


end LinearCodes
