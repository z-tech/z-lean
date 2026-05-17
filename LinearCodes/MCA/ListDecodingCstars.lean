/-
# Cstars-from-list construction

Group C of the BCGM25 §6.2 decomposition. Given a per-seed list of `L`
candidate codewords (the list-decoding analog of the unique-decoding
witness codeword), this file lifts the list to a family of `cstars`
parameterized by a "choice function" `Fin ℓ → Fin L` selecting one
candidate per seed.

Key contents:
* `exists_cstars_list_of_MDS` — for any choice function, produces an
  `ℓ`-tuple `cstars_fam choose : Fin ℓ → (Fin n → F)` of code elements
  whose `G.combine`-image at each distinguished seed `xs k` recovers
  the chosen candidate. Uses the MDS hypothesis on the generator to
  invert at the `ℓ` distinct seed values.

Depends on `LinearCodes.MCA.Case2Subtargets`. Used by
`ListDecodingCounting.lean` and ultimately by `ListDecodingMCA.lean`.
-/

import LinearCodes.MCA.Case2Subtargets

set_option linter.unusedSectionVars false

namespace LinearCodes

variable {F : Type*} [Field F] [DecidableEq F]
variable {S : Type*} [Fintype S] {n ℓ L : ℕ}

/-! ### C1: Multi-witness lift -/

/-- C1: For each "choice function" `Fin ℓ → Fin L`, exists `cstars` matching
the chosen codewords at each distinct seed. -/
theorem exists_cstars_list_of_MDS [DecidableEq S]
    {G : Generator F S ℓ} (hG_MDS : G.IsMDS)
    {c : Submodule F (Fin n → F)}
    (xs : Fin ℓ → S) (h_distinct : Function.Injective xs)
    (cs_list : Fin ℓ → Fin L → (Fin n → F))
    (h_cs : ∀ k ℓ_idx, cs_list k ℓ_idx ∈ c) :
    ∃ cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F),
      ∀ choose : Fin ℓ → Fin L,
        (∀ j, cstars_fam choose j ∈ c) ∧
        (∀ k, G.combine (xs k) (cstars_fam choose) = cs_list k (choose k)) := by
  classical
  choose cstars_fam h_cstars_fam using
    fun choose : Fin ℓ → Fin L => exists_cstars_of_MDS hG_MDS xs h_distinct
      (fun k => cs_list k (choose k)) (fun k => h_cs k (choose k))
  exact ⟨cstars_fam, h_cstars_fam⟩

/-! ### C2: List-version of bad-witness codeword equality -/

/-- C2: For each choice function and corresponding `cstars`, the chosen
codeword from each list bad-witness equals `G.combine (xs k) cstars`. -/
theorem bad_witness_list_cw_eq_combine_cstars
    [DecidableEq S]
    {G : Generator F S ℓ} (_hG_MDS : G.IsMDS) (_hℓ : 0 < ℓ)
    {c : Submodule F (Fin n → F)} {δ_C : ℕ} (_h_minDist : MinDistAtLeast c δ_C)
    (_us : Fin ℓ → (Fin n → F))
    {γ : ℚ} (_hγ_hi : γ * (ℓ + 1) < δ_C / n) (_hn : 0 < n)
    (xs : Fin ℓ → S) (_h_distinct : Function.Injective xs)
    (cs_list : Fin ℓ → Fin L → (Fin n → F))
    (_h_cs : ∀ k ℓ_idx, cs_list k ℓ_idx ∈ c)
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    (h_fam : ∀ choose : Fin ℓ → Fin L, ∀ k,
      G.combine (xs k) (cstars_fam choose) = cs_list k (choose k))
    (choose : Fin ℓ → Fin L) :
    ∀ k, cs_list k (choose k) = G.combine (xs k) (cstars_fam choose) := by
  intro k
  exact (h_fam choose k).symm

/-! ### C3: Per-choice Ttilde definition -/

/-- C3: For each choice function, the corresponding `Ttilde` set of coordinates
where `us` matches the chosen `cstars` family. -/
def Ttilde_choose
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    (choose : Fin ℓ → Fin L) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ∀ j, us j i = cstars_fam choose j i)

@[simp] theorem mem_Ttilde_choose
    (us : Fin ℓ → (Fin n → F))
    (cstars_fam : (Fin ℓ → Fin L) → Fin ℓ → (Fin n → F))
    (choose : Fin ℓ → Fin L) (i : Fin n) :
    i ∈ Ttilde_choose us cstars_fam choose ↔ ∀ j, us j i = cstars_fam choose j i := by
  simp [Ttilde_choose]

end LinearCodes
