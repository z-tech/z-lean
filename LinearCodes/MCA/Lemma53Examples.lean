/-
# Lemma 5.3 boundary-case numerical analysis

Concrete `#eval` examples that probe the boundary of the BCGM25 Lemma 5.3
formalization in `LinearCodes/MCA/Case2Subtargets.lean`
(`Ttilde_card_gt_of_MDS_aggregate`).

Parameters: `n = 5`, `ℓ = 2`, `γ = 0.4`, `F = ZMod 5`, `S = F`,
`G(x) = (1, x)` (the `affineLine` generator). The MDS-induced per-coord
zero-evading bound is `ℓ - 1 = 1`.

Threshold values:
  * `n · γ = 2`
  * `n · γ · (ℓ - 1) = 2`              (paper hypothesis: |B_set| > 2)
  * `(n · γ + 1) · (ℓ - 1) = 3`        (Lean hypothesis: |B_set| > 3)
  * `n · (1 - γ) = 3`                  (target conclusion: |Ttilde| ≥ 3)

The construction below realizes `(|B_set|, |Ttilde|) = (3, 2)`. This
falsifies *the paper bound applied to the Lean hypothesis shape*
(`B_set := {x : Δ ≤ nγ}`): the hypothesis `|B_set| > 2` is satisfied,
but the conclusion `|Ttilde| ≥ 3` fails.

See `LinearCodes/doc/lemma-5-3-numerical-analysis.md` for the full
analysis.
-/

import LinearCodes.MCA.Generators

set_option linter.unusedSectionVars false

namespace LinearCodes
namespace Lemma53Examples

/-- Field used in the example. -/
abbrev F : Type := ZMod 5

/-- Length of the codeword. -/
def n : ℕ := 5

/-- Output dimension of the generator. -/
def ℓ : ℕ := 2

/-- The `us` family: two vectors of length 5 over `ZMod 5`.
  `us 0 = (0, 0, 0, 4, 3)`, `us 1 = (0, 0, 1, 1, 1)`. -/
def us : Fin 2 → (Fin 5 → F)
  | 0 => ![0, 0, 0, 4, 3]
  | 1 => ![0, 0, 1, 1, 1]

/-- The `cstars` family: identically zero. (Codewords; zero is in any
linear code.) -/
def cstars : Fin 2 → (Fin 5 → F) := fun _ _ => 0

/-- Column-difference at coord `i`: `v(i) := us(i) - cstars(i) ∈ F^ℓ`.
With `cstars = 0`, `v(i) = (us 0 i, us 1 i)`. -/
def v (i : Fin 5) : Fin 2 → F
  | 0 => us 0 i
  | 1 => us 1 i

/-- The combined value `G(x) · us(i) = us 0 i + x * us 1 i`. -/
def combineUs (x : F) (i : Fin 5) : F := us 0 i + x * us 1 i

/-- The combined value `G(x) · cstars(i) = 0`. -/
def combineCstars (_x : F) (_i : Fin 5) : F := 0

/-- Agreement at `(x, i)`: holds iff `G(x) · v(i) = 0`. -/
def agreeAt (x : F) (i : Fin 5) : Bool :=
  decide (combineUs x i = combineCstars x i)

/-- Per-coordinate agreement set (over all seeds). -/
def agreeSeedsAt (i : Fin 5) : Finset F :=
  (Finset.univ : Finset F).filter (fun x => agreeAt x i)

/-- Per-seed agreement domain (over all coords). -/
def agreeCoordsFor (x : F) : Finset (Fin 5) :=
  (Finset.univ : Finset (Fin 5)).filter (fun i => agreeAt x i)

/-- The exact-agreement set `Ttilde := {i : ∀ j, us j i = cstars j i}`. -/
def Ttilde : Finset (Fin 5) :=
  (Finset.univ : Finset (Fin 5)).filter
    (fun i => decide (us 0 i = cstars 0 i) ∧ decide (us 1 i = cstars 1 i))

/-- The bad-seed set `B_set` (Lean-style): seeds whose agreement domain
has size ≥ `n(1-γ) = 3`. -/
def Bset : Finset F :=
  (Finset.univ : Finset F).filter (fun x => 3 ≤ (agreeCoordsFor x).card)

/-- The strict-paper bad-seed set: seeds with `Δ = 0` (the paper's `A`
when `t_param = e`). -/
def AsetStrict : Finset F :=
  (Finset.univ : Finset F).filter (fun x => 5 ≤ (agreeCoordsFor x).card)

/-! ### Sanity checks via `#eval`. -/

#eval (Ttilde.card, Bset.card, AsetStrict.card)
-- Expected: (2, 3, 0)

-- All seven cardinalities together: `Ttilde.card`, `Bset.card`,
-- `AsetStrict.card`, then `agreeCoordsFor x .card` for `x = 0, 1, 2, 3, 4`.
#eval ((Ttilde.card, Bset.card, AsetStrict.card),
       ((agreeCoordsFor 0).card,
        (agreeCoordsFor 1).card,
        (agreeCoordsFor 2).card,
        (agreeCoordsFor 3).card,
        (agreeCoordsFor 4).card))
-- Expected: ((2, 3, 0), (3, 3, 3, 2, 2))
-- |Ttilde| = 2, |B_set| = 3 (paper hyp 'b > 2' satisfied),
-- |Ttilde| = 2 < 3 = n(1-γ): Lean conclusion FAILS.

#eval ((agreeSeedsAt 0).card,   -- coord 0 ∈ Ttilde:  all 5 seeds agree
       (agreeSeedsAt 1).card,   -- coord 1 ∈ Ttilde:  all 5 seeds agree
       (agreeSeedsAt 2).card,   -- coord 2 ∉ Ttilde:  ≤ ℓ-1 = 1 seed agrees
       (agreeSeedsAt 3).card,   -- coord 3 ∉ Ttilde:  ≤ ℓ-1 = 1 seed agrees
       (agreeSeedsAt 4).card)   -- coord 4 ∉ Ttilde:  ≤ ℓ-1 = 1 seed agrees
-- Expected: (5, 5, 1, 1, 1)

end Lemma53Examples
end LinearCodes
