import LinearCodes.LinearCode
import LinearCodes.ReedSolomon
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Smoke tests for the Reed-Solomon code

Concrete encoding examples over `ZMod 17` validated by `decide`. Force the
linear-code interface and the polynomial-evaluation kernel to elaborate on
real inputs.

See also `LinearCodes/ReedSolomonProperties.lean` for proven properties
(minimum distance, etc.) of the Reed-Solomon code.
-/

namespace __ReedSolomonTests__

open LinearCodes

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev 𝔽 := ZMod 17

/-! ### Hand-computed encoding

Message `[3, 1]` corresponds to the polynomial `p(X) = 3 + X`. Encoding
on the domain `[0, 1, 2, 3]` should produce `[3, 4, 5, 6]`. Code length
4, message length 2 — a `(4, 2)` Reed-Solomon code.
-/

def cfg : ReedSolomonConfig 𝔽 :=
  { messageLength := 2
    codeLength := 4
    domain := #[0, 1, 2, 3] }

def msg : Array 𝔽 := #[3, 1]

example : reedSolomonEncode cfg msg = #[3, 4, 5, 6] := by native_decide

/-! ### Through the typeclass interface

Construct a `ReedSolomonCode` from the config, then encode via the
`LinearCode` instance. -/

def rs : ReedSolomonCode 𝔽 := ⟨cfg⟩

example : LinearCode.encode (F := 𝔽) rs msg = #[3, 4, 5, 6] := by native_decide
example : LinearCode.messageLen (F := 𝔽) rs = 2 := by native_decide
example : LinearCode.codeLen (F := 𝔽) rs = 4 := by native_decide

/-! ### Quadratic message

`p(X) = 1 + 2·X + X²`, evaluated on `[0, 1, 2, 3, 4]`:
`[1, 4, 9, 16, 25]` — but 25 mod 17 = 8, so the last entry is `8`. -/

def cfgQuad : ReedSolomonConfig 𝔽 :=
  { messageLength := 3
    codeLength := 5
    domain := #[0, 1, 2, 3, 4] }

example : reedSolomonEncode cfgQuad #[1, 2, 1] = #[1, 4, 9, 16, 8] := by native_decide

/-! ### Security-bound smoke tests

A `(n=8, k=2)` Reed-Solomon code over an arbitrary field. Bounds:
* `minimumDistance = n − k + 1 = 7` (Singleton).
* `uniqueDecodingRadius = ⌊(d − 1) / 2⌋ = 3`.
* `johnsonRadius = n − ⌈√(n·k)⌉ − 1 = 8 − 4 − 1 = 3`. (`√16 = 4` exactly.)
* `mcaProximityGapError` (proven): the integer-tight bound from
  `rs_MCA_list_decoding_bound` is `n² · (max(δ,1) + 1) · (l-1) / q`. -/

def cfg82 : ReedSolomonConfig 𝔽 :=
  { messageLength := 2
    codeLength := 8
    domain := #[0, 1, 2, 3, 4, 5, 6, 7] }

def rs82 : ReedSolomonCode 𝔽 := ⟨cfg82⟩

example : LinearCode.minimumDistance (F := 𝔽) rs82 = 7 := by native_decide
example : LinearCodes.uniqueDecodingRadius (F := 𝔽) rs82 = 3 := by native_decide
example : LinearCode.johnsonRadius (F := 𝔽) rs82 = 3 := by native_decide

/-- Proven (Johnson-regime) bound: matches the bound proved by
`rs_MCA_list_decoding_bound`. At `l = 3, δ = 0, q = 17`:
`n² · (max(0,1) + 1) · (l-1) / q = 64 · 2 · 2 / 17 = 256/17 > 1`, clipped
to `1` (vacuous bound for these toy parameters — the proven Johnson
regime needs `q ≫ n²·l` to give a useful number). -/
example :
    LinearCode.mcaProximityGapError (F := 𝔽) rs82 .proven 3 0 17 = 1 := by
  native_decide

/-- Conjectured (capacity-regime) placeholder bound:
`(l − 1) · n / q = 2 · 8 / 17 = 16/17`. Not yet machine-checked. -/
example :
    LinearCode.mcaProximityGapError (F := 𝔽) rs82 .conjectured 3 0 17
      = 16 / 17 := by
  native_decide

/-- A larger field makes the proven Johnson bound non-vacuous. With
`q = 1009`, `l = 3`, `δ = 0`: `n² · 2 · (l-1) / q = 256/1009`. -/
example :
    LinearCode.mcaProximityGapError (F := 𝔽) rs82 .proven 3 0 1009
      = 256 / 1009 := by
  native_decide

/-- Rate of the (8, 2) code is 2/8 = 1/4. -/
example : LinearCodes.rate (F := 𝔽) rs82 = 1 / 4 := by native_decide

end __ReedSolomonTests__
