import LinearCodes.LinearCode
import LinearCodes.ReedSolomon
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Smoke tests for the Reed-Solomon code

Concrete encoding examples over `ZMod 17` validated by `decide`. Force the
linear-code interface and the polynomial-evaluation kernel to elaborate on
real inputs.
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
* `mcaProximityGapError` at `l = 3, q = 17`: `(l − 1)·d/q = 2·7/17 = 14/17`. -/

def cfg82 : ReedSolomonConfig 𝔽 :=
  { messageLength := 2
    codeLength := 8
    domain := #[0, 1, 2, 3, 4, 5, 6, 7] }

def rs82 : ReedSolomonCode 𝔽 := ⟨cfg82⟩

example : LinearCode.minimumDistance (F := 𝔽) rs82 = 7 := by native_decide
example : LinearCodes.uniqueDecodingRadius (F := 𝔽) rs82 = 3 := by native_decide
example : LinearCode.johnsonRadius (F := 𝔽) rs82 = 3 := by native_decide
example :
    LinearCode.mcaProximityGapError (F := 𝔽) rs82 3 0 17 = 14 / 17 := by
  native_decide

/-- Rate of the (8, 2) code is 2/8 = 1/4. -/
example : LinearCodes.rate (F := 𝔽) rs82 = 1 / 4 := by native_decide

end __ReedSolomonTests__
