# Getting started with `LinearCodes`

A quick tour of the three things most callers actually do: encode a
Reed-Solomon message, read off security bounds for a configuration, and
plug those bounds into a STIR/WHIR-style profiler.

## What to import

The public umbrella is `LinearCodes.lean` at the repo root:

```lean
import LinearCodes
```

That pulls in the `LinearCode` typeclass, the `ReedSolomonCode`
instance, the MCA framework (BCGM25 §6.1 / §6.2 capstones), and the
STIR / WHIR / WARP application bridges. Research-facing files (the
in-progress capstone scratch under `LinearCodes/Research/`) are *not*
pulled in — that's intentional.

If you only need the typeclass and a single concrete code, you can be
narrower:

```lean
import LinearCodes.LinearCode      -- the typeclass + derived helpers
import LinearCodes.ReedSolomon     -- the RS instance
```

The MCA capstones live in `LinearCodes/MCA/`; if you only want the
abstract bounds (not the RS-specialised ones), import
`LinearCodes.MCA.Case2Capstone` and `LinearCodes.MCA.ListDecoding.MCA`
directly.

## 1. Encode a message

```lean
import LinearCodes
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open LinearCodes

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev 𝔽 := ZMod 17

def cfg : ReedSolomonConfig 𝔽 :=
  { messageLength := 2
    codeLength    := 4
    domain        := #[0, 1, 2, 3] }

def msg : Array 𝔽 := #[3, 1]  -- polynomial 3 + X

#eval reedSolomonEncode cfg msg  -- #[3, 4, 5, 6]
```

`reedSolomonEncode` is the Horner-loop encoder; it agrees with
`Polynomial.eval` at every domain point (theorem `messagePoly_eval` +
`reedSolomonEncode_getD` in `ReedSolomonProperties.lean`).

## 2. Read off security bounds for a configuration

The `LinearCode` typeclass exposes four computable security primitives
that return exact rationals:

```lean
def rs82 : ReedSolomonCode 𝔽 := ⟨{
  messageLength := 2
  codeLength    := 8
  domain        := #[0, 1, 2, 3, 4, 5, 6, 7]
}⟩

#eval LinearCode.minimumDistance (F := 𝔽) rs82
-- 7 (Singleton: n - k + 1 = 8 - 2 + 1)

#eval LinearCodes.uniqueDecodingRadius (F := 𝔽) rs82
-- 3 (⌊(d-1)/2⌋)

#eval LinearCode.johnsonRadius (F := 𝔽) rs82
-- 3 (n - ⌈√(n·k)⌉ - 1)

#eval LinearCodes.rate (F := 𝔽) rs82
-- 1/4 (k/n)
```

The MCA proximity-gap error needs a regime (`.proven` or
`.conjectured`), batch size `l`, agreement-slack `δ`, and field size
`q`:

```lean
#eval LinearCode.mcaProximityGapError (F := 𝔽) rs82 .proven 3 0 1009
-- 256/1009 (machine-checked via rs_MCA_list_decoding_bound)

#eval LinearCode.mcaProximityGapError (F := 𝔽) rs82 .conjectured 3 0 17
-- 16/17 (placeholder; relies on the capacity-achieving conjecture)
```

The `.proven` branch matches the integer-tight bound from
`rs_MCA_list_decoding_bound` (`MCA/RSListDecoding.lean`) — clipped to
`1` when the field is too small for the bound to be useful. See the
"Bounds delivered" section of the PR description for the bound shape.

## 3. Plug into a STIR-style profiler

The `Applications/STIR.lean` file wraps the MCA capstones for the
specific generator shape STIR uses. The main entry points:

- `STIR_MCA_unique_decoding_bound` — `MCA_unique_decoding_bound` for
  the univariate-powers generator over an RS code.
- `STIR_MCA_list_decoding_bound` — the list-decoding analogue.
- `STIR_MutualCorrelatedAgreement` — packages the bound into BCGM25's
  `MutualCorrelatedAgreement` predicate.
- `STIR_zeroEvading` — zero-evading specialisation for the STIR seed
  family.

A security profiler would chain `mcaProximityGapError` (per-round
bound) through the protocol's round count and per-round overhead to
land on a final bit-security number.

## Where to look next

- **Reed-Solomon properties** (`ReedSolomonProperties.lean`): the seven
  formal properties proved about the encoder.
- **MCA / RS bridge** (`MCA/RSListDecoding.lean`): the proven RS-MCA
  bounds backing the `.proven` typeclass branch.
- **Tests** (`Tests.lean`): hand-computed encoding examples and
  security-bound smoke tests; good as reading material.
- **Paper-to-Lean map** (`doc/paper-to-lean-map.md`): theorem-by-theorem
  mapping from BCGM25 (ePrint 2025/2051) to the Lean codebase.
