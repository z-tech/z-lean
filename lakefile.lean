import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Sumcheck» where

lean_lib «InteractiveProtocol» where

lean_lib «VC» where

require "leanprover-community" / mathlib @ git "v4.28.0"
require CompPoly from git "https://github.com/z-tech/CompPoly" @ "z-tech/keep_add_rm_instHAddMaxNat"
