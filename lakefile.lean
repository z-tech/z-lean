import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

@[default_target]
lean_lib «SumcheckProtocol» where

lean_lib «InteractiveProtocol» where

@[default_target]
lean_lib «LinearCodes» where

@[default_target]
lean_lib «Upstream» where

-- Research-facing scratch (`LinearCodes/Research/`). Built in CI so it
-- catches API regressions, but excluded from the public umbrella
-- `LinearCodes.lean` so downstream users don't transitively import it.
@[default_target]
lean_lib «LinearCodes.Research» where
  roots := #[`LinearCodes.Research.Capstones]

-- User-facing examples / smoke tests (`LinearCodes/Examples/`). Same
-- reasoning as Research above: built in CI to catch encoder regressions,
-- not pulled in by `import LinearCodes`.
@[default_target]
lean_lib «LinearCodes.Examples» where
  roots := #[`LinearCodes.Examples.RSSmokeTest]

lean_lib «VC» where

require "leanprover-community" / mathlib @ git "v4.29.1"
-- Pinned to a specific rev (not `master`) so upstream churn doesn't break CI.
-- Bump deliberately when picking up new CompPoly features.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly" @ "01609714fa06e8f83485fe663f953d59c229477f"
