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

lean_lib «VectorCommitment» where

lean_lib «PCP» where

lean_lib «Kilian» where

require "leanprover-community" / mathlib @ git "v4.30.0-rc2"
-- Pinned to a specific rev (not `master`) so upstream churn doesn't break CI.
-- Bump deliberately when picking up new CompPoly features.
-- Temporarily on the z-tech fork until cmvpoly-univariate-evalext-and-lawfulbeq
-- merges to Verified-zkEVM/CompPoly master; switch back to upstream then.
require CompPoly from git "https://github.com/z-tech/CompPoly" @ "84e478d57f34effce0f46246068b96548975af08"
