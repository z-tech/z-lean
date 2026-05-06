/-
# Reed-Solomon → `IsListDecodable` bridge (skeleton)

This file is a placeholder for connecting the Reed-Solomon infrastructure
in `LinearCodes/ReedSolomonProperties.lean` (which works in `Array F`)
to the Phase B `IsListDecodable` predicate (which works in
`Submodule F (Fin n → F)`).

The bridge requires careful Array ↔ Fin function conversion; deferred to
future work.
-/

import LinearCodes.MCA.ListDecoding

namespace LinearCodes
-- bridge content: TBD
end LinearCodes
