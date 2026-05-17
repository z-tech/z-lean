/-
# `LinearCodes.MCA.RSListDecoding` — back-compat shim

The Reed-Solomon MCA bridge (1419 lines in the original) was split into
three files for reviewability. This module re-exports them so existing
`import LinearCodes.MCA.RSListDecoding` calls keep working.

For new code, import the appropriate sub-file directly:

* `LinearCodes.MCA.RS.Submodule` — submodule reformulation of RS,
  min-distance, MDS, squared-Johnson list-decodability.
* `LinearCodes.MCA.RS.ArrayBridge` — `Array F` ↔ submodule plumbing,
  `rsGenerator` alias, `combine ↔ linComb`.
* `LinearCodes.MCA.RS.MCABound` — the RS-MCA bound itself
  (`rs_MCA_list_decoding_bound`, `rs_MCA_caseA`) plus sanity checks
  and reader-friendly aliases.
-/

import LinearCodes.MCA.RS.Submodule
import LinearCodes.MCA.RS.ArrayBridge
import LinearCodes.MCA.RS.MCABound
