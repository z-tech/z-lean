/-
# `LinearCodes.MCA.Case2Subtargets` — back-compat shim

The Case 2 sub-targets (1479 lines in the original) were split into
three files for reviewability. This module re-exports them so existing
`import LinearCodes.MCA.Case2Subtargets` calls keep working.

For new code, import the appropriate sub-file directly:

* `LinearCodes.MCA.Case2.Counting` — probabilistic / combinatorial primitives.
* `LinearCodes.MCA.Case2.MDSBridge` — MDS sub-targets D, F, E1, E2, E6, E8.
* `LinearCodes.MCA.Case2.Lemma53` — column-difference helpers + L5.3
  aggregate-counting bound + agreement-set companion.
-/

import LinearCodes.MCA.Case2.Counting
import LinearCodes.MCA.Case2.MDSBridge
import LinearCodes.MCA.Case2.Lemma53
