# Stale TODO / FIXME / parked audit — `LinearCodes/`

Audit performed 2026-05-07 on branch `z-tech/linear-codes`. Search terms:
`TODO`, `FIXME`, `XXX`, `HACK`, `deferred`, `parked` across `LinearCodes/**.lean`
and `LinearCodes/**.md`. Total hits: 11 (across 6 files).

This is a read-only audit; no source files were modified.

---

## Stale TODOs (recommended for removal)

- `LinearCodes/doc/rs-bridge-followups.md:15` — Heading "Update `paper-to-lean-map.md` 'Future / parked' table — RS bridge entry is stale" — **Stale**. The followup describes the entry as still reading "Stub-only; full bridge needs Array↔Fin function plumbing", but `paper-to-lean-map.md:381` already reads `Reed-Solomon → IsListDecodable bridge | **Landed** (Phases 1–4, full bridge in MCA/RSListDecoding.lean, 0 sorries) ...` with a full enumeration of the new API. The textual content of the parked-table row has been updated; only the *placement* (still inside the "Future / parked" section heading) remains. The followup item describes the current state inaccurately.
- `LinearCodes/doc/rs-bridge-followups.md:19` — Body of Item 2 claims "the bridge is no longer a stub" and proposes rewriting the entry — **Stale** for the same reason: the rewrite has already been applied to the cell content (line 381); the only residual is the section header (`## Future / parked`) above it. Item 2's "Proposed improvement" prose no longer matches the file it describes.
- `LinearCodes/doc/rs-bridge-followups.md:21` — Item 2 priority annotation ("HIGH — discoverability fix; misleads anyone scanning the parked table") — **Stale**. The parked-table cell now starts with `**Landed**` and lists every API symbol; a reader scanning the table is no longer misled about the bridge's status.
- `LinearCodes/doc/rs-bridge-followups.md:93` — Summary-table row 2 pointing at "`doc/paper-to-lean-map.md:303`" — **Stale** twice over: (a) the line number is wrong (the parked table is now at line 375, the RS row at line 381); (b) the action item ("document its current API") has already been performed inside the cell.

## Live TODOs (keep)

- `LinearCodes/MCA/Examples.lean:14` — "Quantitative zero-evading bounds (e.g. for `univariatePowers`, `ε_ZE = d/|S|` over sufficiently large fields) are deferred — those require polynomial identity-lemma machinery that we'll build alongside §6." — **Live**. The note describes a real outstanding piece of work; no `ε_ZE` quantitative bound for `univariatePowers` exists in the file or its companions, and the §6 polynomial-identity machinery has not yet landed. Keep.
- `LinearCodes/MCA/ConcreteMDS.lean:402` — "**TODO (deferred): `affineSpace_IsMDS` for `s ≥ 2`.**" — **Live**. The accompanying discussion (lines 400–432) correctly notes that the general `s ≥ 2` claim is mathematically false (the construction is only MDS for `s ∈ {0, 1}` or `s = 2 ∧ |F| = 2`), and the deferred-TODO documents legitimate refinement directions. Keep as a permanent design note rather than a literal TODO.
- `LinearCodes/MCA/Applications/STIR.lean:177` — "the deferred-TODO discussion in `LinearCodes/MCA/ConcreteMDS.lean`, lines ~296–323" — **Live in spirit**. The cross-reference is valid (it points at the deferred discussion which itself is Live); see "Misleading" entry below for the line-number staleness.
- `LinearCodes/MCA/Applications/STIR.lean:183` — "TODO: Generalize once `affineSpace_IsMDS` is proved for additional structural cases (e.g., `s = 2 ∧ |F| = 2`, or `s ≥ |F|^(s-1)`)." — **Live**. Tracks the Lean-side generalization that becomes possible if/when the structural special cases are proved; matches the deferred discussion in `ConcreteMDS.lean`. Keep.
- `LinearCodes/MCA/Applications/STIR.lean:261` — "TODO: Add this once explicit field-theory infrastructure (cyclotomic splitting in `ZMod`, primitive-root machinery) is available. Currently out of scope for the LinearCodes library." — **Live**. The A7 STIR-bound-tightness statement remains genuinely unproven (and the cyclotomic prerequisites are not in the library). Keep.
- `LinearCodes/MCA/Applications/STIR.lean:284` — "TODO: Add a `RestrictedReedSolomon` (or analogous) `Code` wrapper alongside the existing `ReedSolomonCode` instance and wire its `mcaProximityGapError` through `STIR_MCA_unique_decoding_bound`." — **Live**. The A8 wiring is still unfinished; the `LinearCode` instance for the RS submodule bridge has not been added (also tracked as Item 3 of `rs-bridge-followups.md`). Keep.
- `LinearCodes/doc/paper-to-lean-map.md:375` — "## Future / parked" section heading — **Live**. The section legitimately still contains parked items (Lemma 5.3 paper-tight bound, Bivariate / Guruswami-Sudan, WHIR multivariate). See "Misleading" below for one entry inside it that is no longer parked.

## Misleading

- `LinearCodes/MCA/Applications/STIR.lean:177` — "the deferred-TODO discussion in `LinearCodes/MCA/ConcreteMDS.lean`, lines ~296–323" — **Misleading line numbers**. The cross-referenced deferred-TODO is actually at lines ~400–432 of `ConcreteMDS.lean` (the `## affineSpace general (s ≥ 2)` block), not 296–323. Recommended rewording: replace the line range with a section/identifier reference, e.g. "see the deferred-TODO discussion under `affineSpace general (s ≥ 2)` in `LinearCodes/MCA/ConcreteMDS.lean`".
- `LinearCodes/doc/paper-to-lean-map.md:381` (inside the section that begins at line 375 `## Future / parked`) — The "Reed-Solomon → `IsListDecodable` bridge" row is marked "**Landed**" yet sits inside a section titled "Future / parked". The cell content is accurate, but the placement is misleading. Recommended rewording: lift the row out of the "Future / parked" table and into a "Reed-Solomon submodule bridge" subsection (parallel to the existing list-decoding capstones subsection), as already proposed by the now-stale Item 2 of `rs-bridge-followups.md`.

---

## Notes

- No `FIXME`, `XXX`, or `HACK` markers were found anywhere in `LinearCodes/`.
- The literal-string `parked` matches in `rs-bridge-followups.md` are all references to the misplaced parked-table row in `paper-to-lean-map.md`; they are tracking notes, not in-source TODOs.
- All `deferred` markers reference legitimate mathematical limitations (general `affineSpace_IsMDS` for `s ≥ 2` is false; quantitative `ε_ZE = d/|S|` for `univariatePowers` requires §6 machinery). They function as design documentation rather than work-in-progress markers.
