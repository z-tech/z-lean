# AGENTS.md — Contributor & AI-Assistant Policy

Guidance for both human contributors and AI assistants (Claude Code,
Cursor, Copilot, etc.) working on this repo. Symlinked or duplicated
to `CLAUDE.md` for Claude-specific tooling.

## Repo layout (at-a-glance)

- [`SumcheckProtocol/`](SumcheckProtocol/) — sumcheck protocol
  (formalization + computable transcript). See
  [`SumcheckProtocol/doc/stability.md`](SumcheckProtocol/doc/stability.md)
  for stability tiers.
- [`LinearCodes/`](LinearCodes/) — `LinearCode` typeclass, Reed-Solomon
  encoder, BCGM25 MCA framework. See
  [`LinearCodes/README.md`](LinearCodes/README.md).
- [`InteractiveProtocol/`](InteractiveProtocol/) — generic
  `PublicCoinProtocol` infra, soundness/completeness packaging,
  `InIP` class.
- [`Upstream/`](Upstream/) — combinatorics and other helpers destined
  for Mathlib. Should remain Mathlib-importable in isolation.

## Build & validation

- Lean toolchain pinned at [`lean-toolchain`](lean-toolchain)
  (v4.29.1 at time of writing). CompPoly pinned to a specific `rev`
  in [`lakefile.lean`](lakefile.lean) — bump deliberately.
- CI rejects proof-term `sorry` and user-declared `axiom` across
  `LinearCodes/`, `Upstream/`, `SumcheckProtocol/`, and
  `InteractiveProtocol/`. See
  [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml).
- `native_decide` is allowed **only in `*/Tests/` directories**, where
  it backstops `#eval` oracle vectors. Any new `native_decide` outside
  `Tests/` will be flagged in review.

## Branch hygiene

- `main` is the publishable line. Feature work happens on
  `z-tech/<topic>` branches; AI-generated proof exploration lands on
  `ai-prover-<timestamp>` branches.
- Long-running refactor branches (`z-tech/refactor-*`) are merged via
  PR once the council punch list for that scope is exhausted, not
  earlier.
- Stashes accumulate; prune yours before merging.

## AI-assistant policy

The repo has accumulated ~14 `ai-prover-*` PRs. Lessons:

- **Heartbeat budget.** A bare `set_option maxHeartbeats <N>` above
  default (200000) is a code smell. Acceptable in `*/Tests/` files
  driven by `#eval` instance synthesis (typical: 800000). Anything
  ≥ 1M outside `Tests/` requires a comment with the root cause —
  ideally a TODO linking to an upstream PR if the blowup is in
  CompPoly / Mathlib.
- **Narrowed theorems.** If you prove a theorem that's weaker than
  its name suggests (e.g. round-0 only, multilinear-only,
  conditional-on-an-unproved-lemma), put the qualifier in the
  **first line** of the docstring, not buried near the end. Future
  readers should not have to read 30 lines to learn what's been
  proven.
- **No `sorry`.** Use a clearly named placeholder hypothesis instead,
  and add it to a TODO list in the file header. CI will refuse a
  `sorry` even in a TODO branch.
- **One concern per PR.** Refactors mixed with proof additions get
  bounced.

## Coding conventions

- `Type*` for universe binders unless a definition genuinely needs
  `Type 0`. The repo has been bitten by `{R : Type}` restricting
  downstream callers; see
  [`SumcheckProtocol/IP/SharpSAT/Arithmetize.lean`](SumcheckProtocol/IP/SharpSAT/Arithmetize.lean)
  for context on the workaround.
- Prefer `simp only [...]` over bare `simp` in proof-critical paths
  (calc steps, rewrites under binders). Bare `simp` is fine in
  `decide`-style closers.
- Don't put `@[simp]` on `instance` declarations. Put it on lemmas.
- Don't put `@[simp]` on `def`s — use a companion unfold lemma.
- New CompPoly extension lemmas (in `namespace CPoly`) should be
  marked `-- TO UPSTREAM` in a comment so they aren't lost when
  CompPoly absorbs them.

## Council reviews

Major subtrees get periodic "council of experts" reviews — multi-agent
cross-disciplinary critiques. The LinearCodes 2026-05-17 review and the
SumcheckProtocol 2026-05-18 review are recorded in
[`CHANGELOG.md`](CHANGELOG.md). The follow-up punch lists are tracked
in `*/doc/stability.md` and the issue tracker. New features should not
be added to a subtree with an open P0 punch list item — close those
first.
