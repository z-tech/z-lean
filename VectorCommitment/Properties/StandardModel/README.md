# `Properties/StandardModel/` — reserved

This directory is **reserved for future standard-model security instances** that discharge the abstract Layer-2 typeclasses from [`VectorCommitment/Src/Security/`](../../Src/Security/) without invoking the random-oracle model.

It is currently empty by design.

## What goes here

When a paper or protocol formalization in the standard model arrives (e.g. a KZG-based polynomial commitment, Pedersen with DLog, or a CR-hash-based Merkle in the standard model), add instance files alongside their assumption declarations:

```
StandardModel/
├── Assumptions/
│   ├── CollisionResistance.lean    -- class CollisionResistantHash
│   ├── DiscreteLog.lean            -- class DLogHard
│   └── ...
└── Instances/
    ├── BindingCR.lean              -- HasPositionBinding under CR-hash assumption
    ├── HidingOneWay.lean           -- HasHiding under one-way-hash assumption
    ├── BindingPedersen.lean        -- HasPositionBinding under DLog (algebraic)
    └── ...
```

## Architectural discipline

* Each instance file targets a **specific commitment type + specific assumption**.
* Files here **must not import** anything from [`Properties/Probability/`](../Probability/) — that's the ROM lane. Standard-model and ROM live in parallel directories so the dependency boundary is visible at the file-tree level.
* Each file uses the same `class HasX V` declared in `Src/Security/`. The advantage / bound / proof shape mirrors the ROM instances but discharges the bound via cryptographic reduction (existential adversary against an underlying assumption) rather than via a probability bound over `RODistribution`.

## Mathematical note: equivocation

Not every property in `Src/Security/` is dischargeable in every model. In particular, **`HasEquivocation` for a hash-based commitment in the standard model is impossible** — hash-based commitments are statistically binding and cannot be equivocated without a trapdoor. Algebraic commitments (Pedersen, KZG) *can* discharge `HasEquivocation` in the standard model under their respective algebraic assumptions.

Higher-level protocol theorems consuming `HasEquivocation V` will simply fail typeclass synthesis for V values whose only instances live under `StandardModel/Instances/*` and exclude an equivocation file — which is the correct behavior.

## Status

* **Currently empty.** Closing the four ROM-instance sorries in [`Properties/Probability/Instances/`](../Probability/Instances/) is the priority before standard-model work begins.
* No standard-model paper is currently queued for formalization on this branch.
