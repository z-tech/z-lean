/-
Copyright (c) 2026 LeanStuff contributors. All rights reserved.
-/
import PCP.Src.Trait
import VectorCommitment.Src.Trait

/-!
# Kilian's protocol — the 3-message compilation of a PCP via a vector commitment

J. Kilian (1992) compiles a PCP `P` into a 3-message public-coin
interactive argument using a vector commitment `V`:

1. **Prover** commits to the full PCP string via `V.commit`, sending
   the root.
2. **Verifier** sends a random challenge `ρ` (= the PCP verifier's
   randomness).
3. **Prover** replies with claimed values at the PCP-verifier-queried
   positions, plus the VC opening proof for those positions.

The verifier accepts iff (a) every opening verifies under `V.check`
and (b) the PCP verifier accepts the opened values on randomness `ρ`.

This file declares the protocol's data types — the transcript shape,
the honest prover, and the verifier. The soundness theorem (Theorem 5.1
of [eprint 2024/1434](https://eprint.iacr.org/2024/1434)) is stated in
[`Kilian/Properties/Theorem51.lean`](../Properties/Theorem51.lean); it
binds abstractly on `[PCPSystem P]` together with `[HasPositionBinding
V]` from `VectorCommitment/Src/Security/`, so the theorem statement is
model-neutral and the bound is `ε_PCP(n) + bindingError κ q + ε`.

## Notes on `Alphabet` matching

Kilian compiles a PCP whose `Alphabet` matches the VC's `Alphabet` —
the prover commits to a `List (PCPSystem.Alphabet P)` via the VC, so we
need `PCPSystem.Alphabet P = VectorCommitment.Alphabet V` (or a
coercion). We expose this as the small typeclass `KilianCompatible`
below; downstream definitions assume it.
-/

namespace Kilian

/-- A small compatibility constraint: the PCP's alphabet matches the
    VC's alphabet (so a PCP string can be committed to), and the VC's
    index type matches `ℕ` (the natural index type of a PCP's positions).
    The simplest realisation sets both equal; coercion-based
    instantiations are also fine. -/
class KilianCompatible (P V : Type) [PCPSystem P] [VectorCommitment V] where
  alphabet_eq : PCPSystem.Alphabet P = VectorCommitment.Alphabet V
  index_eq : ℕ = VectorCommitment.Index V

namespace KilianCompatible

variable {P V : Type} [PCPSystem P] [VectorCommitment V] [KilianCompatible P V]

/-- Cast a list of PCP-alphabet symbols to VC-alphabet symbols. -/
def castAlphabet (xs : List (PCPSystem.Alphabet P)) :
    List (VectorCommitment.Alphabet V) :=
  (KilianCompatible.alphabet_eq (P := P) (V := V)) ▸ xs

/-- Inverse: cast a VC-alphabet list to PCP-alphabet. -/
def uncastAlphabet (xs : List (VectorCommitment.Alphabet V)) :
    List (PCPSystem.Alphabet P) :=
  (KilianCompatible.alphabet_eq (P := P) (V := V)).symm ▸ xs

/-- Cast a list of natural-number positions to VC indices. -/
def castIndex (ns : List ℕ) : List (VectorCommitment.Index V) :=
  (KilianCompatible.index_eq (P := P) (V := V)) ▸ ns

end KilianCompatible

variable {P V : Type} [PCPSystem P] [VectorCommitment V] [KilianCompatible P V]

/-- A complete Kilian transcript: the three protocol messages.

    Message-1 = commitment, Message-2 = randomness (verifier's coin),
    Message-3 = (values, proof). -/
structure Transcript (P V : Type) [PCPSystem P] [VectorCommitment V] where
  /-- Message 1: prover's commitment to the PCP. -/
  commitment : VectorCommitment.Commitment V
  /-- Message 2: verifier's randomness. -/
  randomness : PCPSystem.Randomness P
  /-- Message 3, part a: claimed PCP values at the queried positions. -/
  values : List (PCPSystem.Alphabet P)
  /-- Message 3, part b: the VC opening proof for those positions. -/
  proof : VectorCommitment.Proof V

end Kilian
