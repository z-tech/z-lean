import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Rat.Defs

/-!
# Linear-code interface

Lean 4 analogue of the `LinearCode<F>` Rust trait from `dmpierre/ark-codes`,
extended with security-profiling primitives that downstream proximity-test
protocols (FRI, STIR, WHIR, Brakedown, …) consume.

A code is a *type* `Code` together with a `Config` type, an encoder, and
declared bounds:

* `messageLen` / `codeLen` — basic shape.
* `minimumDistance` — Hamming-distance lower bound on distinct codewords.
* `johnsonRadius` — list-decoding radius beyond unique decoding.
* `mcaProximityGapError` — BCIKS18-style correlated-agreement error bound,
  parameterised by batch size, distance, and field size.

The bounds are returned as `ℕ` for radii and `ℚ` for probabilities so a
security profiler can call them on concrete configurations and chain
them through per-protocol soundness formulas without floating-point
error. Each concrete code (`ReedSolomonCode`, future `BrakedownCode`, …)
fills in its own formulas; helpers like `rate` and `uniqueDecodingRadius`
are derived once at the interface level.
-/

namespace LinearCodes

/-- Security regime for proximity-gap analysis. The two modes correspond to
the two ways soundness is reported in the FRI / STIR / WHIR family of
protocols:

* `proven` — uses the **Johnson-regime** proximity gap (`δ < 1 − √ρ`).
  Proved in BCIKS18 and follow-up papers. Solid pen-and-paper math
  modulo formalisation.
* `conjectured` — uses the **capacity-regime** proximity gap
  (`δ → 1 − ρ`). Believed but not proved, even at the paper level
  ("capacity-achieving proximity gap conjecture"). Yields tighter bounds
  and therefore higher bit-security; used by protocols when stronger
  numbers are desired and the risk of relying on a conjecture is
  acceptable. -/
inductive ProximityRegime where
  | proven
  | conjectured
  deriving DecidableEq, Repr

/-- A linear-code instance over the field `F`. -/
class LinearCode (Code : Type*) (F : Type*) [Field F] where
  /-- Configuration type (parameters: message length, code length, domain, …). -/
  Config : Type*
  /-- Construct a code value from a configuration. -/
  new : Config → Code
  /-- Encode a message of length `messageLen` into a codeword of length `codeLen`. -/
  encode : Code → Array F → Array F
  /-- Length `k` of messages. -/
  messageLen : Code → Nat
  /-- Length `n` of codewords. -/
  codeLen : Code → Nat
  /-- Minimum Hamming distance `d`: any two distinct codewords differ in at
  least `d` positions. For RS this is `n − k + 1` (Singleton, achieved). -/
  minimumDistance : Code → Nat
  /-- Johnson list-decoding radius: largest `t` such that for any received
  word `y ∈ 𝔽^n`, the number of codewords within Hamming distance `t` of
  `y` is polynomially bounded. For RS: roughly `n − √(n·k)`. -/
  johnsonRadius : Code → Nat
  /-- BCIKS18-style **Maximum Correlated Agreement** proximity-gap error
  bound. Given a batch of `l` received words, a distance bound `δ`, a
  field size `q`, and a security `regime`, returns the per-test
  soundness-error contribution: the probability that a random α-linear
  combination is δ-close to the code while no single codeword is δ-close
  to all `l` words simultaneously. Returned as a rational for exact
  chaining in security profilers. The `regime` selects between
  Johnson-bound (`proven`) and capacity-bound (`conjectured`) formulas;
  see `ProximityRegime`. -/
  mcaProximityGapError : Code → ProximityRegime → (l : Nat) → (δ : Nat)
    → (q : Nat) → ℚ

/-! ### Derived quantities

Common helpers that don't need per-code customisation. -/

variable {F : Type*} [Field F] {Code : Type*} [LinearCode Code F]

/-- Code rate `ρ = k / n`, as a rational. Returns `0` when `n = 0`. -/
def rate (c : Code) : ℚ :=
  if LinearCode.codeLen (F := F) c = 0 then (0 : ℚ)
  else ((LinearCode.messageLen (F := F) c : ℚ)) /
       ((LinearCode.codeLen (F := F) c : ℚ))

/-- Unique-decoding radius `⌊(d − 1) / 2⌋`, derived from `minimumDistance`. -/
def uniqueDecodingRadius (c : Code) : Nat :=
  (LinearCode.minimumDistance (F := F) c - 1) / 2

end LinearCodes
