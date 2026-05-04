import LinearCodes.ReedSolomon
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Reed-Solomon: formal properties (stubbed)

The key mathematical properties of the Reed-Solomon code, stated as theorems
with `sorry` proofs. These are the **API contract** that downstream
protocols (FRI low-degree testing, Brakedown commit-and-evaluate, …) can
rely on. Each `sorry` is to be closed when a downstream protocol that
actually exercises the property gets formalised.

## Properties stated here

* `encode_size` — encoding has length `codeLength` (given a well-formed domain).
* `encode_add` — additive linearity: `enc (m₁ + m₂) = enc m₁ + enc m₂`.
* `encode_smul` — scalar multiplicativity: `enc (c · m) = c · enc m`.
* `encode_min_distance` — Singleton-MDS distance bound:
  `Hamming(enc m₁, enc m₂) ≥ n − k + 1` for distinct messages.
* `encode_injective` — encoding is injective on length-`k` messages
  (corollary of `encode_min_distance`).
* `johnson_list_decoding_radius` — the list of codewords within the
  Johnson radius of any received word is finite (and polynomial — the
  quantitative bound is left as TODO).
* `mca_correlated_agreement` — BCIKS18 proximity-gap: if a random
  α-linear combination of received words is δ-close to the code for
  enough `α`, there exists a single codeword δ-close to all components.

## Conventions

* Linear operations on messages and codewords are represented pointwise via
  `Array.zipWith (·+·)` and `Array.map (c * ·)`. The size hypotheses are
  carried explicitly because `Array` has no length in its type.
* `hammingDist` returns `0` when sizes mismatch — proper distance is only
  meaningful on equal-length arrays.
-/

namespace LinearCodes

variable {F : Type} [Field F]

/-- Hamming distance: number of positions where two equal-size arrays
disagree. Returns `0` for mismatched sizes (callers should ensure equal
sizes before reading the value). -/
def hammingDist [DecidableEq F] (a b : Array F) : Nat :=
  if a.size = b.size then
    (List.range a.size).foldl
      (fun acc i => acc + if a.getD i 0 = b.getD i 0 then 0 else 1) 0
  else 0

/-! ### Encoding length -/

/-- The encoded codeword has length `codeLength`, given a domain of the
right size. Provable from `Array.size_map`; left as `sorry` here for
parity with the rest of the API contract. -/
theorem encode_size (cfg : ReedSolomonConfig F)
    (h_dom : cfg.domain.size = cfg.codeLength) (msg : Array F) :
    (reedSolomonEncode cfg msg).size = cfg.codeLength := by
  sorry

/-! ### Linearity -/

/-- **Additive linearity.** Encoding the pointwise sum of two messages
equals the pointwise sum of their encodings. -/
theorem encode_add (cfg : ReedSolomonConfig F)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength) :
    reedSolomonEncode cfg (Array.zipWith (· + ·) m1 m2) =
      Array.zipWith (· + ·)
        (reedSolomonEncode cfg m1) (reedSolomonEncode cfg m2) := by
  sorry

/-- **Scalar multiplicativity.** Encoding a scalar multiple of a message
equals the scalar multiple of its encoding. -/
theorem encode_smul (cfg : ReedSolomonConfig F) (c : F) (msg : Array F) :
    reedSolomonEncode cfg (msg.map (c * ·)) =
      (reedSolomonEncode cfg msg).map (c * ·) := by
  sorry

/-! ### Minimum distance -/

/-- **Reed-Solomon is MDS (Singleton bound is tight).** Any two distinct
length-`k` messages encode to codewords differing in at least
`codeLength − messageLength + 1` positions, provided the evaluation
domain consists of distinct points. -/
theorem encode_min_distance [DecidableEq F] (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength)
    (h_neq : m1 ≠ m2)
    (h_le : cfg.messageLength ≤ cfg.codeLength) :
    hammingDist (reedSolomonEncode cfg m1) (reedSolomonEncode cfg m2)
      ≥ cfg.codeLength - cfg.messageLength + 1 := by
  sorry

/-! ### Injectivity (corollary of `encode_min_distance`) -/

/-- Encoding is injective on length-`k` messages. -/
theorem encode_injective [DecidableEq F] (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_lt : cfg.messageLength < cfg.codeLength)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength)
    (h_eq : reedSolomonEncode cfg m1 = reedSolomonEncode cfg m2) :
    m1 = m2 := by
  sorry

/-! ### List-decoding radius (Johnson bound) -/

/-- **Johnson list-decoding radius for Reed-Solomon.** For any received
word `y ∈ 𝔽^n` and radius `t` strictly below the Johnson bound — i.e.
`(n − t)² > n · k` (equivalently `t < n − √(n·k)`) — the set of length-`k`
messages whose encoding is within Hamming distance `t` of `y` is finite.
RS achieves the Johnson bound algorithmically (Guruswami-Sudan); the
explicit polynomial bound on list size is left as TODO. -/
theorem johnson_list_decoding_radius [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (y : Array F) (h_y_size : y.size = cfg.codeLength)
    (t : ℕ)
    (h_johnson :
      (cfg.codeLength - t) * (cfg.codeLength - t) >
        cfg.codeLength * cfg.messageLength) :
    Set.Finite {m : Array F | m.size = cfg.messageLength ∧
                   hammingDist y (reedSolomonEncode cfg m) ≤ t} := by
  sorry

/-! ### Maximum Correlated Agreement (proximity gap) -/

/-- α-linear combination of `l` words at a fixed length `n`:
`(linComb n fs α)[j] = Σ_i α^i · (fs i).getD j 0`. Out-of-bounds reads
default to `0`, so callers must ensure each `fs i` has size `n`. -/
def linComb (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (α : F) : Array F :=
  Array.ofFn (n := n) fun j : Fin n =>
    (List.finRange l).foldl
      (fun acc i => acc + α ^ i.val * (fs i).getD j.val 0) 0

open Classical in
/-- **Maximum Correlated Agreement (BCIKS18 proximity gap).** Given `l`
received words `f₀, …, f_{l-1} ∈ 𝔽^n`: if for at least `threshold`-many
`α ∈ 𝔽`, the α-linear combination `Σ_i α^i · fᵢ` is within Hamming
distance `δ` of some RS codeword, then there exists a single message
`m` whose encoding is within Hamming distance `δ` of *all* `fᵢ`.

Used as a batched-proximity-test soundness amplifier in FRI, STIR, and
Brakedown. The exact `(δ, threshold)` regime is paper-dependent —
e.g. δ < (1−ρ)/2 for unique decoding, δ < 1−√ρ for Johnson. Both
parameters are left as theorem inputs to specialise per protocol. -/
theorem mca_correlated_agreement [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (h_sizes : ∀ i : Fin l, (fs i).size = cfg.codeLength)
    (δ : ℕ) (threshold : ℕ)
    (h_close_combo :
      (Finset.univ.filter fun α : F =>
        ∃ m : Array F, m.size = cfg.messageLength ∧
          hammingDist (linComb cfg.codeLength fs α)
                      (reedSolomonEncode cfg m) ≤ δ).card ≥ threshold) :
    ∃ m : Array F, m.size = cfg.messageLength ∧
      ∀ i : Fin l, hammingDist (fs i) (reedSolomonEncode cfg m) ≤ δ := by
  sorry

end LinearCodes
