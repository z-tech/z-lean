import LinearCodes.LinearCode
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-!
# Reed-Solomon code

Lean port of `ark-codes`'s `ReedSolomon` instance of the linear-code trait.
A message `m = (m_0, …, m_{k-1}) ∈ 𝔽^k` is interpreted as the coefficient
vector of a polynomial `p(X) = Σ_{i<k} m_i · X^i` of degree `< k`. The
codeword is the evaluation of `p` over a fixed `n`-point domain
`(d_0, …, d_{n-1}) ∈ 𝔽^n`. Required: `n > k`.

Unlike the Rust version (which uses arkworks' `GeneralEvaluationDomain`
and FFT), this implementation takes the domain as an explicit `Array F`
and evaluates point-by-point via Horner's method. The evaluation is
`O(n · k)` rather than `O(n log n)`, but it is fully computable and works
for any field — no `FftField` constraint, no need for an `n`-th root of
unity. An FFT-based encoder can be slotted in later as an optimisation.
-/

namespace LinearCodes

variable {F : Type*} [Field F]

/-- Reed-Solomon configuration: message length `k`, code length `n` (with
`n > k`), and the evaluation domain — an array of `n` distinct points in `F`.
The constructor `mkConfig` performs no validation; if the domain is not the
right length or contains duplicates, `encode` will still produce a (broken)
codeword. -/
structure ReedSolomonConfig (F : Type*) [Field F] where
  messageLength : Nat
  codeLength : Nat
  domain : Array F

/-- The Reed-Solomon code over `F`, parameterised by a `ReedSolomonConfig`. -/
structure ReedSolomonCode (F : Type*) [Field F] where
  config : ReedSolomonConfig F

/-- Evaluate a polynomial given by its coefficient array `coeffs`
(low-degree first: `coeffs[0]` is the constant term) at the point `x`,
using Horner's method. Right-fold so `[a₀, a₁, a₂]` evaluates as
`a₀ + x·(a₁ + x·a₂)`. -/
def evalPoly (coeffs : Array F) (x : F) : F :=
  coeffs.foldr (fun a acc => a + x * acc) 0

/-- Encode a message of length `k` into a codeword of length `n` by
evaluating the polynomial whose coefficients are the message at each
domain point. -/
def reedSolomonEncode (cfg : ReedSolomonConfig F) (message : Array F) : Array F :=
  cfg.domain.map (fun x => evalPoly message x)

/-- Integer square root: returns the largest `m : Nat` with `m² ≤ n`.
Linear scan; adequate for security-profiler-scale inputs. -/
private def isqrtAux : Nat → Nat → Nat
  | _, 0 => 0
  | n, k + 1 =>
    if (k + 1) * (k + 1) ≤ n then k + 1 else isqrtAux n k

/-- Largest `m : Nat` with `m² ≤ n`. -/
private def isqrt (n : Nat) : Nat := isqrtAux n n

/-- The MCA proximity-gap error formula for Reed-Solomon, factored out
of the typeclass instance so its `[0, 1]` range can be proved cleanly.

* `.proven` returns the integer-tight bound from
  `rs_MCA_list_decoding_bound`,
  `n² · (max(δ, 1) + 1) · (l - 1) / q`, clipped to `[0, 1]` via
  `min · 1`.
* `.conjectured` returns the capacity-regime placeholder
  `n · (l - 1) / q`, also clipped. Not yet machine-checked. -/
def rsMCAProximityGapError (rs : ReedSolomonCode F) (regime : ProximityRegime)
    (l δ q : Nat) : ℚ :=
  let lq : ℚ := if l = 0 then 0 else ((l - 1 : ℕ) : ℚ)
  let n_q : ℚ := (rs.config.codeLength : ℚ)
  let proven_raw : ℚ := n_q ^ 2 * (max (δ : ℚ) 1 + 1) * lq / (q : ℚ)
  let conjectured_raw : ℚ := n_q * lq / (q : ℚ)
  if q = 0 then (1 : ℚ)
  else
    match regime with
    | .proven => min proven_raw 1
    | .conjectured => min conjectured_raw 1

/-- Common non-negativity helper for the RS proximity-gap formula:
`lq := if l = 0 then 0 else (l - 1)` is always nonneg in `ℚ`. -/
private lemma rs_lq_nonneg (l : Nat) :
    0 ≤ (if l = 0 then (0 : ℚ) else ((l - 1 : ℕ) : ℚ)) := by
  split_ifs
  · exact le_refl (0 : ℚ)
  · exact_mod_cast Nat.zero_le _

/-- The `rsMCAProximityGapError` value is always in `[0, 1]`. -/
theorem rsMCAProximityGapError_in_unit_interval
    (rs : ReedSolomonCode F) (regime : ProximityRegime) (l δ q : Nat) :
    0 ≤ rsMCAProximityGapError rs regime l δ q ∧
    rsMCAProximityGapError rs regime l δ q ≤ 1 := by
  unfold rsMCAProximityGapError
  by_cases hq : q = 0
  · -- q = 0 branch: returns 1.
    simp only [hq, if_true]
    exact ⟨zero_le_one, le_refl 1⟩
  · -- q > 0 branch: each regime returns `min raw 1`, raw ≥ 0.
    simp only [if_neg hq]
    have hlq_nn := rs_lq_nonneg l
    have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    have h_n_q_nn : (0 : ℚ) ≤ (rs.config.codeLength : ℚ) := Nat.cast_nonneg _
    cases regime with
    | proven =>
      simp only
      have h_n_sq : (0 : ℚ) ≤ (rs.config.codeLength : ℚ) ^ 2 :=
        pow_nonneg h_n_q_nn 2
      have h_max : (0 : ℚ) ≤ max (δ : ℚ) 1 + 1 := by
        have : (1 : ℚ) ≤ max (δ : ℚ) 1 := le_max_right _ _
        linarith
      have h_raw : (0 : ℚ) ≤
          (rs.config.codeLength : ℚ) ^ 2 * (max (δ : ℚ) 1 + 1) *
            (if l = 0 then (0 : ℚ) else ((l - 1 : ℕ) : ℚ)) / (q : ℚ) :=
        div_nonneg (mul_nonneg (mul_nonneg h_n_sq h_max) hlq_nn) hq_pos.le
      exact ⟨le_min h_raw zero_le_one, min_le_right _ _⟩
    | conjectured =>
      simp only
      have h_raw : (0 : ℚ) ≤
          (rs.config.codeLength : ℚ) *
            (if l = 0 then (0 : ℚ) else ((l - 1 : ℕ) : ℚ)) / (q : ℚ) :=
        div_nonneg (mul_nonneg h_n_q_nn hlq_nn) hq_pos.le
      exact ⟨le_min h_raw zero_le_one, min_le_right _ _⟩

/-- Linear-code instance for `ReedSolomonCode`.

Security bounds:
* **Minimum distance**: `n − k + 1` (Singleton, RS is MDS).
* **Johnson radius**: `n − ⌈√(n·k)⌉`. Computed via `Nat.sqrt`, which gives
  `⌊√x⌋`; we adjust to `⌈·⌉` by the standard `n − Nat.sqrt(n*k) − 1` form
  (sound but slightly conservative when `n·k` is a perfect square).
* **MCA proximity-gap error**: two modes —
  * `proven` (Johnson regime): the integer-tight bound machine-checked
    by `rs_MCA_list_decoding_bound`,
    `n² · (max(δ, 1) + 1) · (l − 1) / q`. Here `δ` is the agreement-slack
    distance from the BCGM25 §6.2 setup (so `n·γ = δ` with `γ = δ/n` the
    real-valued slack). Holds *unconditionally* in Lean — see the proof
    in `LinearCodes/MCA/RS/`.
  * `conjectured` (capacity regime): a tighter placeholder shape
    `(l − 1) · n / q`, valid up to `δ → 1 − ρ`. Relies on the
    capacity-achieving proximity-gap conjecture. Yields higher
    bit-security but inherits the conjecture's risk; not currently
    backed by a Lean theorem. -/
instance : LinearCode (ReedSolomonCode F) F where
  Config := ReedSolomonConfig F
  new cfg := { config := cfg }
  encode rs message := reedSolomonEncode rs.config message
  messageLen rs := rs.config.messageLength
  codeLen rs := rs.config.codeLength
  minimumDistance rs :=
    rs.config.codeLength - rs.config.messageLength + 1
  johnsonRadius rs :=
    rs.config.codeLength
      - isqrt (rs.config.codeLength * rs.config.messageLength)
      - 1
  mcaProximityGapError := rsMCAProximityGapError
  mcaProximityGapError_in_unit_interval := rsMCAProximityGapError_in_unit_interval

end LinearCodes
