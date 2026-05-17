import LinearCodes.LinearCode

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
    in `LinearCodes/MCA/RSListDecoding.lean`.
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
  mcaProximityGapError rs regime l δ q :=
    if q = 0 then (1 : ℚ)
    else
      let lq : ℚ := if l = 0 then 0 else ((l - 1 : ℕ) : ℚ)
      let raw : ℚ := match regime with
        | .proven =>
          -- Matches `rs_MCA_list_decoding_bound` /
          -- `LinearCodes/MCA/RSListDecoding.lean#L651`:
          --   n² · (max(n·γ, 1) + 1) · (ℓ − 1) / |F|
          -- with γ := δ/n so that n·γ = δ.
          let n_q : ℚ := (rs.config.codeLength : ℚ)
          let δ_q : ℚ := (δ : ℚ)
          n_q ^ 2 * (max δ_q 1 + 1) * lq / (q : ℚ)
        | .conjectured =>
          -- Capacity-regime placeholder; not yet machine-checked.
          (rs.config.codeLength : ℚ) * lq / (q : ℚ)
      min raw 1

end LinearCodes
