import SumcheckProtocol.Properties.MultilinearProver
import SumcheckProtocol.Src.EvalForm
import SumcheckProtocol.Src.SubstRound0
import SumcheckProtocol.Properties.Lemmas.Hypercube

/-!
# Phase 2 bridge: eval-table prover ↔ symbolic eval-form spec

This file connects the **table-form** correctness theorem
`compute_correctness_table` (a `Finset.sum` over `Fin (2^n)` of
`p.eval ∘ boolPoint_msb`) to the **symbolic** spec
`honestProverMessageEvalsAt` (a `sumOverDomainRecursive [0,1] (·+·) 0`).

The bridge has three load-bearing steps, each in its own section:

1. `sumOverDomainRecursive_bool_eq_finSum` — `sumOverDomainRecursive [0,1] _ _ F`
   equals `∑ k : Fin (2^n), F (boolFromFin_lsb k)`, by induction on `n`. Here
   `boolFromFin_lsb k j = (if k.val.testBit j.val then 1 else 0)` is the LSB
   bit decomposition: variable `j` = bit `j` of `k`.

2. `finSum_lsb_eq_msb` — `∑ k : Fin (2^n), F (boolFromFin_lsb k) =
   ∑ k : Fin (2^n), F (boolFromFin_msb k)`, by `Finset.sum_bij` along the
   bit-reversal involution `bitReverse n : Fin (2^n) → Fin (2^n)`.

3. `compute_correctness_at_zero` / `compute_correctness_at_one` — combine 1, 2,
   the equality `boolFromFin_msb = boolPoint_msb`, and the existing
   `compute_correctness_table` to land at `honestProverMessageEvalsAt … 0`/`1`.
-/

namespace SumcheckProtocol.MultilinearProver

open CompPoly SumcheckProtocol

variable {𝔽 : Type _}

/-! ### Boolean point from a `Fin (2^n)` index -/

/-- LSB-style Boolean point: variable `j` is bit `j` of `k`. The natural
    convention for sums over `Fin (2^n) → 𝔽` indexed by bit decomposition. -/
def boolFromFin_lsb [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) : Fin n → 𝔽 :=
  fun j => if k.val.testBit j.val then (1 : 𝔽) else (0 : 𝔽)

/-- MSB-style Boolean point: variable `j` is bit `n-1-j` of `k`.
    This matches `boolPoint_msb` (variable 0 = high bit, variable n-1 = low
    bit) modulo a `BitVec.getLsb ↔ Nat.testBit` rewrite. -/
def boolFromFin_msb [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) : Fin n → 𝔽 :=
  fun j => if k.val.testBit (n - 1 - j.val) then (1 : 𝔽) else (0 : 𝔽)

/-- The MSB Boolean point we just defined matches the existing `boolPoint_msb`
    from `SumcheckProtocol/Src/MultilinearProver.lean`. The contents of the
    `if`s line up via two named bridge facts: `BitVec.toNat_ofFin` collapses
    `(BitVec.ofFin k).toNat` to `k.val`, and `reverseFin_val` collapses
    `(reverseFin j).val` to `n - 1 - j.val`. -/
lemma boolFromFin_msb_eq_boolPoint_msb [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) :
    boolFromFin_msb (𝔽 := 𝔽) k = boolPoint_msb (𝔽 := 𝔽) k := by
  funext j
  show (if k.val.testBit (n - 1 - j.val) then (1 : 𝔽) else 0)
      = if (BitVec.ofFin k).getLsb (reverseFin j) then (1 : 𝔽) else 0
  have h : (BitVec.ofFin k).getLsb (reverseFin j)
      = k.val.testBit (n - 1 - j.val) := by
    show (BitVec.ofFin k).toNat.testBit (reverseFin j).val
        = k.val.testBit (n - 1 - j.val)
    rw [BitVec.toNat_ofFin, reverseFin_val]
  rw [h]

/-! ### Task 1: `sumOverDomainRecursive [0,1]` as a finite sum over `Fin (2^n)`

We prove the equality by induction on `n`, splitting `Fin (2^(n+1))` into
its even and odd halves under the equivalence `k ↔ (k.val.testBit 0, k/2)`.
The recursion in `sumOverDomainRecursive` peels off variable 0 first via
`Fin.cons` (= `Fin.cases`), so the LSB convention (`boolFromFin_lsb`) is the
one that lines up: variable 0 = bit 0. -/

/-- `k.val / 2 < 2^n` when `k : Fin (2^(n+1))`. -/
private lemma half_lt_two_pow {n : ℕ} (k : Fin (2^(n+1))) :
    k.val / 2 < 2^n := by
  have h1 : k.val < 2^(n+1) := k.isLt
  have h2 : (2:ℕ) ^ n * 2 = 2^(n+1) := by rw [pow_succ]
  have : k.val < 2^n * 2 := by omega
  exact Nat.div_lt_iff_lt_mul (by norm_num : (0:ℕ) < 2) |>.mpr this

/-- Splitting `boolFromFin_lsb` at the head: the head is the LSB bit, and
    the tail is `boolFromFin_lsb` of `k / 2`. -/
private lemma boolFromFin_lsb_succ [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^(n+1))) :
    boolFromFin_lsb (𝔽 := 𝔽) (n := n+1) k =
      (Fin.cons
        (α := fun _ : Fin (n+1) => 𝔽)
        (if k.val.testBit 0 then (1 : 𝔽) else 0)
        (boolFromFin_lsb (𝔽 := 𝔽) (n := n)
          ⟨k.val / 2, half_lt_two_pow k⟩)) := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · -- j = 0 case
    show (if k.val.testBit (0 : Fin (n+1)).val then (1 : 𝔽) else 0)
        = (Fin.cons
              (α := fun _ : Fin (n+1) => 𝔽)
              (if k.val.testBit 0 then (1 : 𝔽) else 0)
              (boolFromFin_lsb (𝔽 := 𝔽) ⟨k.val / 2, half_lt_two_pow k⟩)) 0
    simp
  · -- j = j'.succ case; bit (j'.val + 1) of k = bit j'.val of (k / 2)
    show (if k.val.testBit j'.succ.val then (1 : 𝔽) else 0)
        = (Fin.cons
              (α := fun _ : Fin (n+1) => 𝔽)
              (if k.val.testBit 0 then (1 : 𝔽) else 0)
              (boolFromFin_lsb (𝔽 := 𝔽) ⟨k.val / 2, half_lt_two_pow k⟩)) j'.succ
    rw [Fin.cons_succ]
    show (if k.val.testBit (j'.val + 1) then (1 : 𝔽) else 0)
        = if (k.val / 2).testBit j'.val then (1 : 𝔽) else 0
    -- Nat.testBit_succ states k.testBit (n+1) = (k/2).testBit n
    rw [show k.val.testBit (j'.val + 1) = (k.val / 2).testBit j'.val
        from Nat.testBit_succ k.val j'.val]

/-- Pair a `Fin 2 × Fin (2^n)` with the corresponding `Fin (2^(n+1))` index
    via `(b, k') ↦ b.val + 2 * k'.val`. The LSB of the result is `b`, the
    higher bits are `k'`. -/
private def packLsb {n : ℕ} (b : Fin 2) (k' : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨b.val + 2 * k'.val, by
    have hb : b.val < 2 := b.isLt
    have hk : k'.val < 2^n := k'.isLt
    have h2 : 2^(n+1) = 2 + 2 * (2^n - 1) + 0 := by
      rw [pow_succ]
      have : 1 ≤ 2^n := Nat.one_le_two_pow
      omega
    -- simpler: 2 * k'.val + 2 ≤ 2 * 2^n = 2^(n+1)
    have hk2 : 2 * k'.val + 2 ≤ 2 * 2^n := by omega
    have hpow : (2:ℕ) * 2^n = 2^(n+1) := by rw [pow_succ]; ring
    omega⟩

/-- The pairing `packLsb` is a bijection `Fin 2 × Fin (2^n) ≃ Fin (2^(n+1))`. -/
private def lsbEquiv (n : ℕ) : Fin 2 × Fin (2^n) ≃ Fin (2^(n+1)) where
  toFun p := packLsb p.1 p.2
  invFun k :=
    (⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩,
     ⟨k.val / 2, half_lt_two_pow k⟩)
  left_inv := by
    rintro ⟨b, k'⟩
    have hb : b.val < 2 := b.isLt
    ext
    · show (b.val + 2 * k'.val) % 2 = b.val
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hb
    · show (b.val + 2 * k'.val) / 2 = k'.val
      rw [Nat.add_mul_div_left _ _ (by norm_num : (0:ℕ) < 2)]
      have : b.val / 2 = 0 := Nat.div_eq_of_lt hb
      omega
  right_inv := by
    intro k
    apply Fin.ext
    show k.val % 2 + 2 * (k.val / 2) = k.val
    have := Nat.div_add_mod k.val 2
    omega

/-- Splitting `Fin (2^(n+1))` summation by the LSB. -/
private lemma sum_fin_two_pow_succ_lsb {β : Type _} [AddCommMonoid β]
    {n : ℕ} (G : Fin (2^(n+1)) → β) :
    (∑ k : Fin (2^(n+1)), G k) =
      (∑ k' : Fin (2^n), G (packLsb 0 k'))
      + (∑ k' : Fin (2^n), G (packLsb 1 k')) := by
  rw [← (lsbEquiv n).sum_comp G]
  show (∑ p : Fin 2 × Fin (2^n), G (packLsb p.1 p.2)) = _
  rw [Fintype.sum_prod_type]
  -- ∑ b : Fin 2, ∑ k', G (packLsb b k') = (case b = 0) + (case b = 1)
  rw [Fin.sum_univ_two]

/-- The packed `Fin (2^(n+1))` index has LSB equal to `b`. -/
private lemma packLsb_testBit_zero {n : ℕ} (b : Fin 2) (k' : Fin (2^n)) :
    (packLsb b k').val.testBit 0 = decide (b.val = 1) := by
  show (b.val + 2 * k'.val).testBit 0 = decide (b.val = 1)
  -- bit 0 of (b + 2*k') equals bit 0 of b (since b < 2 it's just b == 1)
  have hb : b.val < 2 := b.isLt
  have hmod : (b.val + 2 * k'.val) % 2 = b.val := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hb
  fin_cases b <;> simp [Nat.testBit_zero, hmod]

/-- The packed `Fin (2^(n+1))` index has higher bits equal to `k'`. -/
private lemma packLsb_div_two {n : ℕ} (b : Fin 2) (k' : Fin (2^n)) :
    (packLsb b k').val / 2 = k'.val := by
  show (b.val + 2 * k'.val) / 2 = k'.val
  rw [Nat.add_mul_div_left _ _ (by norm_num : (0:ℕ) < 2)]
  have hb : b.val < 2 := b.isLt
  have : b.val / 2 = 0 := Nat.div_eq_of_lt hb
  omega

/-- For `b = 0`, `boolFromFin_lsb (packLsb 0 k')` is `Fin.cons 0 (boolFromFin_lsb k')`. -/
private lemma boolFromFin_lsb_pack_zero [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k' : Fin (2^n)) :
    boolFromFin_lsb (𝔽 := 𝔽) (n := n+1) (packLsb 0 k')
      = (Fin.cons (α := fun _ : Fin (n+1) => 𝔽)
            (0 : 𝔽) (boolFromFin_lsb (𝔽 := 𝔽) k')) := by
  rw [boolFromFin_lsb_succ]
  -- Now need both (if testBit 0 then 1 else 0) = 0 and
  -- the inner boolFromFin_lsb equality.
  congr 1
  · -- bit 0 of (packLsb 0 k') is false → 0
    rw [packLsb_testBit_zero]
    simp
  · -- (packLsb 0 k').val / 2 = k'.val
    apply congrArg
    apply Fin.ext
    exact packLsb_div_two 0 k'

/-- For `b = 1`, `boolFromFin_lsb (packLsb 1 k')` is `Fin.cons 1 (boolFromFin_lsb k')`. -/
private lemma boolFromFin_lsb_pack_one [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k' : Fin (2^n)) :
    boolFromFin_lsb (𝔽 := 𝔽) (n := n+1) (packLsb 1 k')
      = (Fin.cons (α := fun _ : Fin (n+1) => 𝔽)
            (1 : 𝔽) (boolFromFin_lsb (𝔽 := 𝔽) k')) := by
  rw [boolFromFin_lsb_succ]
  congr 1
  · rw [packLsb_testBit_zero]
    simp
  · apply congrArg
    apply Fin.ext
    exact packLsb_div_two 1 k'

/-- **Task 1 — Bridge: `sumOverDomainRecursive [0,1]` as a `Finset.sum` over
    `Fin (2^n)` indexed by LSB bit decomposition.**

    The LHS walks the boolean hypercube `{0,1}^n` recursively, peeling off
    variable 0 first; the RHS enumerates the same `2^n` points by their LSB
    integer encoding. -/
theorem sumOverDomainRecursive_bool_eq_finSum
    [CommSemiring 𝔽]
    {n : ℕ} (F : (Fin n → 𝔽) → 𝔽) :
    sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
        [(0 : 𝔽), 1] (· + ·) 0 (m := n) F
      = ∑ k : Fin (2^n), F (boolFromFin_lsb (𝔽 := 𝔽) k) := by
  induction n with
  | zero =>
      rw [sum_over_domain_recursive_zero]
      -- RHS is sum over Fin 1 of F applied to boolFromFin_lsb of the single index;
      -- that single index is 0 (Fin (2^0) = Fin 1) and the bool point is Fin.elim0.
      have : (Finset.univ : Finset (Fin (2^0))) = {⟨0, by simp⟩} := by
        rfl
      rw [this, Finset.sum_singleton]
      congr 1
      funext j; exact j.elim0
  | succ n ih =>
      rw [sum_over_domain_recursive_succ]
      -- LHS: foldl over [0,1] starting from 0
      -- = 0 + sumOver(F ∘ cons 0) + sumOver(F ∘ cons 1)
      simp only [List.foldl_cons, List.foldl_nil, zero_add]
      -- Apply IH to each summand
      rw [ih (fun x => F (Fin.cons 0 x))]
      rw [ih (fun x => F (Fin.cons 1 x))]
      -- Now combine via the LSB split of the RHS
      rw [sum_fin_two_pow_succ_lsb (G := fun k => F (boolFromFin_lsb k))]
      -- Each side now matches via `boolFromFin_lsb_pack_{zero,one}`
      congr 1
      · apply Finset.sum_congr rfl
        intro k' _
        rw [boolFromFin_lsb_pack_zero]
      · apply Finset.sum_congr rfl
        intro k' _
        rw [boolFromFin_lsb_pack_one]

/-! ### Task 2: Bit-reversal bijection on `Fin (2^n)`

We define the bit-reversal map recursively on `n`. The natural induction
structure matches `lsbEquiv`: split off the LSB via `(b, k') ↦ b + 2*k'`,
recurse on `k' : Fin (2^n)`, then reattach `b` as the **highest** bit.

Concretely, on `Fin (2^(n+1))`:

  `bitReverseFin (packLsb b k') = packMsb b (bitReverseFin k')`

where `packMsb b k' = b * 2^n + k'.val` is the "high-bit" encoding into
`Fin (2^(n+1))`. That makes the involutivity `bitReverseFin ∘ bitReverseFin = id`
direct: peeling LSB on the inside corresponds to peeling MSB on the outside,
and on the recursion the IH applies.

Crucially, the relationship to `boolFromFin_lsb / boolFromFin_msb` is:

  `boolFromFin_lsb (bitReverseFin k) = boolFromFin_msb k`

This makes Task 2 a one-line `Equiv.sum_comp`.
-/

/-- The "high-bit" pairing dual to `packLsb`: `(b, k') ↦ b * 2^n + k'.val`.
    The MSB (bit `n`) of the result is `b`, and the lower `n` bits are `k'`. -/
private def packMsb {n : ℕ} (b : Fin 2) (k' : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨b.val * 2^n + k'.val, by
    have hb : b.val < 2 := b.isLt
    have hk : k'.val < 2^n := k'.isLt
    have hpow : (2:ℕ) * 2^n = 2^(n+1) := by rw [pow_succ]; ring
    have : b.val * 2^n + k'.val < 2 * 2^n := by
      cases hb_eq : b.val with
      | zero => simp; exact lt_of_lt_of_le hk (by omega)
      | succ b' =>
          have : b' = 0 := by omega
          subst this
          show 1 * 2^n + k'.val < 2 * 2^n
          omega
    omega⟩

/-- `packMsb` is the same family but on the dual side: it encodes
    `(b, k') ↦ b * 2^n + k'.val` into `Fin (2^(n+1))`. The inverse is
    `k ↦ (k.val / 2^n, k.val % 2^n)`. -/
private def msbEquiv (n : ℕ) : Fin 2 × Fin (2^n) ≃ Fin (2^(n+1)) where
  toFun p := packMsb p.1 p.2
  invFun k :=
    (⟨k.val / 2^n, by
       have hk : k.val < 2^(n+1) := k.isLt
       have hpow : (2:ℕ)^n * 2 = 2^(n+1) := by rw [pow_succ]
       have hk2 : k.val < 2 * 2^n := by
         rw [show (2:ℕ) * 2^n = 2^n * 2 from by ring]
         omega
       exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n) |>.mpr hk2⟩,
     ⟨k.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩)
  left_inv := by
    rintro ⟨b, k'⟩
    have hb : b.val < 2 := b.isLt
    have hk : k'.val < 2^n := k'.isLt
    have hpos : 0 < 2^n := Nat.two_pow_pos n
    ext
    · show (b.val * 2^n + k'.val) / 2^n = b.val
      rw [show b.val * 2^n + k'.val = 2^n * b.val + k'.val from by ring,
          Nat.mul_add_div hpos]
      have : k'.val / 2^n = 0 := Nat.div_eq_of_lt hk
      omega
    · show (b.val * 2^n + k'.val) % 2^n = k'.val
      rw [show b.val * 2^n + k'.val = 2^n * b.val + k'.val from by ring,
          Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hk
  right_inv := by
    intro k
    apply Fin.ext
    show (k.val / 2^n) * 2^n + k.val % 2^n = k.val
    have h := Nat.div_add_mod k.val (2^n)
    -- h : 2 ^ n * (↑k / 2 ^ n) + ↑k % 2 ^ n = ↑k
    linarith [h, Nat.mul_comm (2^n) (k.val / 2^n)]

/-- The bit-reversal equivalence on `Fin (2^n)`, defined by recursion on `n`.

    On `Fin (2^(n+1))`: split the LSB off via `lsbEquiv⁻¹`, recurse the rest
    via the inductively defined bit-reversal, and reassemble with the LSB
    becoming the new high bit via `msbEquiv`. -/
def bitReverseEquiv : (n : ℕ) → Fin (2^n) ≃ Fin (2^n)
  | 0     => Equiv.refl _
  | n + 1 =>
      ((lsbEquiv n).symm.trans
        ((Equiv.refl (Fin 2)).prodCongr (bitReverseEquiv n))).trans (msbEquiv n)

/-- Computational unfolding of `bitReverseEquiv` at `n+1` on a `packLsb`
    decomposition. -/
private lemma bitReverseEquiv_packLsb {n : ℕ} (b : Fin 2) (k' : Fin (2^n)) :
    bitReverseEquiv (n+1) (packLsb b k') = packMsb b (bitReverseEquiv n k') := by
  show msbEquiv n
        (((Equiv.refl (Fin 2)).prodCongr (bitReverseEquiv n))
          ((lsbEquiv n).symm (packLsb b k'))) = _
  have h1 : (lsbEquiv n).symm (packLsb b k') = (b, k') :=
    (lsbEquiv n).symm_apply_apply (b, k')
  rw [h1]
  rfl

/-! ### bridging boolFromFin_msb to boolFromFin_lsb via bitReverseEquiv -/

/-- The numeric content of bit-reversal: bit `j` of the reversed index
    equals bit `n-1-j` of the original index, for `j < n`. We prove this by
    induction on `n` using the recursive structure of `bitReverseEquiv`. -/
private lemma bitReverseEquiv_testBit :
    ∀ (n : ℕ) (k : Fin (2^n)) (j : ℕ), j < n →
      (bitReverseEquiv n k).val.testBit j = k.val.testBit (n - 1 - j) := by
  intro n
  induction n with
  | zero => intro k j hj; exact absurd hj (by omega)
  | succ m ih =>
      intro k j hj
      -- Decompose k = packLsb b k' via lsbEquiv⁻¹.
      set bk' := (lsbEquiv m).symm k with hbk'_def
      set b : Fin 2 := bk'.1 with hb_def
      set k' : Fin (2^m) := bk'.2 with hk'_def
      have hk_eq : k = packLsb b k' := by
        have h1 : (lsbEquiv m) bk' = k := (lsbEquiv m).apply_symm_apply k
        show k = packLsb b k'
        rw [← h1]
        rfl
      rw [hk_eq, bitReverseEquiv_packLsb]
      show (b.val * 2^m + (bitReverseEquiv m k').val).testBit j
          = (b.val + 2 * k'.val).testBit (m + 1 - 1 - j)
      have hsub : m + 1 - 1 - j = m - j := by omega
      rw [hsub]
      have hb_lt : b.val < 2 := b.isLt
      have hkr_lt : (bitReverseEquiv m k').val < 2^m := (bitReverseEquiv m k').isLt
      -- Commute LHS to use Nat.testBit_two_pow_mul_add (which is 2^i * a + b'):
      have hcomm : b.val * 2^m + (bitReverseEquiv m k').val
          = 2^m * b.val + (bitReverseEquiv m k').val := by ring
      rw [hcomm, Nat.testBit_two_pow_mul_add (a := b.val) hkr_lt j]
      by_cases hjm : j < m
      · -- j < m: LHS = (br k').val.testBit j, RHS = bit (m - j) of (b + 2*k'.val) = bit (m-j-1) of k'.
        simp only [hjm, if_true]
        have hmj_pos : 0 < m - j := by omega
        have hmj_eq : m - j = (m - j - 1) + 1 := by omega
        rw [hmj_eq]
        show (bitReverseEquiv m k').val.testBit j
            = (b.val + 2 * k'.val).testBit ((m - j - 1) + 1)
        rw [Nat.testBit_succ]
        have hdiv : (b.val + 2 * k'.val) / 2 = k'.val := by
          rw [Nat.add_mul_div_left _ _ (by norm_num : (0:ℕ) < 2)]
          have hbd : b.val / 2 = 0 := Nat.div_eq_of_lt hb_lt
          omega
        rw [hdiv]
        -- Apply ih
        rw [ih k' j hjm]
        congr 1
        omega
      · -- j ≥ m, but j < m+1, so j = m. Don't substitute (subst variants
        -- can confuse the term `m`); just rewrite via the equality.
        have hj_eq : j = m := by omega
        -- LHS branch: j < m is false, so the if takes the else branch.
        -- The goal becomes b.val.testBit (j - m) = (b.val + 2 * k'.val).testBit (m - j).
        -- With j = m, j - m = 0 and m - j = 0.
        have hjlt : ¬ j < m := by omega
        simp only [hjlt, if_false]
        have hsub1 : j - m = 0 := by omega
        have hsub2 : m - j = 0 := by omega
        rw [hsub1, hsub2]
        rw [Nat.testBit_zero, Nat.testBit_zero]
        have hmod : (b.val + 2 * k'.val) % 2 = b.val := by
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hb_lt
        rw [hmod]
        have : b.val % 2 = b.val := Nat.mod_eq_of_lt hb_lt
        rw [this]

/-- The bit-reversal equivalence converts MSB-style Boolean points to
    LSB-style Boolean points. -/
lemma boolFromFin_lsb_bitReverseEquiv [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) :
    boolFromFin_lsb (𝔽 := 𝔽) (bitReverseEquiv n k)
      = boolFromFin_msb (𝔽 := 𝔽) k := by
  funext j
  show (if (bitReverseEquiv n k).val.testBit j.val then (1 : 𝔽) else 0)
      = if k.val.testBit (n - 1 - j.val) then (1 : 𝔽) else 0
  rw [bitReverseEquiv_testBit n k j.val j.isLt]

/-- **Task 2 — Bit-reversal bijection.** The `Finset.sum` over `Fin (2^n)` of
    `F (boolFromFin_lsb k)` equals the sum of `F (boolFromFin_msb k)`, by
    reindexing along the bit-reversal equivalence. -/
theorem finSum_lsb_eq_msb [Zero 𝔽] [One 𝔽] {β : Type _} [AddCommMonoid β]
    {n : ℕ} (F : (Fin n → 𝔽) → β) :
    (∑ k : Fin (2^n), F (boolFromFin_lsb (𝔽 := 𝔽) k))
      = ∑ k : Fin (2^n), F (boolFromFin_msb (𝔽 := 𝔽) k) := by
  rw [← (bitReverseEquiv n).sum_comp (g := fun k => F (boolFromFin_lsb k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [boolFromFin_lsb_bitReverseEquiv]

/-! ### Task 3: bridge to `honestProverMessageEvalsAt`

We connect `compute_correctness_table` (which expresses the table-prover's
`(s0, s1)` as sums over `Fin (2^n)` of `boolPoint_msb`-indexed evaluations)
to `honestProverMessageEvalsAt [0,1] p ⟨0, _⟩ Fin.elim0 c` (which is a
`sumOverDomainRecursive [0,1] (·+·) 0` over the Boolean hypercube of `n`
open variables).

For the round-0 message, the open variables are exactly the `n` non-leading
positions of `Fin (n+1)`, and the leading position is fixed to `c`. The
chain is:

  honestProverMessageEvalsAt … c
    = sumOverDomainRecursive [0,1] _ _ (m := n) (fun x => eval (cons c x) p)   [defn]
    = ∑ k : Fin (2^n), eval (cons c (boolFromFin_lsb k)) p                       [Task 1]
    = ∑ k : Fin (2^n), eval (cons c (boolFromFin_msb k)) p                       [Task 2]
    = ∑ k : Fin (2^n), eval (boolPoint_msb (k as Fin (2^(n+1)) with high bit c-encoded)) p

The last step uses `boolFromFin_msb_eq_boolPoint_msb` and a bookkeeping
lemma about `Fin.cons` agreeing with `boolPoint_msb` on a half-cube. -/

variable [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽]

omit [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
/-- The point built inside `residualSumWithOpenVars` at round 0 with no prior
    challenges and current value `c` equals `Fin.cons c x` (where `x` is the
    open-variable assignment). -/
private lemma residual_point_round_zero
    {n : ℕ} (c : 𝔽) (x : Fin n → 𝔽) (i : Fin (n+1)) :
    addCasesFun (Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) x
        (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i)
      = Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x i := by
  unfold addCasesFun
  refine Fin.cases ?_ (fun i' => ?_) i
  · -- index 0
    have h0 : (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm 0)
        = Fin.castAdd (numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)
            (⟨0, Nat.succ_pos 0⟩ : Fin 1) := by
      apply Fin.ext; rfl
    change Fin.addCases (Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) x
        (Fin.castAdd (numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)
          (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      = Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x 0
    rw [Fin.addCases_left (motive := fun _ => 𝔽) (m := 1)
        (n := numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)
        (left := Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) (right := x)
        (⟨0, Nat.succ_pos 0⟩ : Fin 1)]
    have hlast : (⟨0, Nat.succ_pos 0⟩ : Fin 1) = Fin.last 0 := by
      apply Fin.ext; rfl
    rw [hlast, Fin.snoc_last, Fin.cons_zero]
  · -- index i'.succ
    have h0 : (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i'.succ)
        = Fin.natAdd 1
            (⟨i'.val, by
              have := i'.isLt
              show i'.val < numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩
              show i'.val < (n+1) - (0 + 1)
              omega⟩ : Fin (numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)) := by
      apply Fin.ext
      show i'.val + 1 = 1 + i'.val
      omega
    let idx : Fin (numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩) :=
      ⟨i'.val, by
        have := i'.isLt
        show i'.val < numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩
        show i'.val < (n+1) - (0 + 1)
        omega⟩
    calc
      Fin.addCases (Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) x
          (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i'.succ)
          = Fin.addCases (Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) x (Fin.natAdd 1 idx) := by
            exact congrArg (Fin.addCases (Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) x) h0
      _ = x idx := by
        rw [Fin.addCases_right (motive := fun _ => 𝔽) (m := 1)
          (n := numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)
          (left := Fin.snoc (Fin.elim0 : Fin 0 → 𝔽) c) (right := x) idx]
      _ = Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x i'.succ := by
        rw [Fin.cons_succ]
        -- Now x idx = x i' since the index has the same value.
        congr 1

omit [BEq 𝔽] [LawfulBEq 𝔽] in
/-- Unfolding of `honestProverMessageEvalsAt` at round 0 with no prior
    challenges. The result is a `sumOverDomainRecursive` of `eval (Fin.cons c x) p`. -/
private lemma honestProverMessageEvalsAt_zero_unfold
    {n : ℕ}
    (domain : List 𝔽)
    (p : CPoly.CMvPolynomial (n+1) 𝔽)
    (c : 𝔽) :
    honestProverMessageEvalsAt domain p ⟨0, Nat.succ_pos n⟩ Fin.elim0 c
      = sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽)
          domain (· + ·) 0 (m := n)
          (fun x => CPoly.CMvPolynomial.eval
            (Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x) p) := by
  unfold honestProverMessageEvalsAt residualSumWithOpenVars
  show sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽) domain (· + ·) 0
      (m := numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩)
      (fun x =>
        let point : Fin (n+1) → 𝔽 := fun i =>
          addCasesFun (Fin.snoc Fin.elim0 c) x
            (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i)
        CPoly.CMvPolynomial.eval point p)
    = sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽) domain (· + ·) 0 (m := n)
        (fun x => CPoly.CMvPolynomial.eval
          (Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x) p)
  -- numOpenVars i for i.val = 0 is n+1 - 1 = n; the cast is reflexive
  have hopen : numOpenVars (n := n+1) ⟨0, Nat.succ_pos n⟩ = n := by
    show n + 1 - (0 + 1) = n
    omega
  rw [sum_over_domain_recursive_cast (hm := hopen)]
  apply sum_over_domain_recursive_congr
  intro x
  -- After cast, the inner sum's argument becomes x ∘ Fin.cast hopen.
  -- The point function in the let-binding agrees pointwise with Fin.cons c x.
  show CPoly.CMvPolynomial.eval (fun i : Fin (n+1) =>
            addCasesFun (Fin.snoc Fin.elim0 c) (x ∘ Fin.cast hopen)
              (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i)) p
      = CPoly.CMvPolynomial.eval
          (Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x) p
  congr 1
  funext i
  calc
    addCasesFun (Fin.snoc Fin.elim0 c) (x ∘ Fin.cast hopen)
        (Fin.cast (snoc_split_eq (n := n+1) ⟨0, Nat.succ_pos n⟩).symm i)
        = Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c (x ∘ Fin.cast hopen) i := by
          exact residual_point_round_zero c (x ∘ Fin.cast hopen) i
    _ = Fin.cons (α := fun _ : Fin (n+1) => 𝔽) c x i := by
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero]
      · rw [Fin.cons_succ, Fin.cons_succ]
        show x ((Fin.cast hopen) i') = x i'
        have : (Fin.cast hopen) i' = i' := by apply Fin.ext; rfl
        rw [this]

omit [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
/-- Helper: `Fin.cons c (boolFromFin_msb k)` for `k : Fin (2^n)` equals
    `boolPoint_msb` of the `Fin (2^(n+1))` index obtained by encoding `c` as the
    high bit. We give two specialised versions: `c = 0` (low half) and `c = 1`
    (high half). -/
private lemma Fin_cons_zero_boolFromFin_msb_eq [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) :
    (Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (0 : 𝔽)
      (boolFromFin_msb (𝔽 := 𝔽) k))
      = boolPoint_msb (𝔽 := 𝔽) (n := n+1)
          (⟨k.val, by
            have hk : k.val < 2^n := k.isLt
            have : (2:ℕ)^n ≤ 2^(n+1) := by rw [pow_succ]; omega
            omega⟩ : Fin (2^(n+1))) := by
  have hkbnd : k.val < 2^(n+1) := by
    have hk : k.val < 2^n := k.isLt
    have : (2:ℕ)^n ≤ 2^(n+1) := by rw [pow_succ]; omega
    omega
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · -- index 0: LHS = 0; RHS = bit n of k.val (which is 0 since k.val < 2^n).
    show Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (0 : 𝔽)
            (boolFromFin_msb (𝔽 := 𝔽) k) 0
        = boolPoint_msb (𝔽 := 𝔽) (⟨k.val, hkbnd⟩ : Fin (2^(n+1))) 0
    rw [Fin.cons_zero]
    show (0 : 𝔽) = if (BitVec.ofFin (⟨k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
              (reverseFin (n := n+1) (0 : Fin (n+1)))
            then (1 : 𝔽) else 0
    have hbit : (BitVec.ofFin (⟨k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
              (reverseFin (n := n+1) (0 : Fin (n+1))) = false := by
      show k.val.testBit ((reverseFin (n := n+1) (0 : Fin (n+1))).val) = false
      rw [show (reverseFin (n := n+1) (0 : Fin (n+1))).val = n from by
        show (n+1) - 1 - 0 = n; omega]
      have hk : k.val < 2^n := k.isLt
      exact Nat.testBit_lt_two_pow hk
    rw [hbit]; simp
  · -- index j'.succ: LHS = boolFromFin_msb k j'; RHS = bit (n - 1 - j') of k.val.
    show Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (0 : 𝔽)
            (boolFromFin_msb (𝔽 := 𝔽) k) j'.succ
        = boolPoint_msb (𝔽 := 𝔽) (⟨k.val, hkbnd⟩ : Fin (2^(n+1))) j'.succ
    rw [Fin.cons_succ]
    show (if k.val.testBit (n - 1 - j'.val) then (1 : 𝔽) else 0)
        = if (BitVec.ofFin (⟨k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
              (reverseFin (n := n+1) j'.succ)
            then (1 : 𝔽) else 0
    have hr : (reverseFin (n := n+1) j'.succ).val = n - 1 - j'.val := by
      show (n+1) - 1 - (j'.val + 1) = n - 1 - j'.val
      have := j'.isLt
      omega
    -- (BitVec.ofFin _).getLsb (reverseFin _) = k.val.testBit (reverseFin _ .val)
    show (if k.val.testBit (n - 1 - j'.val) then (1 : 𝔽) else 0)
        = if k.val.testBit (reverseFin (n := n+1) j'.succ).val
            then (1 : 𝔽) else 0
    rw [hr]

omit [Field 𝔽] [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
/-- Companion for the `c = 1` (high-half) case. -/
private lemma Fin_cons_one_boolFromFin_msb_eq [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) :
    (Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (1 : 𝔽)
      (boolFromFin_msb (𝔽 := 𝔽) k))
      = boolPoint_msb (𝔽 := 𝔽) (n := n+1)
          (⟨2^n + k.val, by
            have hk : k.val < 2^n := k.isLt
            show 2^n + k.val < 2^(n+1)
            rw [pow_succ]; omega⟩ : Fin (2^(n+1))) := by
  have hkbnd : 2^n + k.val < 2^(n+1) := by
    have hk : k.val < 2^n := k.isLt
    show 2^n + k.val < 2^(n+1)
    rw [pow_succ]; omega
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · show Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (1 : 𝔽)
            (boolFromFin_msb (𝔽 := 𝔽) k) 0
        = boolPoint_msb (𝔽 := 𝔽) (⟨2^n + k.val, hkbnd⟩ : Fin (2^(n+1))) 0
    rw [Fin.cons_zero]
    show (1 : 𝔽) = if (BitVec.ofFin
              (⟨2^n + k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
              (reverseFin (n := n+1) (0 : Fin (n+1)))
            then (1 : 𝔽) else 0
    have hbit : (BitVec.ofFin
        (⟨2^n + k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
        (reverseFin (n := n+1) (0 : Fin (n+1))) = true := by
      show (2^n + k.val).testBit ((reverseFin (n := n+1) (0 : Fin (n+1))).val) = true
      rw [show (reverseFin (n := n+1) (0 : Fin (n+1))).val = n from by
        show (n+1) - 1 - 0 = n; omega]
      have hk : k.val < 2^n := k.isLt
      rw [Nat.testBit_two_pow_add_eq]
      rw [Nat.testBit_lt_two_pow hk]
      rfl
    rw [hbit]; simp
  · show Fin.cons (α := fun _ : Fin (n+1) => 𝔽) (1 : 𝔽)
            (boolFromFin_msb (𝔽 := 𝔽) k) j'.succ
        = boolPoint_msb (𝔽 := 𝔽) (⟨2^n + k.val, hkbnd⟩ : Fin (2^(n+1))) j'.succ
    rw [Fin.cons_succ]
    show (if k.val.testBit (n - 1 - j'.val) then (1 : 𝔽) else 0)
        = if (BitVec.ofFin (⟨2^n + k.val, hkbnd⟩ : Fin (2^(n+1)))).getLsb
              (reverseFin (n := n+1) j'.succ)
            then (1 : 𝔽) else 0
    have hr : (reverseFin (n := n+1) j'.succ).val = n - 1 - j'.val := by
      have := j'.isLt
      show (n+1) - 1 - (j'.val + 1) = n - 1 - j'.val
      omega
    show (if k.val.testBit (n - 1 - j'.val) then (1 : 𝔽) else 0)
        = if (2^n + k.val).testBit (reverseFin (n := n+1) j'.succ).val
            then (1 : 𝔽) else 0
    rw [hr]
    congr 1
    have hjlt : n - 1 - j'.val < n := by
      have := j'.isLt
      omega
    rw [Nat.testBit_two_pow_add_gt hjlt]

omit [BEq 𝔽] [LawfulBEq 𝔽] in
/-- **Task 3 — Final bridge: `s0` matches the symbolic eval-form spec at round 0
    on input `c = 0`.** -/
theorem compute_correctness_at_zero
    {n : ℕ} (p : CPoly.CMvPolynomial (n+1) 𝔽) :
    (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)).1
      = honestProverMessageEvalsAt [(0:𝔽), 1] p ⟨0, Nat.succ_pos n⟩ Fin.elim0 0 := by
  -- LHS: Use compute_correctness_table to express as ∑ k, eval (boolPoint_msb (low k)) p.
  have hL := compute_correctness_table (𝔽 := 𝔽) (n := n) p
  rw [show (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)).1
        = (∑ k : Fin (2^n), CPoly.CMvPolynomial.eval
            (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
              (⟨k.val, by
                have hk : k.val < 2^n := k.isLt
                have : (2:ℕ)^n ≤ 2^(n+1) := by rw [pow_succ]; omega
                omega⟩ : Fin (2^(n+1)))) p) from by rw [hL]]
  -- RHS: unfold and apply Task 1 + Task 2.
  rw [honestProverMessageEvalsAt_zero_unfold]
  rw [sumOverDomainRecursive_bool_eq_finSum
        (F := fun x => CPoly.CMvPolynomial.eval (Fin.cons (0 : 𝔽) x) p)]
  rw [finSum_lsb_eq_msb
        (F := fun x => CPoly.CMvPolynomial.eval (Fin.cons (0 : 𝔽) x) p)]
  -- Now align points via Fin_cons_zero_boolFromFin_msb_eq.
  apply Finset.sum_congr rfl
  intro k _
  -- LHS index: ⟨k.val, _⟩; RHS uses Fin.cons 0 (boolFromFin_msb k) which equals
  -- boolPoint_msb of ⟨k.val, _⟩ by Fin_cons_zero_boolFromFin_msb_eq.
  rw [Fin_cons_zero_boolFromFin_msb_eq]

omit [BEq 𝔽] [LawfulBEq 𝔽] in
/-- **Task 4 — Companion: `s1` matches the symbolic eval-form spec at round 0
    on input `c = 1`.** -/
theorem compute_correctness_at_one
    {n : ℕ} (p : CPoly.CMvPolynomial (n+1) 𝔽) :
    (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)).2
      = honestProverMessageEvalsAt [(0:𝔽), 1] p ⟨0, Nat.succ_pos n⟩ Fin.elim0 1 := by
  have hL := compute_correctness_table (𝔽 := 𝔽) (n := n) p
  rw [show (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)).2
        = (∑ k : Fin (2^n), CPoly.CMvPolynomial.eval
            (boolPoint_msb (𝔽 := 𝔽) (n := n+1)
              (⟨2^n + k.val, by
                have hk : k.val < 2^n := k.isLt
                show 2^n + k.val < 2^(n+1)
                rw [pow_succ]; omega⟩ : Fin (2^(n+1)))) p) from by rw [hL]]
  rw [honestProverMessageEvalsAt_zero_unfold]
  rw [sumOverDomainRecursive_bool_eq_finSum
        (F := fun x => CPoly.CMvPolynomial.eval (Fin.cons (1 : 𝔽) x) p)]
  rw [finSum_lsb_eq_msb
        (F := fun x => CPoly.CMvPolynomial.eval (Fin.cons (1 : 𝔽) x) p)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin_cons_one_boolFromFin_msb_eq]

omit [BEq 𝔽] [LawfulBEq 𝔽] in
/-- **Task 4 (bundled): full round-0 correctness.** -/
theorem compute_correctness
    {n : ℕ} (p : CPoly.CMvPolynomial (n+1) 𝔽) :
    computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)
      = ( honestProverMessageEvalsAt [(0:𝔽), 1] p ⟨0, Nat.succ_pos n⟩ Fin.elim0 0,
          honestProverMessageEvalsAt [(0:𝔽), 1] p ⟨0, Nat.succ_pos n⟩ Fin.elim0 1 ) := by
  refine Prod.ext ?_ ?_
  · exact compute_correctness_at_zero p
  · exact compute_correctness_at_one p

/-! ### Phase 2 multi-round correctness

The `fold_correctness` theorem ties the table-side `fold_msb_succ` operation
to the symbolic-side `substRound0` substitution; from there
`multi_round_correctness` follows by induction on `n`.

Both theorems are now unconditional: the pointwise-evaluation property of
`substRound0` for polynomials that are multilinear at variable 0 is proved in
[`SumcheckProtocol/Src/SubstRound0.lean`](../Src/SubstRound0.lean). -/

omit [DecidableEq 𝔽] in
/-- **`fold_correctness`** (conditional, multilinear at variable 0).

For `p` multilinear in its high-order variable, the table representation
commutes with the substitution: building the eval-table of
`substRound0 w p` is the same as folding the eval-table of `p` by `w`.

Now unconditional: uses `CPoly.eval_substRound0_multilinear` proven in
`SumcheckProtocol/Src/SubstRound0.lean`. -/
theorem fold_correctness {n : ℕ}
    (w : 𝔽) (p : CPoly.CMvPolynomial (n + 1) 𝔽)
    (hp_ml : CPoly.CMvPolynomial.degreeOf (0 : Fin (n + 1)) p ≤ 1) :
    toEvalTable (𝔽 := 𝔽) (CPoly.substRound0 w p)
      = fold_msb_succ w (toEvalTable (𝔽 := 𝔽) p) := by
  -- Both sides are `Vector 𝔽 (2^n)`. Compare pointwise.
  apply Vector.ext
  intro k hk
  set kFin : Fin (2^n) := ⟨k, hk⟩
  rw [show (toEvalTable (𝔽 := 𝔽) (CPoly.substRound0 w p))[k]
        = (toEvalTable (𝔽 := 𝔽) (CPoly.substRound0 w p))[kFin] from rfl]
  rw [show (fold_msb_succ w (toEvalTable (𝔽 := 𝔽) p))[k]
        = (fold_msb_succ w (toEvalTable (𝔽 := 𝔽) p))[kFin] from rfl]
  rw [getElem_toEvalTable]
  rw [fold_msb_succ_lerp_form w p kFin]
  rw [← boolFromFin_msb_eq_boolPoint_msb]
  -- Apply the now-proven multilinear extension at b = boolFromFin_msb kFin.
  rw [CPoly.eval_substRound0_multilinear w p (boolFromFin_msb (𝔽 := 𝔽) kFin) hp_ml]
  rw [Fin_cons_zero_boolFromFin_msb_eq (𝔽 := 𝔽) kFin]
  rw [Fin_cons_one_boolFromFin_msb_eq (𝔽 := 𝔽) kFin]
  ring

omit [DecidableEq 𝔽] in
/-- **Multi-round recurrence (operational).**

The recursive unfolding of `multilinearProverEvalForm` on `toEvalTable p`:
the head is `computeS0S1_msb` of the input table, and the tail recurses
on the eval-table of the round-0 substituted polynomial.

This is the operational equation underlying `multi_round_correctness`:
combined with `compute_correctness` (round 0) and the symbolic-side recursion
lemma `honestProver_substRound0_bridge`, it inducts to the full multi-round
correctness statement.

Conditional only on `degreeOf 0 p ≤ 1`. -/
theorem multilinearProverEvalForm_recurse {n : ℕ}
    (challenges : Fin (n + 1) → 𝔽)
    (p : CPoly.CMvPolynomial (n + 1) 𝔽)
    (hp_ml : CPoly.CMvPolynomial.degreeOf (0 : Fin (n + 1)) p ≤ 1) :
    multilinearProverEvalForm challenges (toEvalTable (𝔽 := 𝔽) p)
      = computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p)
        :: multilinearProverEvalForm
              (fun j : Fin n => challenges ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (toEvalTable (𝔽 := 𝔽)
                (CPoly.substRound0 (challenges ⟨0, Nat.succ_pos n⟩) p)) := by
  show (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p) ::
          multilinearProverEvalForm
            (fun j : Fin n => challenges ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            (fold_msb_succ (challenges ⟨0, Nat.succ_pos n⟩)
              (toEvalTable (𝔽 := 𝔽) p))) = _
  rw [fold_correctness (challenges ⟨0, Nat.succ_pos n⟩) p hp_ml]

/-! ### Multi-round correctness -/

/-- Symbolic-side recursion under `substRound0`, as a Prop-valued
hypothesis. Provable from `CPoly.eval_substRound0` + careful Fin index
manipulation through `residualSumWithOpenVars`. -/
def HonestProverSubstRound0Bridge (𝔽 : Type _) [Field 𝔽] [DecidableEq 𝔽]
    [BEq 𝔽] [LawfulBEq 𝔽] : Prop :=
  ∀ {m : ℕ} (r₀ : 𝔽) (q : CPoly.CMvPolynomial (m + 1) 𝔽)
    (i : Fin m) (ch : Fin i.val → 𝔽) (c : 𝔽),
    honestProverMessageEvalsAt [(0 : 𝔽), 1] (CPoly.substRound0 r₀ q) i ch c
      = honestProverMessageEvalsAt [(0 : 𝔽), 1] q
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Fin.cons r₀ ch) c

/-- Multilinearity preservation under `substRound0`, as a Prop-valued
hypothesis. Provable via Mathlib's `degreeOf_coeff_finSuccEquiv` bridge. -/
def SubstRound0PreservesMultilinear (𝔽 : Type _) [Field 𝔽] [DecidableEq 𝔽]
    [BEq 𝔽] [LawfulBEq 𝔽] : Prop :=
  ∀ {m : ℕ} (w : 𝔽) (q : CPoly.CMvPolynomial (m + 1) 𝔽),
    (∀ j : Fin (m + 1), CPoly.CMvPolynomial.degreeOf j q ≤ 1) →
    (∀ j : Fin m, CPoly.CMvPolynomial.degreeOf j (CPoly.substRound0 w q) ≤ 1)

/-- Concrete proof of the symbolic-side recursion under `substRound0`. -/
theorem honestProver_substRound0_bridge :
    HonestProverSubstRound0Bridge 𝔽 := by
  intro m r₀ q i ch c
  unfold honestProverMessageEvalsAt residualSumWithOpenVars
  simp [numOpenVars]
  let a : ℕ := m - (i.val + 1)
  let b : ℕ := m + 1 - (i.val + 1 + 1)
  have hab : a = b := by omega
  have hleft : m = i.val + 1 + a := by omega
  have hright : m + 1 = i.val + 1 + 1 + b := by omega
  trans sumOverDomainRecursive (𝔽 := 𝔽) (β := 𝔽) [(0 : 𝔽), 1] (· + ·) 0 (m := b)
      (fun x => CPoly.CMvPolynomial.eval
        (fun i_1 => Fin.addCases (Fin.snoc ch c) (x ∘ Fin.cast hab) (Fin.cast hleft i_1))
        (CPoly.substRound0 r₀ q))
  · exact sum_over_domain_recursive_cast (𝔽 := 𝔽) (β := 𝔽) [(0 : 𝔽), 1] (· + ·) 0 hab _
  · refine sum_over_domain_recursive_congr (𝔽 := 𝔽) (β := 𝔽) [(0 : 𝔽), 1] (· + ·) 0 ?_
    intro x
    rw [CPoly.eval_substRound0]
    congr 1
    change Fin.cons r₀ (Fin.append (Fin.snoc ch c) (x ∘ Fin.cast hab) ∘ Fin.cast hleft) =
      Fin.append (Fin.snoc (Fin.cons r₀ ch) c) x ∘ Fin.cast hright
    rw [← Fin.cons_snoc_eq_snoc_cons]
    rw [Fin.append_cons]
    funext t
    refine Fin.cases ?_ (fun t' => ?_) t
    · simp [Function.comp_def]
    · rw [Fin.append_cast_right (xs := Fin.snoc ch c) (ys := x) (m' := a) hab]
      simp [Function.comp_def]

omit [DecidableEq 𝔽] in
private theorem fromCMvPolynomial_substRound0_symm {m : ℕ}
    (w : 𝔽) (p : MvPolynomial (Fin (m + 1)) 𝔽) :
    CPoly.fromCMvPolynomial
        (CPoly.substRound0 w ((CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).symm p))
      =
    Polynomial.eval (MvPolynomial.C w) (MvPolynomial.finSuccEquiv 𝔽 m p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hsymm : (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).symm (MvPolynomial.C a)
          = CPoly.CMvPolynomial.C (n := m + 1) a := by
        apply (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).injective
        rw [RingEquiv.apply_symm_apply]
        exact (CPoly.CMvPolynomial.fromCMvPolynomial_C (n := m + 1) (R := 𝔽) a).symm
      rw [hsymm, CPoly.substRound0_C]
      simpa [MvPolynomial.finSuccEquiv_apply] using
        CPoly.CMvPolynomial.fromCMvPolynomial_C (n := m) (R := 𝔽) a
  | add p q hp hq =>
      simp [map_add, hp, hq, CPoly.substRound0_add]
  | mul_X p j hp =>
      rw [map_mul]
      unfold CPoly.substRound0
      rw [CPoly.CMvPolynomial.bind₁_mul]
      rw [CPoly.map_mul]
      change CPoly.fromCMvPolynomial (CPoly.substRound0 w (CPoly.polyRingEquiv.symm p)) *
          CPoly.fromCMvPolynomial (CPoly.substRound0 w (CPoly.polyRingEquiv.symm (MvPolynomial.X j))) =
        Polynomial.eval (MvPolynomial.C w) ((MvPolynomial.finSuccEquiv 𝔽 m) (p * MvPolynomial.X j))
      rw [hp]
      rw [map_mul, Polynomial.eval_mul]
      congr 1
      refine Fin.cases ?_ (fun k => ?_) j
      · have hsymm : (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).symm
            (MvPolynomial.X (0 : Fin (m + 1)))
            = CPoly.CMvPolynomial.X (R := 𝔽) (0 : Fin (m + 1)) := by
          apply (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).injective
          rw [RingEquiv.apply_symm_apply]
          exact (CPoly.CMvPolynomial.fromCMvPolynomial_X (R := 𝔽) (0 : Fin (m + 1))).symm
        rw [hsymm]
        unfold CPoly.substRound0
        rw [CPoly.CMvPolynomial.bind₁_X]
        rw [MvPolynomial.finSuccEquiv_X_zero]
        unfold CPoly.substRound0Map
        simp only [Polynomial.eval_X]
        change CPoly.fromCMvPolynomial (CPoly.CMvPolynomial.C (n := m) w) = MvPolynomial.C w
        exact CPoly.CMvPolynomial.fromCMvPolynomial_C (n := m) (R := 𝔽) w
      · have hsymm : (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).symm (MvPolynomial.X k.succ)
            = CPoly.CMvPolynomial.X (R := 𝔽) k.succ := by
          apply (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).injective
          rw [RingEquiv.apply_symm_apply]
          exact (CPoly.CMvPolynomial.fromCMvPolynomial_X (R := 𝔽) k.succ).symm
        rw [hsymm]
        unfold CPoly.substRound0
        rw [CPoly.CMvPolynomial.bind₁_X]
        rw [MvPolynomial.finSuccEquiv_X_succ]
        unfold CPoly.substRound0Map
        simp only [Fin.cases_succ, Polynomial.eval_C]
        change CPoly.fromCMvPolynomial (CPoly.CMvPolynomial.X (R := 𝔽) k) = MvPolynomial.X k
        exact CPoly.CMvPolynomial.fromCMvPolynomial_X (R := 𝔽) k

omit [DecidableEq 𝔽] in
private theorem fromCMvPolynomial_substRound0 {m : ℕ}
    (w : 𝔽) (q : CPoly.CMvPolynomial (m + 1) 𝔽) :
    CPoly.fromCMvPolynomial (CPoly.substRound0 w q)
      =
    Polynomial.eval (MvPolynomial.C w) (MvPolynomial.finSuccEquiv 𝔽 m (CPoly.fromCMvPolynomial q)) := by
  have h := fromCMvPolynomial_substRound0_symm (𝔽 := 𝔽) (m := m) w
    (CPoly.fromCMvPolynomial q)
  have hround :
      (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).symm (CPoly.fromCMvPolynomial q) = q := by
    exact (CPoly.polyRingEquiv (n := m + 1) (R := 𝔽)).left_inv q
  simpa [hround] using h

omit [DecidableEq 𝔽] [BEq 𝔽] [LawfulBEq 𝔽] in
private theorem degreeOf_polynomial_eval_C_le_sup {m : ℕ}
    (j : Fin m) (w : 𝔽) (P : Polynomial (MvPolynomial (Fin m) 𝔽)) :
    MvPolynomial.degreeOf j (Polynomial.eval (MvPolynomial.C w) P) ≤
      P.support.sup (fun i => MvPolynomial.degreeOf j (P.coeff i)) := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  calc
    MvPolynomial.degreeOf j (P.toFinsupp.sum fun e a => a * MvPolynomial.C w ^ e) ≤
        P.support.sup (fun i => MvPolynomial.degreeOf j ((fun e => P.coeff e * MvPolynomial.C w ^ e) i)) := by
      simpa [Polynomial.support] using
        MvPolynomial.degreeOf_sum_le (R := 𝔽) j P.support
          (fun i => P.coeff i * MvPolynomial.C w ^ i)
    _ ≤ P.support.sup (fun i => MvPolynomial.degreeOf j (P.coeff i)) := by
      apply Finset.sup_mono_fun
      intro i hi
      have hmul := MvPolynomial.degreeOf_mul_le j (P.coeff i) (MvPolynomial.C w ^ i)
      have hc : MvPolynomial.degreeOf j (MvPolynomial.C w ^ i : MvPolynomial (Fin m) 𝔽) = 0 := by
        rw [← map_pow (MvPolynomial.C : 𝔽 →+* MvPolynomial (Fin m) 𝔽) w i]
        exact MvPolynomial.degreeOf_C (w ^ i) j
      exact hmul.trans_eq (by rw [hc, Nat.add_zero])

/-- Concrete proof that `substRound0` preserves multilinearity of the remaining variables. -/
theorem substRound0_preserves_multilinear :
    SubstRound0PreservesMultilinear 𝔽 := by
  intro m w q hq j
  have hdegSub :
      CPoly.CMvPolynomial.degreeOf j (CPoly.substRound0 w q)
        =
      MvPolynomial.degreeOf j (CPoly.fromCMvPolynomial (CPoly.substRound0 w q)) := by
    simpa using congrFun
      (CPoly.degreeOf_equiv (p := CPoly.substRound0 w q) (S := 𝔽)) j
  rw [hdegSub, fromCMvPolynomial_substRound0 (𝔽 := 𝔽) w q]
  refine le_trans (degreeOf_polynomial_eval_C_le_sup (𝔽 := 𝔽) j w _) ?_
  apply Finset.sup_le
  intro k hk
  have hcoeff :
      MvPolynomial.degreeOf j
          (Polynomial.coeff (MvPolynomial.finSuccEquiv 𝔽 m (CPoly.fromCMvPolynomial q)) k)
        ≤ MvPolynomial.degreeOf j.succ (CPoly.fromCMvPolynomial q) :=
    MvPolynomial.degreeOf_coeff_finSuccEquiv (CPoly.fromCMvPolynomial q) j k
  have hqSucc :
      MvPolynomial.degreeOf j.succ (CPoly.fromCMvPolynomial q) ≤ 1 := by
    have hdeg :
        CPoly.CMvPolynomial.degreeOf j.succ q =
          MvPolynomial.degreeOf j.succ (CPoly.fromCMvPolynomial q) := by
      simpa using congrFun (CPoly.degreeOf_equiv (p := q) (S := 𝔽)) j.succ
    simpa [hdeg] using hq j.succ
  exact le_trans hcoeff hqSucc

/-- **`multi_round_correctness`** (unconditional).

For multilinear `p : CMvPolynomial n 𝔽`, the i-th entry of the eval-table
prover's output list matches the eval-tuple of the symbolic round-i
message. Combined with `multilinearProverEvalForm_length`, this fully
characterises the VSBW multilinear prover.
 -/
theorem multi_round_correctness {n : ℕ}
    (challenges : Fin n → 𝔽)
    (p : CPoly.CMvPolynomial n 𝔽)
    (hp_ml : ∀ i : Fin n, CPoly.CMvPolynomial.degreeOf i p ≤ 1) :
    ∀ (i : Fin n) (hi : i.val < (multilinearProverEvalForm challenges
        (toEvalTable (𝔽 := 𝔽) p)).length),
      (multilinearProverEvalForm challenges (toEvalTable (𝔽 := 𝔽) p))[i.val]'hi
        = ( honestProverMessageEvalsAt [(0 : 𝔽), 1] p i
              (fun j : Fin i.val =>
                challenges ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt i.isLt)⟩) 0,
            honestProverMessageEvalsAt [(0 : 𝔽), 1] p i
              (fun j : Fin i.val =>
                challenges ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt i.isLt)⟩) 1 ) := by
  induction n with
  | zero => intro i _; exact Fin.elim0 i
  | succ m ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · -- Round 0: use compute_correctness; the challenges-prefix at i=0 is empty.
        intro hi
        simp only [multilinearProverEvalForm_recurse challenges p (hp_ml ⟨0, Nat.succ_pos m⟩)]
        show (computeS0S1_msb (toEvalTable (𝔽 := 𝔽) p) :: _)[0]
          = ( honestProverMessageEvalsAt [(0 : 𝔽), 1] p ⟨0, Nat.succ_pos m⟩ _ 0,
              honestProverMessageEvalsAt [(0 : 𝔽), 1] p ⟨0, Nat.succ_pos m⟩ _ 1 )
        simp only [List.getElem_cons_zero]
        convert compute_correctness (𝔽 := 𝔽) p using 2
      · -- Round j.succ: apply IH on (substRound0 r₀ p), bridge with hSubstHonest.
        intro hi
        simp only [multilinearProverEvalForm_recurse challenges p (hp_ml ⟨0, Nat.succ_pos m⟩)]
        let r₀ : 𝔽 := challenges ⟨0, Nat.succ_pos m⟩
        let q : CPoly.CMvPolynomial m 𝔽 := CPoly.substRound0 r₀ p
        have hq_ml : ∀ k : Fin m, q.degreeOf k ≤ 1 :=
          substRound0_preserves_multilinear (𝔽 := 𝔽) r₀ p hp_ml
        let chTail : Fin m → 𝔽 :=
          fun k => challenges ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
        have htail : j.val < (multilinearProverEvalForm chTail
            (toEvalTable (𝔽 := 𝔽) q)).length := by
          rw [multilinearProverEvalForm_length]
          exact j.isLt
        change (multilinearProverEvalForm chTail (toEvalTable (𝔽 := 𝔽) q))[j.val]'htail
          = ( honestProverMessageEvalsAt [(0 : 𝔽), 1] p j.succ
                (fun j_1 : Fin j.succ.val =>
                  challenges ⟨j_1.val,
                    lt_of_lt_of_le j_1.isLt (Nat.le_of_lt j.succ.isLt)⟩) 0,
              honestProverMessageEvalsAt [(0 : 𝔽), 1] p j.succ
                (fun j_1 : Fin j.succ.val =>
                  challenges ⟨j_1.val,
                    lt_of_lt_of_le j_1.isLt (Nat.le_of_lt j.succ.isLt)⟩) 1 )
        have hIH := ih chTail q hq_ml j
        rw [hIH htail]
        · have hB0 := honestProver_substRound0_bridge (𝔽 := 𝔽) (m := m) r₀ p j
            (fun k : Fin j.val => chTail ⟨k.val,
              lt_of_lt_of_le k.isLt (Nat.le_of_lt j.isLt)⟩) (0 : 𝔽)
          have hB1 := honestProver_substRound0_bridge (𝔽 := 𝔽) (m := m) r₀ p j
            (fun k : Fin j.val => chTail ⟨k.val,
              lt_of_lt_of_le k.isLt (Nat.le_of_lt j.isLt)⟩) (1 : 𝔽)
          refine Prod.ext ?_ ?_
          · convert hB0 using 2
            funext k
            refine Fin.cases ?_ (fun k' => ?_) k
            · rw [Fin.cons_zero]; rfl
            · rw [Fin.cons_succ]; rfl
          · convert hB1 using 2
            funext k
            refine Fin.cases ?_ (fun k' => ?_) k
            · rw [Fin.cons_zero]; rfl
            · rw [Fin.cons_succ]; rfl

end SumcheckProtocol.MultilinearProver
