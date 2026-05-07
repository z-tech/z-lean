import Sumcheck.Properties.MultilinearProver
import Sumcheck.Src.EvalForm
import Sumcheck.Properties.Lemmas.Hypercube

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

namespace Sumcheck.MultilinearProver

open CompPoly Sumcheck

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
    from `Sumcheck/Src/MultilinearProver.lean`. -/
lemma boolFromFin_msb_eq_boolPoint_msb [Zero 𝔽] [One 𝔽]
    {n : ℕ} (k : Fin (2^n)) :
    boolFromFin_msb (𝔽 := 𝔽) k = boolPoint_msb (𝔽 := 𝔽) k := by
  funext j
  show (if k.val.testBit (n - 1 - j.val) then (1 : 𝔽) else 0)
      = if (BitVec.ofFin k).getLsb (reverseFin j) then (1 : 𝔽) else 0
  -- (BitVec.ofFin k).getLsb i = k.val.testBit i.val (definitional)
  -- and (reverseFin j).val = n - 1 - j.val (by `reverseFin_val`).
  rfl

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

end Sumcheck.MultilinearProver
