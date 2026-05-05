import LinearCodes.ReedSolomon
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

import Mathlib
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
right size. -/
theorem encode_size (cfg : ReedSolomonConfig F)
    (h_dom : cfg.domain.size = cfg.codeLength) (msg : Array F) :
    (reedSolomonEncode cfg msg).size = cfg.codeLength := by
  unfold reedSolomonEncode
  rw [Array.size_map]
  exact h_dom

/-! ### Linearity -/

/-- Pointwise addition on coefficients distributes through `evalPoly` (List
form). Helper for the Array version. -/
private lemma list_evalPoly_add_zip (l1 l2 : List F)
    (h : l1.length = l2.length) (x : F) :
    (List.zipWith (· + ·) l1 l2).foldr (fun a acc => a + x * acc) 0
      = l1.foldr (fun a acc => a + x * acc) 0
        + l2.foldr (fun a acc => a + x * acc) 0 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp
    | cons _ _ => simp at h
  | cons hd1 tl1 ih =>
    cases l2 with
    | nil => simp at h
    | cons hd2 tl2 =>
      simp only [List.zipWith_cons_cons, List.foldr_cons]
      have h' : tl1.length = tl2.length := by simpa using h
      rw [ih tl2 h']
      ring

/-- Pointwise addition on coefficients distributes through `evalPoly`. -/
private lemma evalPoly_add_zip (m1 m2 : Array F)
    (h : m1.size = m2.size) (x : F) :
    evalPoly (Array.zipWith (· + ·) m1 m2) x
      = evalPoly m1 x + evalPoly m2 x := by
  unfold evalPoly
  rw [← Array.foldr_toList, ← Array.foldr_toList, ← Array.foldr_toList]
  rw [Array.toList_zipWith]
  apply list_evalPoly_add_zip
  rw [← Array.size_eq_length_toList, ← Array.size_eq_length_toList]
  exact h

/-- **Additive linearity.** Encoding the pointwise sum of two messages
equals the pointwise sum of their encodings. -/
theorem encode_add (cfg : ReedSolomonConfig F)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength) :
    reedSolomonEncode cfg (Array.zipWith (· + ·) m1 m2) =
      Array.zipWith (· + ·)
        (reedSolomonEncode cfg m1) (reedSolomonEncode cfg m2) := by
  unfold reedSolomonEncode
  have hsize : m1.size = m2.size := h1.trans h2.symm
  rw [Array.zipWith_map, Array.zipWith_self]
  congr 1
  funext x
  exact evalPoly_add_zip m1 m2 hsize x

/-- Scalar multiplication on coefficients distributes through `evalPoly`. -/
private lemma evalPoly_smul (c : F) (coeffs : Array F) (x : F) :
    evalPoly (coeffs.map (c * ·)) x = c * evalPoly coeffs x := by
  unfold evalPoly
  rw [Array.foldr_map]
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  induction coeffs.toList with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    rw [ih]
    ring

/-- **Scalar multiplicativity.** Encoding a scalar multiple of a message
equals the scalar multiple of its encoding. -/
theorem encode_smul (cfg : ReedSolomonConfig F) (c : F) (msg : Array F) :
    reedSolomonEncode cfg (msg.map (c * ·)) =
      (reedSolomonEncode cfg msg).map (c * ·) := by
  unfold reedSolomonEncode
  rw [Array.map_map]
  congr 1
  funext x
  exact evalPoly_smul c msg x

/-! ### Minimum distance -/

theorem array_exists_ne_index_of_ne [DecidableEq F] (a b : Array F) (n : ℕ) (ha : a.size = n) (hb : b.size = n) (hneq : a ≠ b) :
  ∃ i : Fin n, a.getD i.val 0 ≠ b.getD i.val 0 := by
  by_contra h
  push_neg at h
  apply hneq
  apply Array.ext
  · exact ha.trans hb.symm
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [ha] using hi₁
    have hEq := h ⟨i, hi⟩
    simpa [Array.getElem_eq_getD, hi₁, hi₂] using hEq

open scoped BigOperators in
theorem evalPoly_eq_sum_fin (msg : Array F) (x : F) :
  evalPoly msg x = ∑ i : Fin msg.size, msg[i] * x ^ (i : ℕ) := by
  unfold evalPoly
  rw [← Array.foldr_toList]
  have hlist :
      ∀ l : List F,
        l.foldr (fun a acc => a + x * acc) 0 = ∑ i : Fin l.length, l[i] * x ^ (i : ℕ) := by
    intro l
    induction l with
    | nil =>
        simp
    | cons a tl ih =>
        rw [List.foldr_cons, ih]
        have hsplit :
            (∑ i : Fin (a :: tl).length, (a :: tl)[i] * x ^ (i : ℕ))
              = (a :: tl)[0] * x ^ (0 : ℕ)
                + ∑ i : Fin tl.length, (a :: tl)[i.succ] * x ^ (i.succ : ℕ) := by
          simpa using
            (Fin.sum_univ_succ (f := fun i : Fin (tl.length + 1) =>
              (a :: tl)[i] * x ^ (i : ℕ)))
        rw [hsplit]
        simp [pow_succ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  simpa [Array.length_toList, Array.getElem_fin_eq_getElem_toList] using hlist msg.toList

theorem evalPoly_sub_zip (m1 m2 : Array F) (h : m1.size = m2.size) (x : F) :
  evalPoly (Array.zipWith (· - ·) m1 m2) x = evalPoly m1 x - evalPoly m2 x := by
  have hz :
      Array.zipWith (· - ·) m1 m2
        = Array.zipWith (· + ·) m1 (m2.map ((-1 : F) * ·)) := by
    simpa [sub_eq_add_neg] using
      (Array.zipWith_map_right (as := m1) (bs := m2) (f := ((-1 : F) * ·)) (g := (· + ·))).symm
  rw [hz]
  have hmap : m1.size = (m2.map ((-1 : F) * ·)).size := by
    simpa using h
  rw [evalPoly_add_zip m1 (m2.map ((-1 : F) * ·)) hmap x]
  rw [evalPoly_smul (-1 : F) m2 x]
  ring

theorem hammingDist_eq_codeLength_sub_agreements [DecidableEq F] (a b : Array F) (n : ℕ)
    (ha : a.size = n) (hb : b.size = n) :
    hammingDist a b =
      n - Fintype.card {i : Fin n // a.getD i.val 0 = b.getD i.val 0} := by
  classical
  unfold hammingDist
  rw [if_pos (ha.trans hb.symm)]
  simp only [ha]
  have hfold_count :
      ∀ (xs : List ℕ) (acc : ℕ),
        List.foldl (fun acc i => acc + if a[i]?.getD 0 = b[i]?.getD 0 then 0 else 1) acc xs =
          acc + List.countP (fun i => !(decide (a[i]?.getD 0 = b[i]?.getD 0))) xs := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons x xs ih =>
        intro acc
        by_cases h : a[x]?.getD 0 = b[x]?.getD 0
        · simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih acc
        · simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (acc + 1)
  have hp :
      (fun i : ℕ => !(decide (a[i]?.getD 0 = b[i]?.getD 0))) =
        (fun i : ℕ => decide (a[i]?.getD 0 ≠ b[i]?.getD 0)) := by
    funext i
    by_cases h : a[i]?.getD 0 = b[i]?.getD 0 <;> simp [h]
  have hcount :
      List.foldl
          (fun acc i => acc + if a.getD i 0 = b.getD i 0 then 0 else 1) 0 (List.range n) =
        Nat.count (fun i => a.getD i 0 ≠ b.getD i 0) n := by
    rw [Nat.count]
    simpa [hp] using hfold_count (List.range n) 0
  rw [hcount, Nat.count_eq_card_fintype]
  letI := Nat.CountSet.fintype (p := fun i => a.getD i 0 ≠ b.getD i 0) n
  let e :
      { k : ℕ // k < n ∧ a.getD k 0 ≠ b.getD k 0 } ≃
        { i : Fin n // a.getD i.val 0 ≠ b.getD i.val 0 } :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl }
  rw [Fintype.card_congr e]
  simpa [Fintype.card_fin] using
    (Fintype.card_subtype_compl (p := fun i : Fin n => a.getD i.val 0 = b.getD i.val 0))

open scoped BigOperators in
noncomputable def messagePoly (msg : Array F) : Polynomial F :=
  ∑ i : Fin msg.size, Polynomial.C (msg[i]) * Polynomial.X ^ (i : ℕ)

open scoped BigOperators in
theorem messagePoly_coeff_fin (msg : Array F) (i : Fin msg.size) : (messagePoly msg).coeff (i : ℕ) = msg[i] := by
  unfold messagePoly
  have hsum : (∑ x : Fin msg.size, if i = x then msg[x] else 0) = msg[i] :=
    Fintype.sum_ite_eq i (fun x : Fin msg.size => msg[x])
  simpa [Polynomial.coeff_C_mul_X_pow, Fin.ext_iff] using hsum

open scoped BigOperators in
theorem messagePoly_eval (msg : Array F) (x : F) : (messagePoly msg).eval x = evalPoly msg x := by
  unfold messagePoly
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow]
  symm
  exact evalPoly_eq_sum_fin msg x

open scoped BigOperators in
theorem messagePoly_natDegree_lt_of_nonzero (msg : Array F) (hmsg : messagePoly msg ≠ 0) :
  (messagePoly msg).natDegree < msg.size := by
  refine (Polynomial.natDegree_lt_iff_degree_lt hmsg).2 ?_
  unfold messagePoly
  simpa using (Polynomial.degree_sum_fin_lt (n := msg.size) (f := fun i : Fin msg.size => msg[i]))

theorem reedSolomonEncode_getD (cfg : ReedSolomonConfig F) (msg : Array F) (i : Fin cfg.domain.size) :
  (reedSolomonEncode cfg msg).getD i.val 0 = evalPoly msg (cfg.domain.getD i.val 0) := by
  unfold reedSolomonEncode
  rw [← Array.getElem_eq_getD (xs := cfg.domain.map (fun x => evalPoly msg x)) (i := i.val) (h := by simpa using i.isLt) (fallback := 0)]
  rw [Array.getElem_map]
  rw [Array.getElem_eq_getD (xs := cfg.domain) (i := i.val) (h := i.isLt) (fallback := 0)]

open scoped BigOperators in
theorem agreement_card_lt_messageLength [DecidableEq F] (cfg : ReedSolomonConfig F)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength)
    (h_neq : m1 ≠ m2) :
    Fintype.card {i : Fin cfg.domain.size //
      (reedSolomonEncode cfg m1).getD i.val 0 =
        (reedSolomonEncode cfg m2).getD i.val 0} < cfg.messageLength := by
  classical
  let Δ : Array F := Array.zipWith (· - ·) m1 m2
  let q : Polynomial F := messagePoly Δ
  have hsize : m1.size = m2.size := h1.trans h2.symm
  have hΔsize : Δ.size = cfg.messageLength := by
    simp [Δ, h1, h2]
  rcases array_exists_ne_index_of_ne m1 m2 cfg.messageLength h1 h2 h_neq with ⟨i, hi_ne⟩
  have hi1 : i.val < m1.size := by
    simpa [h1] using i.isLt
  have hi2 : i.val < m2.size := by
    simpa [h2] using i.isLt
  have hiΔ : i.val < Δ.size := by
    simpa [hΔsize] using i.isLt
  let iΔ : Fin Δ.size := ⟨i.val, hiΔ⟩
  have hΔget : Δ.getD i.val 0 = m1.getD i.val 0 - m2.getD i.val 0 := by
    rw [← Array.getElem_eq_getD (xs := Δ) (i := i.val) (h := hiΔ) (fallback := 0)]
    rw [Array.getElem_zipWith (xs := m1) (ys := m2) (f := (· - ·)) (i := i.val) (hi := by simpa [Δ] using hiΔ)]
    rw [Array.getElem_eq_getD (xs := m1) (i := i.val) (h := hi1) (fallback := 0)]
    rw [Array.getElem_eq_getD (xs := m2) (i := i.val) (h := hi2) (fallback := 0)]
  have hΔnz : Δ.getD i.val 0 ≠ 0 := by
    rw [hΔget]
    exact sub_ne_zero.mpr hi_ne
  have hΔelem_nz : Δ[iΔ] ≠ 0 := by
    change Δ[i.val]'hiΔ ≠ 0
    rw [Array.getElem_eq_getD (xs := Δ) (i := i.val) (h := hiΔ) (fallback := 0)]
    exact hΔnz
  have hcoeff : q.coeff (iΔ : ℕ) = Δ[iΔ] := by
    simpa [q] using messagePoly_coeff_fin Δ iΔ
  have hcoeff_nz' : q.coeff (iΔ : ℕ) ≠ 0 := by
    rw [hcoeff]
    exact hΔelem_nz
  have hcoeff_nz : q.coeff i.val ≠ 0 := by
    simpa [iΔ] using hcoeff_nz'
  have hq_ne : q ≠ 0 := by
    intro hq0
    apply hcoeff_nz
    simpa [hq0]
  have hq_deg : q.natDegree < cfg.messageLength := by
    simpa [q, hΔsize] using messagePoly_natDegree_lt_of_nonzero Δ (by simpa [q] using hq_ne)
  let Sidx : Finset (Fin cfg.domain.size) :=
    Finset.univ.filter fun i =>
      (reedSolomonEncode cfg m1).getD i.val 0 = (reedSolomonEncode cfg m2).getD i.val 0
  let Sval : Finset F := Sidx.image fun i => cfg.domain.getD i.val 0
  have h_inj : Set.InjOn (fun i : Fin cfg.domain.size => cfg.domain.getD i.val 0) ↑Sidx := by
    intro i hi j hj hij
    by_contra hne
    exact (h_distinct i j hne) hij
  have hsubset : Sval.val ⊆ q.roots := by
    intro x hx
    have hx' : x ∈ Sval := by
      simpa using hx
    rcases Finset.mem_image.mp hx' with ⟨i, hiSidx, rfl⟩
    have hi_eq : (reedSolomonEncode cfg m1).getD i.val 0 = (reedSolomonEncode cfg m2).getD i.val 0 := by
      exact (Finset.mem_filter.mp hiSidx).2
    rw [reedSolomonEncode_getD (cfg := cfg) (msg := m1) (i := i), reedSolomonEncode_getD (cfg := cfg) (msg := m2) (i := i)] at hi_eq
    have heval0 : evalPoly Δ (cfg.domain.getD i.val 0) = 0 := by
      rw [evalPoly_sub_zip m1 m2 hsize (cfg.domain.getD i.val 0)]
      exact sub_eq_zero.mpr hi_eq
    have hqeval0 : q.eval (cfg.domain.getD i.val 0) = 0 := by
      simpa [q] using (show (messagePoly Δ).eval (cfg.domain.getD i.val 0) = 0 by
        rw [messagePoly_eval]
        exact heval0)
    exact (Polynomial.mem_roots hq_ne).2 (by simpa [Polynomial.IsRoot] using hqeval0)
  have hcard_le : Sval.card ≤ q.natDegree := by
    exact Polynomial.card_le_degree_of_subset_roots hsubset
  have hmain : Sidx.card < cfg.messageLength := by
    calc
      Sidx.card = Sval.card := by
        symm
        exact Finset.card_image_of_injOn h_inj
      _ ≤ q.natDegree := hcard_le
      _ < cfg.messageLength := hq_deg
  rw [Fintype.card_subtype]
  simpa [Sidx] using hmain

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
  have hc1 : (reedSolomonEncode cfg m1).size = cfg.domain.size := by
    rw [h_dom_size]
    exact encode_size cfg h_dom_size m1
  have hc2 : (reedSolomonEncode cfg m2).size = cfg.domain.size := by
    rw [h_dom_size]
    exact encode_size cfg h_dom_size m2
  have hagree :
      Fintype.card {i : Fin cfg.domain.size //
        (reedSolomonEncode cfg m1).getD i.val 0 =
          (reedSolomonEncode cfg m2).getD i.val 0} < cfg.messageLength := by
    exact agreement_card_lt_messageLength cfg h_distinct m1 m2 h1 h2 h_neq
  have hdist := hammingDist_eq_codeLength_sub_agreements
      (reedSolomonEncode cfg m1) (reedSolomonEncode cfg m2) cfg.domain.size hc1 hc2
  rw [hdist]
  rw [← h_dom_size]
  cases hm : cfg.messageLength with
  | zero =>
      exfalso
      simpa [hm] using hagree
  | succ k =>
      rw [hm] at hagree h_le
      have hA_le :
          Fintype.card {i : Fin cfg.domain.size //
            (reedSolomonEncode cfg m1).getD i.val 0 =
              (reedSolomonEncode cfg m2).getD i.val 0} ≤ k :=
        Nat.lt_succ_iff.mp hagree
      have hrhs : cfg.domain.size - (k + 1) + 1 = cfg.domain.size - k := by
        omega
      rw [hrhs]
      simpa using Nat.sub_le_sub_left hA_le cfg.domain.size


/-! ### Injectivity (corollary of `encode_min_distance`) -/

/-- Hamming distance from an array to itself is zero. -/
private lemma hammingDist_self [DecidableEq F] (a : Array F) :
    hammingDist a a = 0 := by
  unfold hammingDist
  rw [if_pos rfl]
  have h : ∀ (l : List ℕ) (acc : ℕ),
      l.foldl (fun ac i => ac + if a.getD i 0 = a.getD i 0 then 0 else 1) acc
        = acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons hd tl ih =>
      intro acc
      rw [List.foldl_cons, if_pos rfl, Nat.add_zero]
      exact ih acc
  exact h (List.range a.size) 0

/-- Encoding is injective on length-`k` messages. Direct corollary of
`encode_min_distance`: distinct messages would yield codewords at Hamming
distance `≥ n − k + 1 > 0` when `k < n`, but equal codewords have
Hamming distance `0`. -/
theorem encode_injective [DecidableEq F] (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (h_distinct : ∀ i j : Fin cfg.domain.size, i ≠ j →
      cfg.domain.getD i.val 0 ≠ cfg.domain.getD j.val 0)
    (h_lt : cfg.messageLength < cfg.codeLength)
    (m1 m2 : Array F)
    (h1 : m1.size = cfg.messageLength) (h2 : m2.size = cfg.messageLength)
    (h_eq : reedSolomonEncode cfg m1 = reedSolomonEncode cfg m2) :
    m1 = m2 := by
  by_contra h_neq
  have hd := encode_min_distance cfg h_dom_size h_distinct m1 m2 h1 h2 h_neq
    (Nat.le_of_lt h_lt)
  rw [h_eq, hammingDist_self] at hd
  omega

/-! ### List-decoding radius (Johnson bound) -/

def johnsonAgreementPositions [DecidableEq F] (cfg : ReedSolomonConfig F) (y m : Array F) : Finset (Fin cfg.domain.size) :=
  Finset.univ.filter fun i =>
    y.getD i.val 0 = (reedSolomonEncode cfg m).getD i.val 0

theorem johnsonAgreementPositions_card_ge [DecidableEq F] (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    (y m : Array F) (h_y_size : y.size = cfg.codeLength)
    (t : ℕ)
    (h_close : hammingDist y (reedSolomonEncode cfg m) ≤ t) :
    cfg.codeLength - t ≤ (johnsonAgreementPositions cfg y m).card := by
  have hy : y.size = cfg.domain.size := by
    simpa [h_dom_size] using h_y_size
  have henc : (reedSolomonEncode cfg m).size = cfg.domain.size := by
    rw [h_dom_size]
    exact encode_size cfg h_dom_size m
  rw [johnsonAgreementPositions]
  rw [hammingDist_eq_codeLength_sub_agreements y (reedSolomonEncode cfg m) cfg.domain.size hy henc] at h_close
  rw [Fintype.card_subtype] at h_close
  omega

theorem johnson_threshold_gt_messageLength (cfg : ReedSolomonConfig F) (t : ℕ)
    (h_johnson :
      (cfg.codeLength - t) * (cfg.codeLength - t) >
        cfg.codeLength * cfg.messageLength) :
    cfg.messageLength < cfg.codeLength - t := by
  let a := cfg.codeLength - t
  have ha1 : a ≤ cfg.codeLength := by
    dsimp [a]
    exact Nat.sub_le _ _
  by_contra hlt
  have ha2 : a ≤ cfg.messageLength := Nat.not_lt.mp hlt
  have hmul : a * a ≤ cfg.codeLength * cfg.messageLength := Nat.mul_le_mul ha1 ha2
  exact (not_le_of_gt h_johnson) hmul

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
  classical
  let S : Set (Array F) := {m : Array F | m.size = cfg.messageLength ∧
    hammingDist y (reedSolomonEncode cfg m) ≤ t}
  refine Set.Finite.of_injOn
    (f := fun m : Array F => johnsonAgreementPositions cfg y m)
    (s := S) (t := (Set.univ : Set (Finset (Fin cfg.domain.size))))
    ?_ ?_ ?_
  · intro m hm
    simp
  · intro m1 hm1 m2 hm2 hEq
    change johnsonAgreementPositions cfg y m1 = johnsonAgreementPositions cfg y m2 at hEq
    have hm1' : m1.size = cfg.messageLength ∧ hammingDist y (reedSolomonEncode cfg m1) ≤ t := by
      simpa [S] using hm1
    have hm2' : m2.size = cfg.messageLength ∧ hammingDist y (reedSolomonEncode cfg m2) ≤ t := by
      simpa [S] using hm2
    rcases hm1' with ⟨hsize1, hclose1⟩
    rcases hm2' with ⟨hsize2, hclose2⟩
    by_contra hneq
    have hcard_ge : cfg.codeLength - t ≤ (johnsonAgreementPositions cfg y m1).card := by
      exact johnsonAgreementPositions_card_ge cfg h_dom_size y m1 h_y_size t hclose1
    have hmsg_lt : cfg.messageLength < cfg.codeLength - t := by
      exact johnson_threshold_gt_messageLength cfg t h_johnson
    let common : Finset (Fin cfg.domain.size) :=
      Finset.univ.filter fun i : Fin cfg.domain.size =>
        (reedSolomonEncode cfg m1).getD i.val 0 = (reedSolomonEncode cfg m2).getD i.val 0
    have hsubset : johnsonAgreementPositions cfg y m1 ⊆ common := by
      intro i hi
      have hi1 : y.getD i.val 0 = (reedSolomonEncode cfg m1).getD i.val 0 := by
        exact (Finset.mem_filter.mp hi).2
      have hi2 : i ∈ johnsonAgreementPositions cfg y m2 := by
        have hi' := hi
        rwa [hEq] at hi'
      have hi2' : y.getD i.val 0 = (reedSolomonEncode cfg m2).getD i.val 0 := by
        exact (Finset.mem_filter.mp hi2).2
      have henc : (reedSolomonEncode cfg m1).getD i.val 0 = (reedSolomonEncode cfg m2).getD i.val 0 := by
        rw [← hi1]
        exact hi2'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, henc⟩
    have hcommon_lt : common.card < cfg.messageLength := by
      have hagree : Fintype.card {i : Fin cfg.domain.size //
          (reedSolomonEncode cfg m1).getD i.val 0 =
            (reedSolomonEncode cfg m2).getD i.val 0} < cfg.messageLength := by
        exact agreement_card_lt_messageLength cfg h_distinct m1 m2 hsize1 hsize2 hneq
      rw [Fintype.card_subtype] at hagree
      simpa [common] using hagree
    have hcard_le : (johnsonAgreementPositions cfg y m1).card ≤ common.card :=
      Finset.card_le_card hsubset
    have hlarge : cfg.messageLength < (johnsonAgreementPositions cfg y m1).card :=
      lt_of_lt_of_le hmsg_lt hcard_ge
    have hsmall : (johnsonAgreementPositions cfg y m1).card < cfg.messageLength :=
      lt_of_le_of_lt hcard_le hcommon_lt
    omega
  · simpa using (finite_univ : (Set.univ : Set (Finset (Fin cfg.domain.size))).Finite)


/-! ### Maximum Correlated Agreement (proximity gap) -/

/-- α-linear combination of `l` words at a fixed length `n`:
`(linComb n fs α)[j] = Σ_i α^i · (fs i).getD j 0`. Out-of-bounds reads
default to `0`, so callers must ensure each `fs i` has size `n`. -/
def linComb (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (α : F) : Array F :=
  Array.ofFn (n := n) fun j : Fin n =>
    (List.finRange l).foldl
      (fun acc i => acc + α ^ i.val * (fs i).getD j.val 0) 0

open scoped BigOperators in
theorem finRange_foldl_eq_sum {l : ℕ} (g : Fin l → F) :
    (List.finRange l).foldl (fun acc i => acc + g i) 0 = ∑ i : Fin l, g i := by
  rw [Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]

noncomputable def linCombCoordPoly (n : ℕ) {l : ℕ}
    (fs : Fin l → Array F) (j : Fin n) : Polynomial F :=
  messagePoly (Array.ofFn fun i : Fin l => (fs i).getD j.val 0)

theorem linCombCoordPoly_coeff (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (j : Fin n) (i : Fin l) :
    (linCombCoordPoly n fs j).coeff i.val = (fs i).getD j.val 0 := by
  let arr : Array F := Array.ofFn fun r : Fin l => (fs r).getD j.val 0
  let k : Fin arr.size := ⟨i.val, by simpa [arr] using i.isLt⟩
  have h := messagePoly_coeff_fin arr k
  simpa [linCombCoordPoly, arr, k] using h

theorem linCombCoordPoly_natDegree_lt_of_nonzero (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (j : Fin n)
    (h : linCombCoordPoly n fs j ≠ 0) :
    (linCombCoordPoly n fs j).natDegree < l := by
  unfold linCombCoordPoly at h ⊢
  simpa only [Array.size_ofFn] using
    (messagePoly_natDegree_lt_of_nonzero (msg := Array.ofFn fun i : Fin l => (fs i).getD j.val 0) h)

theorem linComb_getD (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (α : F) (j : Fin n) :
    (linComb n fs α).getD j.val 0 =
      (List.finRange l).foldl
        (fun acc i => acc + α ^ i.val * (fs i).getD j.val 0) 0 := by
  unfold linComb
  rw [← Array.getElem_eq_getD
    (xs := Array.ofFn (n := n) fun j : Fin n =>
      (List.finRange l).foldl
        (fun acc i => acc + α ^ i.val * (fs i).getD j.val 0) 0)
    (i := j.val) (h := by simpa using j.isLt) (fallback := 0)]
  simp only [Array.getElem_ofFn, Array.size_ofFn]

theorem linCombCoordPoly_eval (n : ℕ) {l : ℕ} (fs : Fin l → Array F) (j : Fin n) (α : F) :
    (linCombCoordPoly n fs j).eval α = (linComb n fs α).getD j.val 0 := by
  unfold linCombCoordPoly
  rw [messagePoly_eval, evalPoly_eq_sum_fin, linComb_getD, finRange_foldl_eq_sum]
  let e : Fin (Array.ofFn fun i : Fin l => (fs i).getD j.val 0).size ≃ Fin l :=
    { toFun := fun x => ⟨x.val, by simpa [Array.size_ofFn] using x.isLt⟩
      invFun := fun i => ⟨i.val, by simpa [Array.size_ofFn] using i.isLt⟩
      left_inv := by intro x; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  simpa [e, mul_comm] using
    (Fintype.sum_equiv e
      (fun x : Fin (Array.ofFn fun i : Fin l => (fs i).getD j.val 0).size =>
        (Array.ofFn fun i : Fin l => (fs i).getD j.val 0)[x] * α ^ ((e x : Fin l) : ℕ))
      (fun i : Fin l => (fs i).getD j.val 0 * α ^ (i : ℕ))
      (by
        intro x
        have hraw :=
          Array.getElem_ofFn (f := fun i : Fin l => (fs i).getD j.val 0) (i := x.val)
            (h := by simpa [Array.size_ofFn] using x.isLt)
        simpa [e] using congrArg (fun a => a * α ^ ((e x : Fin l) : ℕ)) hraw))

def mcaAgreementWitness (cfg : ReedSolomonConfig F) {l : ℕ}
    (fs : Fin l → Array F) (δ : ℕ) : Prop :=
  ∃ S : Finset (Fin cfg.codeLength),
    cfg.codeLength - S.card ≤ δ ∧
    ∀ i : Fin l, ∃ m : Array F, m.size = cfg.messageLength ∧
      ∀ j : Fin cfg.codeLength, j ∈ S →
        (fs i).getD j.val 0 = (reedSolomonEncode cfg m).getD j.val 0

def mcaDomainWitness (cfg : ReedSolomonConfig F) {l : ℕ}
    (fs : Fin l → Array F) (δ : ℕ) : Prop :=
  ∃ S : Finset (Fin cfg.domain.size),
    cfg.codeLength - S.card ≤ δ ∧
    ∀ i : Fin l, ∃ m : Array F, m.size = cfg.messageLength ∧
      ∀ j : Fin cfg.domain.size, j ∈ S →
        (fs i).getD j.val 0 = (reedSolomonEncode cfg m).getD j.val 0

theorem mcaAgreementWitness_of_domainWitness (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F) (δ : ℕ) :
    mcaDomainWitness cfg fs δ → mcaAgreementWitness cfg fs δ := by
  intro hdom
  rcases hdom with ⟨S, hlarge, hagree⟩
  let e : Fin cfg.domain.size ↪ Fin cfg.codeLength := (finCongr h_dom_size).toEmbedding
  refine ⟨S.map e, ?_, ?_⟩
  · simpa [e] using hlarge
  · intro i
    rcases hagree i with ⟨m, hm, hmagree⟩
    refine ⟨m, hm, ?_⟩
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨j0, hj0, hjEq⟩
    have hEq : j0.val = j.val := by
      simpa [e] using congrArg Fin.val hjEq
    simpa [hEq] using hmagree j0 hj0

def mcaGoodScalar [DecidableEq F] (cfg : ReedSolomonConfig F) {l : ℕ}
    (fs : Fin l → Array F) (δ : ℕ) (α : F) : Prop :=
  ∃ m : Array F, m.size = cfg.messageLength ∧
    hammingDist (linComb cfg.codeLength fs α) (reedSolomonEncode cfg m) ≤ δ

theorem mcaGoodScalar_largeAgreement [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (α : F)
    (h_good : mcaGoodScalar cfg fs δ α) :
    ∃ m : Array F, m.size = cfg.messageLength ∧
      ∃ S : Finset (Fin cfg.domain.size),
        cfg.codeLength - S.card ≤ δ ∧
        cfg.messageLength < S.card ∧
        ∀ j : Fin cfg.domain.size, j ∈ S →
          (linComb cfg.codeLength fs α).getD j.val 0 =
            (reedSolomonEncode cfg m).getD j.val 0 := by
  rcases h_good with ⟨m, hm_size, h_close⟩
  let S : Finset (Fin cfg.domain.size) :=
    johnsonAgreementPositions cfg (linComb cfg.codeLength fs α) m
  have hlin_size : (linComb cfg.codeLength fs α).size = cfg.codeLength := by
    simp [linComb]
  have hS_ge : cfg.codeLength - δ ≤ S.card := by
    simpa [S] using
      johnsonAgreementPositions_card_ge cfg h_dom_size
        (linComb cfg.codeLength fs α) m hlin_size δ h_close
  have hcard_le : cfg.codeLength - S.card ≤ δ := by
    omega
  have hmsg_lt : cfg.messageLength < cfg.codeLength - δ :=
    johnson_threshold_gt_messageLength cfg δ h_johnson
  have hmsg_card : cfg.messageLength < S.card := by
    omega
  refine ⟨m, hm_size, S, hcard_le, hmsg_card, ?_⟩
  intro j hj
  have hjS : j ∈ johnsonAgreementPositions cfg (linComb cfg.codeLength fs α) m := by
    simpa [S] using hj
  unfold johnsonAgreementPositions at hjS
  exact (Finset.mem_filter.mp hjS).2

theorem mcaGoodScalar_choice [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength) :
    ∃ msgOf : F → Array F, ∃ suppOf : F → Finset (Fin cfg.domain.size),
      ∀ α : F, mcaGoodScalar cfg fs δ α →
        (msgOf α).size = cfg.messageLength ∧
        cfg.codeLength - (suppOf α).card ≤ δ ∧
        cfg.messageLength < (suppOf α).card ∧
        ∀ j : Fin cfg.domain.size, j ∈ suppOf α →
          (linComb cfg.codeLength fs α).getD j.val 0 =
            (reedSolomonEncode cfg (msgOf α)).getD j.val 0 := by
  classical
  let msgOf : F → Array F := fun α =>
    if h : mcaGoodScalar cfg fs δ α then
      Classical.choose (mcaGoodScalar_largeAgreement cfg h_dom_size fs δ h_johnson α h)
    else
      #[]
  let suppOf : F → Finset (Fin cfg.domain.size) := fun α =>
    if h : mcaGoodScalar cfg fs δ α then
      Classical.choose
        (And.right
          (Classical.choose_spec
            (mcaGoodScalar_largeAgreement cfg h_dom_size fs δ h_johnson α h)))
    else
      ∅
  refine ⟨msgOf, suppOf, ?_⟩
  intro α h_good
  dsimp [msgOf, suppOf]
  simp only [dif_pos h_good]
  let hAG := mcaGoodScalar_largeAgreement cfg h_dom_size fs δ h_johnson α h_good
  have hmsg : (Classical.choose hAG).size = cfg.messageLength :=
    (Classical.choose_spec hAG).1
  have hsupp :
      cfg.codeLength -
          (Classical.choose (And.right (Classical.choose_spec hAG))).card ≤ δ ∧
        cfg.messageLength <
          (Classical.choose (And.right (Classical.choose_spec hAG))).card ∧
        ∀ j : Fin cfg.domain.size,
          j ∈ Classical.choose (And.right (Classical.choose_spec hAG)) →
            (linComb cfg.codeLength fs α).getD j.val 0 =
              (reedSolomonEncode cfg (Classical.choose hAG)).getD j.val 0 :=
    Classical.choose_spec (And.right (Classical.choose_spec hAG))
  exact ⟨hmsg, hsupp.1, hsupp.2.1, hsupp.2.2⟩

noncomputable def mcaGoodScalars [DecidableEq F] [Fintype F] (cfg : ReedSolomonConfig F) {l : ℕ}
    (fs : Fin l → Array F) (δ : ℕ) : Finset F := by
  classical
  exact Finset.univ.filter fun α : F => mcaGoodScalar cfg fs δ α

open scoped BigOperators in
theorem mca_commonSupport_manyScalars_implies_domainWitness [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (h_sizes : ∀ i : Fin l, (fs i).size = cfg.codeLength)
    (S : Finset (Fin cfg.domain.size))
    (hSlarge : cfg.messageLength < S.card)
    (A : Finset F)
    (hAcard : A.card > l + 1)
    (hAprop : ∀ α ∈ A, ∃ m : Array F, m.size = cfg.messageLength ∧
      ∀ j : Fin cfg.domain.size, j ∈ S →
        (linComb cfg.codeLength fs α).getD j.val 0 =
          (reedSolomonEncode cfg m).getD j.val 0) :
    ∀ i : Fin l, ∃ m : Array F, m.size = cfg.messageLength ∧
      ∀ j : Fin cfg.domain.size, j ∈ S →
        (fs i).getD j.val 0 = (reedSolomonEncode cfg m).getD j.val 0 := by
  classical
  by_cases hl0 : l = 0
  · subst hl0
    intro i
    exact False.elim (Fin.elim0 i)
  · have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (n := l) (by omega)
    let mOf : F → Array F := fun α => if hα : α ∈ A then Classical.choose (hAprop α hα) else #[]
    have hmOf_size : ∀ α ∈ B, (mOf α).size = cfg.messageLength := by
      intro α hαB
      have hchoose := Classical.choose_spec (hAprop α (hBA hαB))
      simpa [mOf, hBA hαB] using hchoose.1
    have hmOf_agree : ∀ α ∈ B, ∀ j : Fin cfg.domain.size, j ∈ S →
        (linComb cfg.codeLength fs α).getD j.val 0 =
          (reedSolomonEncode cfg (mOf α)).getD j.val 0 := by
      intro α hαB j hjS
      have hchoose := Classical.choose_spec (hAprop α (hBA hαB))
      simpa [mOf, hBA hαB] using hchoose.2 j hjS
    intro i
    let c : F → F := fun α => (Lagrange.basis B id α).coeff i.val
    let mi : Array F := Array.ofFn (fun t : Fin cfg.messageLength =>
      ∑ α ∈ B, c α * (mOf α).getD t.val 0)
    have hmi_size : mi.size = cfg.messageLength := by
      simp [mi, Array.size_ofFn]
    refine ⟨mi, hmi_size, ?_⟩
    intro j hjS
    let j' : Fin cfg.codeLength := ⟨j.val, by simpa [h_dom_size] using j.isLt⟩
    let Pj : Polynomial F := linCombCoordPoly cfg.codeLength fs j'
    have hPj_eval_eq : ∀ α ∈ B, Pj.eval α = (reedSolomonEncode cfg (mOf α)).getD j.val 0 := by
      intro α hαB
      change (linCombCoordPoly cfg.codeLength fs j').eval α =
        (reedSolomonEncode cfg (mOf α)).getD j.val 0
      rw [linCombCoordPoly_eval]
      simpa [j'] using hmOf_agree α hαB j hjS
    have hPj_deg : Pj.degree < B.card := by
      by_cases hPj0 : Pj = 0
      · simp [hPj0]
      · rw [hBcard]
        exact (Polynomial.natDegree_lt_iff_degree_lt hPj0).1
          (linCombCoordPoly_natDegree_lt_of_nonzero cfg.codeLength (fs := fs) (j := j') hPj0)
    have hcoeff_interp :
        (∑ α ∈ B, Polynomial.C (Pj.eval α) * Lagrange.basis B id α).coeff i.val = Pj.coeff i.val := by
      have hinterp : Lagrange.interpolate B id (fun α => Pj.eval α) = Pj := by
        exact Lagrange.interpolate_poly_eq_self (v := id) Function.injective_id.injOn hPj_deg
      simpa [Lagrange.interpolate_apply] using congrArg (fun p : Polynomial F => p.coeff i.val) hinterp
    have hcoeff_sum : ∑ α ∈ B, c α * Pj.eval α = Pj.coeff i.val := by
      calc
        ∑ α ∈ B, c α * Pj.eval α
            = ∑ α ∈ B, (Polynomial.C (Pj.eval α) * Lagrange.basis B id α).coeff i.val := by
                refine Finset.sum_congr rfl ?_
                intro α hα
                simp [c, Polynomial.coeff_C_mul, mul_comm]
        _ = (∑ α ∈ B, Polynomial.C (Pj.eval α) * Lagrange.basis B id α).coeff i.val := by
              symm
              exact Polynomial.finset_sum_coeff B (fun α => Polynomial.C (Pj.eval α) * Lagrange.basis B id α) i.val
        _ = Pj.coeff i.val := hcoeff_interp
    let x : F := cfg.domain.getD j.val 0
    have hmEq : ∀ α ∈ B,
        Array.ofFn (fun t : Fin cfg.messageLength => (mOf α).getD t.val 0) = mOf α := by
      intro α hαB
      apply Array.ext
      · simp [hmOf_size α hαB, Array.size_ofFn]
      · intro t ht1 ht2
        rw [Array.getElem_ofFn]
        rw [Array.getElem_eq_getD (xs := mOf α) (i := t)
          (h := by simpa [hmOf_size α hαB] using ht1) (fallback := 0)]
    have hinner_range : ∀ α ∈ B,
        (∑ t ∈ Finset.range cfg.messageLength, (mOf α).getD t 0 * x ^ t) = evalPoly (mOf α) x := by
      intro α hαB
      rw [← hmEq α hαB]
      rw [evalPoly_eq_sum_fin]
      rw [Finset.sum_fin_eq_sum_range]
      simp [Array.size_ofFn]
      refine Finset.sum_congr rfl ?_
      intro t ht
      have htlt : t < cfg.messageLength := Finset.mem_range.mp ht
      simp [Array.getElem?_ofFn, htlt]
    have hmi_eval : evalPoly mi x = ∑ α ∈ B, c α * evalPoly (mOf α) x := by
      calc
        evalPoly mi x
            = ∑ t ∈ Finset.range cfg.messageLength,
                (∑ α ∈ B, c α * (mOf α).getD t 0) * x ^ t := by
                  rw [evalPoly_eq_sum_fin]
                  rw [Finset.sum_fin_eq_sum_range]
                  simp [mi, Array.size_ofFn]
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  have htlt : t < cfg.messageLength := Finset.mem_range.mp ht
                  simp [mi, Array.getElem?_ofFn, htlt]
        _ = ∑ t ∈ Finset.range cfg.messageLength,
              ∑ α ∈ B, (c α * (mOf α).getD t 0) * x ^ t := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                rw [Finset.sum_mul]
        _ = ∑ α ∈ B,
              ∑ t ∈ Finset.range cfg.messageLength, (c α * (mOf α).getD t 0) * x ^ t := by
                simpa using
                  (Finset.sum_comm (s := Finset.range cfg.messageLength) (t := B)
                    (f := fun t α => (c α * (mOf α).getD t 0) * x ^ t))
        _ = ∑ α ∈ B, c α * ∑ t ∈ Finset.range cfg.messageLength, (mOf α).getD t 0 * x ^ t := by
              refine Finset.sum_congr rfl ?_
              intro α hα
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
        _ = ∑ α ∈ B, c α * evalPoly (mOf α) x := by
              refine Finset.sum_congr rfl ?_
              intro α hα
              rw [hinner_range α hα]
    have hencode : (reedSolomonEncode cfg mi).getD j.val 0 = ∑ α ∈ B, c α * (reedSolomonEncode cfg (mOf α)).getD j.val 0 := by
      rw [reedSolomonEncode_getD (cfg := cfg) (msg := mi) (i := j)]
      rw [show cfg.domain.getD j.val 0 = x by rfl]
      rw [hmi_eval]
      refine Finset.sum_congr rfl ?_
      intro α hα
      simpa [x] using congrArg (fun y : F => c α * y)
        ((reedSolomonEncode_getD (cfg := cfg) (msg := mOf α) (i := j)).symm)
    have hencode' : (reedSolomonEncode cfg mi).getD j.val 0 = ∑ α ∈ B, c α * Pj.eval α := by
      rw [hencode]
      refine Finset.sum_congr rfl ?_
      intro α hα
      rw [← hPj_eval_eq α hα]
    calc
      (fs i).getD j.val 0 = Pj.coeff i.val := by
        simpa [Pj, j'] using (linCombCoordPoly_coeff cfg.codeLength (fs := fs) (j := j') i).symm
      _ = ∑ α ∈ B, c α * Pj.eval α := by
        symm
        exact hcoeff_sum
      _ = (reedSolomonEncode cfg mi).getD j.val 0 := by
        symm
        exact hencode'

open scoped BigOperators in
theorem mca_local_blocks [DecidableEq F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (A : Finset F)
    (msgOf : F → Array F)
    (suppOf : F → Finset (Fin cfg.domain.size))
    (hchoose : ∀ α ∈ A,
      (msgOf α).size = cfg.messageLength ∧
      cfg.codeLength - (suppOf α).card ≤ δ ∧
      cfg.messageLength < (suppOf α).card ∧
      ∀ j : Fin cfg.domain.size, j ∈ suppOf α →
        (linComb cfg.codeLength fs α).getD j.val 0 =
          (reedSolomonEncode cfg (msgOf α)).getD j.val 0) :
    ∃ blockOf : F → Fin cfg.codeLength × Fin cfg.codeLength,
      ∀ α β, α ∈ A → β ∈ A → blockOf α = blockOf β →
        suppOf α = suppOf β := by
  -- This is the **local bounded-configuration lemma** missing from the current MCA proof. It should be proved only for the chosen finite set `A` and the chosen witness functions `msgOf`, `suppOf`; do **not** try to make the block map global over all good scalars in `F`.
  -- 
  -- Meaning:
  -- - For each `α ∈ A`, `hchoose α` says that `msgOf α` is a Reed–Solomon message whose codeword agrees with `linComb ... α` on a large support `suppOf α`.
  -- - The goal is to compress these locally chosen witnesses into at most `cfg.codeLength^2` classes, encoded by `blockOf α : Fin cfg.codeLength × Fin cfg.codeLength`, such that equal block labels force equal supports.
  -- 
  -- Recommended strategy (paper-faithful, local-on-`A`):
  -- 1. For each coordinate `j`, use `linCombCoordPoly cfg.codeLength fs j` to view
  --    `α ↦ (linComb cfg.codeLength fs α).getD j.val 0`
  --    as evaluation of a degree-`< l` polynomial in `α`.
  -- 2. For each `α ∈ A`, the support `suppOf α` is large (`cfg.messageLength < (suppOf α).card`) and on that support the chosen codeword `reedSolomonEncode cfg (msgOf α)` matches those coordinate polynomials at `α`.
  -- 3. Formalize the paper's **local block/configuration** construction on the finite family indexed by `A`. The output should be a pair of indices in `Fin cfg.codeLength × Fin cfg.codeLength` (or an equivalent local canonical pair that is then reindexed into that type).
  -- 4. Prove the key implication:
  --    if `α, β ∈ A` have the same block label, then the large-agreement supports attached to the chosen witnesses are equal.
  -- 
  -- Two acceptable proof routes:
  -- 
  -- Route A (preferred):
  -- - Follow the local argument from the correlated-agreement paper: each chosen witness on `A` determines a local configuration / block in a codomain of size at most `n^2`; equal configurations imply equal supports.
  -- - Use `linCombCoordPoly_eval`, `linCombCoordPoly_coeff`, and `linCombCoordPoly_natDegree_lt_of_nonzero` for the degree-`< l` polynomial identities in `α`.
  -- 
  -- Route B (equally valid):
  -- - First prove the weaker consequence `(A.image suppOf).card ≤ cfg.codeLength * cfg.codeLength` by constructing an injection of `A.image suppOf` into `Fin cfg.codeLength × Fin cfg.codeLength`.
  -- - Then define `blockOf α` by composing `suppOf α` with that injection.
  -- - If you take this route, the theorem should still return an explicit `blockOf` witnessing `same block ⇒ same support`.
  -- 
  -- Disproof / sanity check guidance:
  -- - The earlier global bounded-family theorem was false because it tried to classify **all** good scalars in the field at once. This theorem is intentionally weaker: `blockOf` may depend on `A`, `msgOf`, and `suppOf`.
  -- - Any proof attempt that silently defines a global `cfgOf : F → Fin _ × Fin _` independent of `A` should be treated as suspect.
  -- 
  -- Why this node is the right abstraction:
  -- - Once this theorem is available, the next node `mca_largeGoodSet_implies_commonSupport` becomes a short and fully checked pigeonhole argument using `Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to`.
  -- - So this node isolates the true remaining mathematics instead of forcing the wrapper theorem to hide it.
  sorry

theorem mca_largeGoodSet_implies_commonSupport [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (A : Finset F)
    (hA_good : ∀ α ∈ A, mcaGoodScalar cfg fs δ α)
    (hAcard : A.card > (l + 1) * cfg.codeLength * cfg.codeLength) :
    ∃ S : Finset (Fin cfg.domain.size),
      cfg.codeLength - S.card ≤ δ ∧
      cfg.messageLength < S.card ∧
      ∃ B : Finset F, B ⊆ A ∧ B.card > l + 1 ∧
        ∀ α ∈ B, ∃ m : Array F, m.size = cfg.messageLength ∧
          ∀ j : Fin cfg.domain.size, j ∈ S →
            (linComb cfg.codeLength fs α).getD j.val 0 =
              (reedSolomonEncode cfg m).getD j.val 0 := by
  classical
  rcases mcaGoodScalar_choice (F := F) cfg h_dom_size fs δ h_johnson with ⟨msgOf, suppOf, hchoose_global⟩
  have hchoose : ∀ α ∈ A,
      (msgOf α).size = cfg.messageLength ∧
      cfg.codeLength - (suppOf α).card ≤ δ ∧
      cfg.messageLength < (suppOf α).card ∧
      ∀ j : Fin cfg.domain.size, j ∈ suppOf α →
        (linComb cfg.codeLength fs α).getD j.val 0 =
          (reedSolomonEncode cfg (msgOf α)).getD j.val 0 := by
    intro α hαA
    exact hchoose_global α (hA_good α hαA)
  rcases mca_local_blocks (F := F) cfg h_dom_size fs δ h_johnson A msgOf suppOf hchoose with ⟨blockOf, hblock⟩
  let t : Finset (Fin cfg.codeLength × Fin cfg.codeLength) := Finset.univ
  have hmaps : ∀ α ∈ A, blockOf α ∈ t := by
    intro α hαA
    simp [t]
  have hmul : t.card * (l + 1) < A.card := by
    have ht : t.card = cfg.codeLength * cfg.codeLength := by
      simp [t]
    rw [ht]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hAcard
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := A) (t := t) (f := blockOf)
      hmaps hmul with ⟨b, hbmem, hBcard⟩
  let B : Finset F := {α ∈ A | blockOf α = b}
  have hBsub : B ⊆ A := by
    intro α hαB
    exact (Finset.mem_filter.mp hαB).1
  have hBcard' : B.card > l + 1 := by
    simpa [B] using hBcard
  have hBnonempty : B.Nonempty := Finset.card_pos.mp <| lt_trans (Nat.succ_pos l) hBcard'
  rcases hBnonempty with ⟨α0, hα0B⟩
  have hα0A : α0 ∈ A := hBsub hα0B
  have hα0props := hchoose α0 hα0A
  rcases hα0props with ⟨hmsg0, hSδ0, hSmsg0, hagree0⟩
  let S : Finset (Fin cfg.domain.size) := suppOf α0
  refine ⟨S, hSδ0, hSmsg0, B, hBsub, hBcard', ?_⟩
  intro α hαB
  have hαA : α ∈ A := hBsub hαB
  have hαprops := hchoose α hαA
  rcases hαprops with ⟨hmsg, hSδ, hSmsg, hagree⟩
  refine ⟨msgOf α, hmsg, ?_⟩
  intro j hjS
  have hblockeq : blockOf α = blockOf α0 := by
    have h1 : blockOf α = b := (Finset.mem_filter.mp hαB).2
    have h0 : blockOf α0 = b := (Finset.mem_filter.mp hα0B).2
    rw [h1, h0]
  have hsupp : suppOf α = suppOf α0 := hblock α α0 hαA hα0A hblockeq
  have hjSupp : j ∈ suppOf α := by
    simpa [S, hsupp] using hjS
  exact hagree j hjSupp

theorem mca_many_good_scalars_implies_commonSupport [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_many : (mcaGoodScalars cfg fs δ).card >
      (l + 1) * cfg.codeLength * cfg.codeLength) :
    ∃ S : Finset (Fin cfg.domain.size),
      cfg.codeLength - S.card ≤ δ ∧
      cfg.messageLength < S.card ∧
      ∃ A : Finset F, A.card > l + 1 ∧
        ∀ α ∈ A, ∃ m : Array F, m.size = cfg.messageLength ∧
          ∀ j : Fin cfg.domain.size, j ∈ S →
            (linComb cfg.codeLength fs α).getD j.val 0 =
              (reedSolomonEncode cfg m).getD j.val 0 := by
  classical
  let good : Finset F := mcaGoodScalars cfg fs δ
  have hgood : ∀ α ∈ good, mcaGoodScalar cfg fs δ α := by
    intro α hα
    simpa [good, mcaGoodScalars] using hα
  obtain ⟨S, hSδ, hSk, B, hBA, hBcard, hBprop⟩ :=
    mca_largeGoodSet_implies_commonSupport cfg h_dom_size fs δ h_johnson good hgood h_many
  exact ⟨S, hSδ, hSk, B, hBcard, hBprop⟩

theorem mca_many_good_scalars_implies_domainWitness [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (h_sizes : ∀ i : Fin l, (fs i).size = cfg.codeLength)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_many : (mcaGoodScalars cfg fs δ).card >
      (l + 1) * cfg.codeLength * cfg.codeLength) :
    mcaDomainWitness cfg fs δ := by
  classical
  rcases mca_many_good_scalars_implies_commonSupport (cfg := cfg) h_dom_size (fs := fs) (δ := δ)
      h_johnson h_many with ⟨S, hSdelta, hSlarge, A, hAcard, hAprop⟩
  refine ⟨S, hSdelta, ?_⟩
  exact mca_commonSupport_manyScalars_implies_domainWitness
    (cfg := cfg) h_dom_size (fs := fs) h_sizes (S := S) hSlarge (A := A) hAcard hAprop

theorem mca_correlated_agreement [DecidableEq F] [Fintype F]
    (cfg : ReedSolomonConfig F)
    (h_dom_size : cfg.domain.size = cfg.codeLength)
    {l : ℕ} (fs : Fin l → Array F)
    (h_sizes : ∀ i : Fin l, (fs i).size = cfg.codeLength)
    (δ : ℕ)
    (h_johnson : (cfg.codeLength - δ) * (cfg.codeLength - δ) >
                 cfg.codeLength * cfg.messageLength)
    (h_threshold : by
      classical
      exact
        (Finset.univ.filter fun α : F =>
          ∃ m : Array F, m.size = cfg.messageLength ∧
            hammingDist (linComb cfg.codeLength fs α)
                        (reedSolomonEncode cfg m) ≤ δ).card >
          (l + 1) * cfg.codeLength * cfg.codeLength) :
    ∃ S : Finset (Fin cfg.codeLength),
      cfg.codeLength - S.card ≤ δ ∧
      ∀ i : Fin l, ∃ m : Array F, m.size = cfg.messageLength ∧
        ∀ j : Fin cfg.codeLength, j ∈ S →
          (fs i).getD j.val 0 = (reedSolomonEncode cfg m).getD j.val 0 := by
  classical
  have h_many :
      (mcaGoodScalars cfg fs δ).card > (l + 1) * cfg.codeLength * cfg.codeLength := by
    simpa [mcaGoodScalars, mcaGoodScalar] using h_threshold
  have hdom : mcaDomainWitness cfg fs δ :=
    mca_many_good_scalars_implies_domainWitness cfg h_dom_size fs h_sizes δ h_johnson h_many
  have hwit : mcaAgreementWitness cfg fs δ :=
    mcaAgreementWitness_of_domainWitness cfg h_dom_size fs δ hdom
  simpa [mcaAgreementWitness] using hwit


end LinearCodes
