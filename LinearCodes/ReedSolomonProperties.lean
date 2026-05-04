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
