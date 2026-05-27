import Mathlib.Tactic
import VectorCommitment.Src.Merkle.Shape
import VectorCommitment.Src.Merkle.Scheme

/-!
Combinatorial lemmas about `MerkleShape.path` / `copath` / `deriveVertexSet`.

The `MerkleShape` typeclass leaves `path` / `copath` totally abstract, so any
useful length lemma must specialise to a concrete shape. We work with
`PerfectBinary` (the only shape with a real body at L1; see
`VectorCommitment/Src/Merkle/Shape.lean`). The other shapes inherit their analogous
lemmas at L9 once they ship real bodies.
-/

namespace PerfectBinary

/-! ### Inner-walk length lemmas (`pathOf.go`, `copathOf.go`). -/

/-- Universal upper bound: the path walk has length at most `fuel + 1`. -/
theorem pathOf_go_length_le (v fuel : Nat) :
    (pathOf.go v fuel).length ≤ fuel + 1 := by
  induction fuel generalizing v with
  | zero => simp [pathOf.go]
  | succ k ih =>
    unfold pathOf.go
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv]
      have := ih ((v - 1) / 2)
      omega

/-- The path walk is always non-empty. -/
theorem pathOf_go_length_pos (v fuel : Nat) :
    0 < (pathOf.go v fuel).length := by
  cases fuel with
  | zero => simp [pathOf.go]
  | succ k =>
    unfold pathOf.go
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv]

/-- Universal upper bound: the copath walk has length at most `fuel`. -/
theorem copathOf_go_length_le_fuel (v fuel : Nat) :
    (copathOf.go v fuel).length ≤ fuel := by
  induction fuel generalizing v with
  | zero => simp [copathOf.go]
  | succ k ih =>
    unfold copathOf.go
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv]
      have := ih ((v - 1) / 2)
      omega

/-- Length identity: the path walk is always exactly one longer than the
    copath walk at the same parameters. The path emits a running vertex at
    each step plus a terminal vertex; the copath emits only siblings. -/
theorem pathOf_go_length_eq_copathOf_go_length_succ (v fuel : Nat) :
    (pathOf.go v fuel).length = (copathOf.go v fuel).length + 1 := by
  induction fuel generalizing v with
  | zero => simp [pathOf.go, copathOf.go]
  | succ k ih =>
    unfold pathOf.go copathOf.go
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv]
      have := ih ((v - 1) / 2)
      omega

/-- "Heap-distance" upper bound: if `v + 1 ≤ 2 ^ k` then the copath walk
    has length at most `k` regardless of fuel — once `v` halves to `0`, the
    walk terminates. -/
theorem copathOf_go_length_le_height (v fuel k : Nat) (h : v + 1 ≤ 2 ^ k) :
    (copathOf.go v fuel).length ≤ k := by
  induction k generalizing v fuel with
  | zero =>
    -- `v + 1 ≤ 2^0 = 1` forces `v = 0`; copath returns `[]`.
    have hv : v = 0 := by
      have : (2 : Nat) ^ 0 = 1 := by simp
      omega
    cases fuel with
    | zero => simp [copathOf.go]
    | succ _ => simp [copathOf.go, hv]
  | succ m ih =>
    cases fuel with
    | zero => simp [copathOf.go]
    | succ f =>
      unfold copathOf.go
      by_cases hv : v = 0
      · simp [hv]
      · -- Step recurses on `(v - 1) / 2`. Need bound `(v-1)/2 + 1 ≤ 2 ^ m`.
        have hpow : (2 : Nat) ^ (m + 1) = 2 ^ m * 2 := by
          rw [pow_succ]
        have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have hv_le : v ≤ 2 * 2 ^ m - 1 := by
          rw [hpow] at h; omega
        have h_recur : (v - 1) / 2 + 1 ≤ 2 ^ m := by
          have h_div : (v - 1) / 2 ≤ 2 ^ m - 1 := by
            have h2pos : (0 : Nat) < 2 := by norm_num
            -- From `v ≤ 2 * 2^m - 1`, get `v - 1 ≤ 2 * 2^m - 2 = 2 * (2^m - 1)`,
            -- so `(v-1)/2 ≤ 2^m - 1`.
            have hv1 : v - 1 ≤ 2 * (2 ^ m - 1) := by omega
            calc (v - 1) / 2
                _ ≤ (2 * (2 ^ m - 1)) / 2 := Nat.div_le_div_right hv1
                _ = 2 ^ m - 1 := by simp [Nat.mul_div_cancel_left _ h2pos]
          omega
        simp only [if_neg hv, List.length_cons]
        have ih' := ih ((v - 1) / 2) f h_recur
        omega

/-- "Heap-distance" lower bound: if `2 ^ k ≤ v + 1` AND `fuel ≥ k`, the
    copath walk has length at least `k`. -/
theorem copathOf_go_length_ge (v fuel k : Nat)
    (h_v : 2 ^ k ≤ v + 1) (h_fuel : k ≤ fuel) :
    k ≤ (copathOf.go v fuel).length := by
  induction k generalizing v fuel with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      unfold copathOf.go
      have hpow : (2 : Nat) ^ (m + 1) = 2 ^ m * 2 := by
        rw [pow_succ]
      have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hv : v ≠ 0 := by
        intro hv0; rw [hv0] at h_v
        rw [hpow] at h_v; omega
      have h_recur_v : 2 ^ m ≤ (v - 1) / 2 + 1 := by
        rw [hpow] at h_v
        -- From `2 * 2^m ≤ v + 1`, get `v ≥ 2 * 2^m - 1`, so
        -- `v - 1 ≥ 2 * 2^m - 2 = 2 * (2^m - 1)`, so `(v-1)/2 ≥ 2^m - 1`.
        have hv_ge : v ≥ 2 * 2 ^ m - 1 := by omega
        have hv1_ge : v - 1 ≥ 2 * (2 ^ m - 1) := by omega
        have h_div : 2 ^ m - 1 ≤ (v - 1) / 2 := by
          have : (2 * (2 ^ m - 1)) / 2 ≤ (v - 1) / 2 :=
            Nat.div_le_div_right hv1_ge
          have heq : (2 * (2 ^ m - 1)) / 2 = 2 ^ m - 1 := by
            simp [Nat.mul_div_cancel_left _ (by norm_num : (0 : Nat) < 2)]
          omega
        omega
      have h_recur_fuel : m ≤ f := by omega
      simp only [if_neg hv, List.length_cons]
      have := ih ((v - 1) / 2) f h_recur_v h_recur_fuel
      omega

/-- Exact copath length: when `2 ^ k ≤ v + 1 ≤ 2 ^ (k + 1) - 1` (`v` sits at
    heap-depth `k`) and the fuel allotment is at least `k`, the copath walk
    emits exactly `k` siblings. -/
theorem copathOf_go_length_eq (v fuel k : Nat)
    (h_lo : 2 ^ k ≤ v + 1) (h_hi : v + 1 ≤ 2 ^ (k + 1) - 1)
    (h_fuel : k ≤ fuel) :
    (copathOf.go v fuel).length = k := by
  -- Refined upper bound: under the tight hypothesis `v + 1 ≤ 2^(k+1) - 1`,
  -- the copath walk has length at most `k` regardless of fuel.
  have h_le_strict : (copathOf.go v fuel).length ≤ k := by
    clear h_lo h_fuel
    induction k generalizing v fuel with
    | zero =>
      -- `v + 1 ≤ 2^1 - 1 = 1` forces `v = 0`.
      have hpow1 : (2 : Nat) ^ 1 = 2 := by simp
      have hv : v = 0 := by rw [hpow1] at h_hi; omega
      cases fuel with
      | zero => simp [copathOf.go]
      | succ _ => simp [copathOf.go, hv]
    | succ m ih =>
      cases fuel with
      | zero => simp [copathOf.go]
      | succ f =>
        unfold copathOf.go
        by_cases hv : v = 0
        · simp [hv]
        · -- `(v-1)/2 + 1 ≤ 2^(m+1) - 1` (recursive hypothesis).
          have hpow : (2 : Nat) ^ (m + 2) = 2 ^ (m + 1) * 2 := by rw [pow_succ]
          have h2m1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
          have hv_le : v ≤ 2 ^ (m + 2) - 2 := by
            -- v + 1 ≤ 2^(m+2) - 1, so v ≤ 2^(m+2) - 2.
            omega
          have h_recur : (v - 1) / 2 + 1 ≤ 2 ^ (m + 1) - 1 := by
            -- (v-1) ≤ 2^(m+2) - 3 = 2 * (2^(m+1)) - 3.
            -- (v-1)/2 ≤ (2 * 2^(m+1) - 3)/2 = 2^(m+1) - 2 (floor).
            have hv1_le : v - 1 ≤ 2 ^ (m + 2) - 3 := by omega
            have h2pos : (0 : Nat) < 2 := by norm_num
            have h_div : (v - 1) / 2 ≤ (2 ^ (m + 2) - 3) / 2 :=
              Nat.div_le_div_right hv1_le
            -- (2^(m+2) - 3)/2 = (2 * 2^(m+1) - 3)/2 = 2^(m+1) - 2 since odd.
            have hpow_eq : (2 : Nat) ^ (m + 2) - 3 = 2 * (2 ^ (m + 1) - 2) + 1 := by
              rw [hpow]; omega
            have h_div_val : (2 ^ (m + 2) - 3) / 2 = 2 ^ (m + 1) - 2 := by
              rw [hpow_eq]; simp [Nat.mul_add_div]
            omega
          simp only [if_neg hv, List.length_cons]
          exact Nat.add_le_add_right (ih _ _ h_recur) 1
  -- Combine with the lower bound.
  have h_ge := copathOf_go_length_ge v fuel k h_lo h_fuel
  omega

end PerfectBinary

-- ---------------------------------------------------------------------------
-- Public lemmas exported via the `MerkleShape` interface (specialised to
-- `PerfectBinary`).
-- ---------------------------------------------------------------------------

/-- Copath length equals depth for the heap-indexed perfect binary tree on
    `2 ^ d` leaves. -/
theorem copath_length_eq_depth (s : PerfectBinary) (i : Nat)
    (h_pow : s.numLeaves = 2 ^ s.depth) (h_i : i < s.numLeaves) :
    (MerkleShape.copath s i).length = MerkleShape.depth s := by
  show (s.copathOf i).length = s.depth
  unfold PerfectBinary.copathOf
  apply PerfectBinary.copathOf_go_length_eq (k := s.depth)
  · -- `2 ^ depth ≤ (numLeaves - 1 + i) + 1`
    rw [h_pow]
    have h2k : 1 ≤ 2 ^ s.depth := Nat.one_le_two_pow
    omega
  · -- `(numLeaves - 1 + i) + 1 ≤ 2 ^ (depth + 1) - 1`
    rw [h_pow]
    have h2k : 1 ≤ 2 ^ s.depth := Nat.one_le_two_pow
    have hpow : (2 : Nat) ^ (s.depth + 1) = 2 ^ s.depth * 2 := by rw [pow_succ]
    rw [hpow]
    omega
  · exact Nat.le_refl _

/-- Path length equals `depth + 1` for the heap-indexed perfect binary tree
    on `2 ^ d` leaves. The path includes both the leaf and the root, so its
    length is one more than the tree's depth.

    Note: the originally-stated `length = depth` was off-by-one; the path
    contains both endpoints, so the correct value is `depth + 1`. We prove
    this by chaining `copath_length_eq_depth` (with fuel `s.depth + 1`,
    which suffices to reach the root) with the path-vs-copath length
    identity. -/
theorem path_length_eq_depth_succ (s : PerfectBinary) (i : Nat)
    (h_pow : s.numLeaves = 2 ^ s.depth) (h_i : i < s.numLeaves) :
    (MerkleShape.path s i).length = MerkleShape.depth s + 1 := by
  show (s.pathOf i).length = s.depth + 1
  unfold PerfectBinary.pathOf
  rw [PerfectBinary.pathOf_go_length_eq_copathOf_go_length_succ]
  -- Reduce to: copath length at fuel = depth + 1 from the leaf is `depth`.
  -- The walk uses `s.depth + 1` fuel; with our exact-length lemma we just
  -- need `k = s.depth ≤ fuel = s.depth + 1`.
  have :
      (PerfectBinary.copathOf.go (s.numLeaves - 1 + i) (s.depth + 1)).length
        = s.depth := by
    apply PerfectBinary.copathOf_go_length_eq (k := s.depth)
    · rw [h_pow]
      have h2k : 1 ≤ 2 ^ s.depth := Nat.one_le_two_pow
      omega
    · rw [h_pow]
      have h2k : 1 ≤ 2 ^ s.depth := Nat.one_le_two_pow
      have hpow : (2 : Nat) ^ (s.depth + 1) = 2 ^ s.depth * 2 := by rw [pow_succ]
      rw [hpow]; omega
    · omega
  rw [this]

/-- The pruned vertex set is contained in the union of copaths over the
    queried indices: every vertex emitted by `deriveVertexSet I` came from
    `copath i` for some `i ∈ I`.

    This corresponds to the inclusion direction of the book's lemma
    `path-pruning-is-copaths-minus-paths` (`copath(I) ∖ path(I) ⊆ copath(I)`).
    The original sorry's conclusion was the trivial `True`; this strengthens
    it to the substantive (and useful) inclusion. -/
theorem deriveVertexSet_subset_internal
    {H : Type} [MerkleHasher H]
    (mc : MerkleCommitment H PerfectBinary) (indices : List Nat) :
    ∀ v ∈ MerkleCommitment.deriveVertexSet mc indices,
      ∃ i ∈ indices, v ∈ MerkleShape.copath mc.shape i := by
  intro v hv
  unfold MerkleCommitment.deriveVertexSet at hv
  rw [List.mem_filter] at hv
  obtain ⟨hv_copath, _⟩ := hv
  rw [List.mem_flatMap] at hv_copath
  exact hv_copath
