import Mathlib.Tactic
import VC.Src.Merkle.Scheme

/-!
# §12.2 — Merkle commitment completeness

Book: *Building Cryptographic Proofs from Hash Functions*, Lemma
`mt-completeness` (`snargs-book.tex` L12644). Statement: for any honest
`commit`/`open`, the verifier's `check` always returns `true`.

## L2 status

The functional `labelAt` (added in `Scheme.lean`) gives us a clean recursive
characterisation of the tree's labels. The completeness proof unfolds in three
steps:

1. **Tree algebra (`Lemmas/PathCopath.lean`)** — for the heap-indexed perfect
   binary tree, `parent(pos) = (pos - 1) / 2` for `pos > 0`, and the sibling
   formula `sibling(2v+1) = 2v+2`, `sibling(2v+2) = 2v+1`. Plus the recursion
   relating `labelAt v` (internal) to its children.
2. **Single-step bridge (`combineUp_eq_parent`)** — `combineUp pos (labelAt pos)
   (labelAt (sibling pos)) = labelAt (parent pos)` whenever `parent pos` is
   internal.
3. **Walk lemma (`walkCopath_eq_root`)** — chained induction on the copath:
   starting from a leaf with `acc = labelAt(leaf)` and feeding the labels of
   `MerkleShape.copath i` produces `labelAt 0`, the root.

Step 1 + Step 2 are short and are sketched in `Lemmas/PathCopath.lean`. Step
3 is the heart of completeness — its proof is by induction on the path
length and reduces to repeated application of Step 2.

The universal `mt_completeness` is closed below using the walk lemma plus a
small `Id.run`/`forIn` reduction helper (`check_forIn_eq_true`). Concrete
`native_decide` round-trips at sizes 4 and 8 in `SchemeTests.lean` give
independent existence proofs for the chain.
-/

namespace MerkleCommitment

variable {H : Type} [MerkleHasher H]

-- ---------------------------------------------------------------------------
-- Step 1: `labelAt` unfolding lemmas
-- ---------------------------------------------------------------------------

/-- `labelAt` at an internal vertex unfolds to `hashNodes` of its children's
    labels. By definitional equation. -/
theorem labelAt_internal
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (v : Nat) (h : v + 1 < MerkleShape.numLeaves mc.shape) :
    labelAt mc msg salts v =
      MerkleHasher.hashNodes mc.hasher
        [labelAt mc msg salts (2 * v + 1), labelAt mc msg salts (2 * v + 2)] := by
  rw [labelAt]
  have hnot : ¬ MerkleShape.numLeaves mc.shape ≤ v + 1 := by omega
  simp [hnot]

/-- `labelAt` at a leaf vertex (`v + 1 ≥ numLeaves`) unfolds to `hashLeaf` of
    the corresponding message symbol. -/
theorem labelAt_leaf
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (v : Nat) (h : MerkleShape.numLeaves mc.shape ≤ v + 1)
    (sym : MerkleHasher.Symbol H)
    (h_sym : msg[v - (MerkleShape.numLeaves mc.shape - 1)]? = some sym) :
    labelAt mc msg salts v =
      MerkleHasher.hashLeaf mc.hasher sym
        (listGetD salts (v - (MerkleShape.numLeaves mc.shape - 1))
          (MerkleHasher.defaultSalt.default)) := by
  rw [labelAt]
  simp [h, h_sym]

-- ---------------------------------------------------------------------------
-- Step 2: single-step `combineUp` bridge
-- ---------------------------------------------------------------------------

/-- For the *left child* `pos = 2v+1`, combining its label with the sibling's
    reproduces `labelAt v` (the parent's label) — provided `v` is internal. -/
theorem combineUp_eq_parent_left
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (v : Nat) (h_v : v + 1 < MerkleShape.numLeaves mc.shape) :
    combineUp mc (2 * v + 1)
              (labelAt mc msg salts (2 * v + 1))
              (labelAt mc msg salts (2 * v + 2)) =
      labelAt mc msg salts v := by
  rw [labelAt_internal mc msg salts v h_v]
  unfold combineUp
  have hodd : (2 * v + 1) % 2 = 1 := by omega
  simp [hodd]

/-- For the *right child* `pos = 2v+2`, combining its label with the
    sibling's reproduces `labelAt v` — provided `v` is internal. The
    parity-controlled branch in `combineUp` swaps the order, so we end
    with the same `hashNodes [labelAt(2v+1), labelAt(2v+2)]`. -/
theorem combineUp_eq_parent_right
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (v : Nat) (h_v : v + 1 < MerkleShape.numLeaves mc.shape) :
    combineUp mc (2 * v + 2)
              (labelAt mc msg salts (2 * v + 2))
              (labelAt mc msg salts (2 * v + 1)) =
      labelAt mc msg salts v := by
  rw [labelAt_internal mc msg salts v h_v]
  unfold combineUp
  have heven : (2 * v + 2) % 2 = 0 := by omega
  simp [heven]

-- ---------------------------------------------------------------------------
-- Step 3: single-step walkCopath bridge
-- ---------------------------------------------------------------------------

/-- Bridge: combining `labelAt pos` with `labelAt sibling(pos)` yields
    `labelAt (parent pos)` regardless of parity. -/
theorem combineUp_at_pos_eq_parent
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (pos : Nat) (h_pos : pos > 0)
    (h_parent_int : (pos - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape) :
    combineUp mc pos
              (labelAt mc msg salts pos)
              (labelAt mc msg salts (PerfectBinary.siblingOf pos)) =
      labelAt mc msg salts ((pos - 1) / 2) := by
  by_cases hodd : pos % 2 = 1
  · -- pos = 2v + 1 (odd, left child); sibling = 2v + 2; parent = v.
    obtain ⟨v, rfl⟩ : ∃ v, pos = 2 * v + 1 := ⟨(pos - 1) / 2, by omega⟩
    have h_parent_eq : (2 * v + 1 - 1) / 2 = v := by omega
    rw [h_parent_eq] at h_parent_int ⊢
    have hsib_val : PerfectBinary.siblingOf (2 * v + 1) = 2 * v + 2 := by
      unfold PerfectBinary.siblingOf
      simp
    rw [hsib_val]
    exact combineUp_eq_parent_left mc msg salts v h_parent_int
  · -- pos = 2v + 2 (even, > 0, right child); sibling = 2v + 1; parent = v.
    have h_pos' : pos ≥ 2 := by omega
    obtain ⟨v, rfl⟩ : ∃ v, pos = 2 * v + 2 := ⟨(pos - 2) / 2, by omega⟩
    have h_parent_eq : (2 * v + 2 - 1) / 2 = v := by omega
    rw [h_parent_eq] at h_parent_int ⊢
    have hsib_val : PerfectBinary.siblingOf (2 * v + 2) = 2 * v + 1 := by
      unfold PerfectBinary.siblingOf
      have : (2 * v + 2) % 2 = 0 := by omega
      simp [this]
    rw [hsib_val]
    exact combineUp_eq_parent_right mc msg salts v h_parent_int

/-- Single inductive step of the walk: when consuming one sibling, the
    accumulator advances from `labelAt pos` to `labelAt (parent pos)`. -/
theorem walkCopath_step
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H))
    (pos : Nat) (h_pos : pos > 0)
    (h_parent_int : (pos - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape)
    (rest : List (MerkleHasher.Digest H)) :
    walkCopath mc pos (labelAt mc msg salts pos)
                       (labelAt mc msg salts (PerfectBinary.siblingOf pos) :: rest) =
      walkCopath mc ((pos - 1) / 2)
                    (labelAt mc msg salts ((pos - 1) / 2)) rest := by
  -- walkCopath on a `cons` reduces (definitionally) to a recursive call with
  -- `combineUp` of the head; substitute the bridge lemma.
  show walkCopath mc ((pos - 1) / 2)
        (combineUp mc pos (labelAt mc msg salts pos)
                          (labelAt mc msg salts (PerfectBinary.siblingOf pos)))
        rest = _
  rw [combineUp_at_pos_eq_parent mc msg salts pos h_pos h_parent_int]

-- ---------------------------------------------------------------------------
-- Step 4: concrete walk-to-root for size-4 PerfectBinary
-- ---------------------------------------------------------------------------

/-- The kth ancestor of a vertex in the heap-indexed binary tree. -/
def ancestor (pos : Nat) : Nat → Nat
  | 0     => pos
  | k + 1 => ancestor ((pos - 1) / 2) k

/-- Size-4 concrete completeness: walking the copath from any leaf to the
    root reconstructs `labelAt 0`. Two applications of `walkCopath_step` —
    a complete worked example of the inductive chain. -/
theorem walkCopath_to_root_4_leaf0
    (mc : MerkleCommitment H PerfectBinary)
    (h_n : MerkleShape.numLeaves mc.shape = 4)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H)) :
    walkCopath mc 3 (labelAt mc msg salts 3)
                    [labelAt mc msg salts 4, labelAt mc msg salts 2]
      = labelAt mc msg salts 0 := by
  -- Step 1: pos = 3, sibling = 4, parent = (3-1)/2 = 1.
  have hint1 : (3 - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape := by
    rw [h_n]; decide
  have hsib3 : (4 : Nat) = PerfectBinary.siblingOf 3 := by
    unfold PerfectBinary.siblingOf; decide
  rw [hsib3]
  rw [walkCopath_step mc msg salts 3 (by decide) hint1]
  -- After step 1: walkCopath mc ((3-1)/2) (labelAt ((3-1)/2)) [labelAt 2].
  -- Reduce (3-1)/2 to 1 syntactically.
  show walkCopath mc 1 (labelAt mc msg salts 1)
        [labelAt mc msg salts 2] = labelAt mc msg salts 0
  -- Step 2: pos = 1, sibling = 2, parent = (1-1)/2 = 0.
  have hint2 : (1 - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape := by
    rw [h_n]; decide
  have hsib1 : (2 : Nat) = PerfectBinary.siblingOf 1 := by
    unfold PerfectBinary.siblingOf; decide
  rw [hsib1]
  rw [walkCopath_step mc msg salts 1 (by decide) hint2]
  -- After step 2 we're at root with empty sibling list.
  show walkCopath mc 0 (labelAt mc msg salts 0) [] = labelAt mc msg salts 0
  rfl

-- ---------------------------------------------------------------------------
-- Step 5: universal walk-to-root via induction
-- ---------------------------------------------------------------------------

/-- Universal form of the walk-to-root lemma: starting at any vertex `pos`
    and consuming the upward sibling chain for `n_steps` levels, we land at
    `labelAt (ancestor pos n_steps)`. -/
theorem walkCopath_lifts_labelAt
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (salts : List (MerkleHasher.Salt H)) :
    ∀ (n_steps : Nat) (pos : Nat),
      (∀ k, k < n_steps →
        ancestor pos k > 0 ∧
        (ancestor pos k - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape) →
      walkCopath mc pos (labelAt mc msg salts pos)
                  ((List.range n_steps).map
                    (fun k => labelAt mc msg salts
                                (PerfectBinary.siblingOf (ancestor pos k))))
        = labelAt mc msg salts (ancestor pos n_steps) := by
  intro n_steps
  induction n_steps with
  | zero =>
    intro pos _h_chain
    simp [ancestor, walkCopath]
  | succ m ih =>
    intro pos h_chain
    -- Decompose the precondition at k=0 to feed walkCopath_step.
    have h0 := h_chain 0 (by omega)
    have h_pos : pos > 0 := by simpa [ancestor] using h0.1
    have h_parent_int : (pos - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape := by
      simpa [ancestor] using h0.2
    -- Decompose List.range (m+1) into 0 :: (1..m).
    have hrange :
        (List.range (m + 1)).map
            (fun k => labelAt mc msg salts
                        (PerfectBinary.siblingOf (ancestor pos k))) =
          labelAt mc msg salts (PerfectBinary.siblingOf pos) ::
          (List.range m).map
            (fun k => labelAt mc msg salts
                        (PerfectBinary.siblingOf (ancestor ((pos - 1) / 2) k))) := by
      simp [List.range_succ_eq_map, List.map_map, ancestor, Function.comp]
    rw [hrange]
    rw [walkCopath_step mc msg salts pos h_pos h_parent_int]
    -- Apply IH at (pos-1)/2 with the chain shifted.
    have ih_chain : ∀ k, k < m →
        ancestor ((pos - 1) / 2) k > 0 ∧
        (ancestor ((pos - 1) / 2) k - 1) / 2 + 1 < MerkleShape.numLeaves mc.shape := by
      intro k hk
      have := h_chain (k + 1) (by omega)
      simpa [ancestor] using this
    rw [ih ((pos - 1) / 2) ih_chain]
    -- Final goal: ancestor ((pos-1)/2) m = ancestor pos (m+1).
    rfl

-- ---------------------------------------------------------------------------
-- Step 6: main mt_completeness theorem (deferred — requires bridging
-- `commit`'s output labels to `labelAt`, `open`'s extraction to the
-- copath labels, and `check`'s `reconstructRoot` to `walkCopath`)
-- ---------------------------------------------------------------------------

/-- Empty-opening completeness: when no indices are queried, `check` returns
    `true` vacuously. A useful warmup that exercises the `commit`/`open`/`check`
    pipeline without invoking the walk lemma. -/
theorem mt_completeness_empty
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H)) :
    let result := mc.commit msg
    let proof  := mc.open msg result.snd []
    let op : Opening H := { indices := [], values := [] }
    mc.check result.fst.root op proof = true := by
  rfl

/-- Bridge: any label in the trapdoor at index `v < 2n - 1` equals
    `labelAt mc msg salts v`. By construction (`buildLabels` is a `map labelAt`
    over `List.range`). -/
theorem trapdoor_labels_eq_labelAt
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (v : Nat) (h_v : v < 2 * MerkleShape.numLeaves mc.shape - 1) :
    let salts : List (MerkleHasher.Salt H) :=
      List.replicate (MerkleShape.numLeaves mc.shape)
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
    (mc.commit msg).snd.labels[v]? = some (labelAt mc msg salts v) := by
  have hne : MerkleShape.numLeaves mc.shape ≠ 0 := Nat.pos_iff_ne_zero.mp h_n_pos
  show (mc.commit msg).snd.labels[v]? = _
  unfold MerkleCommitment.commit MerkleCommitment.buildLabels
  simp [hne]
  rw [List.getElem?_range h_v]
  exact ⟨v, rfl, rfl⟩

/-- Bridge from imperative `commit` to functional `labelAt`: the root in the
    `Committed` returned by `commit` equals `labelAt mc msg salts 0` (where
    `salts` is the default-salt vector used by `commit`). -/
theorem commit_root_eq_labelAt_zero
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0) :
    let salts : List (MerkleHasher.Salt H) :=
      List.replicate (MerkleShape.numLeaves mc.shape)
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
    (mc.commit msg).fst.root = labelAt mc msg salts 0 := by
  -- The `commit` body sets `rootDigest := if n = 0 then ... else listGetD labels 0 ...`,
  -- and `labels = (List.range (2*n - 1)).map (labelAt mc msg salts)`.
  -- Since `n > 0`, the else branch fires; index 0 of the mapped range is `labelAt … 0`.
  have hne : MerkleShape.numLeaves mc.shape ≠ 0 := Nat.pos_iff_ne_zero.mp h_n_pos
  have htotal : 2 * MerkleShape.numLeaves mc.shape - 1 > 0 := by omega
  show (mc.commit msg).fst.root = _
  unfold MerkleCommitment.commit MerkleCommitment.buildLabels MerkleCommitment.listGetD
  simp [hne]
  -- Goal contains `(List.range (2*n-1))[0]?` after simp normalises with
  -- `Option.map`. Closing requires `(List.range total)[0]? = some 0` when
  -- `total > 0`.
  rw [List.getElem?_range htotal]
  rfl

-- ---------------------------------------------------------------------------
-- Step 6 (helpers): structural lemmas linking `copathOf` to `siblingOf ∘ ancestor`,
-- bounds on the ancestor chain, and the d-th ancestor of a leaf.
-- ---------------------------------------------------------------------------

/-- Bounds on ancestors in a perfect binary tree on `2 ^ d` leaves. For a leaf
    `pos = (2 ^ d - 1) + i` with `i < 2 ^ d`, we have
    `2 ^ (d - k) ≤ ancestor pos k + 1 ≤ 2 ^ (d - k + 1) - 1` for all `k ≤ d`. -/
theorem ancestor_bounds_pow2 :
    ∀ (d k : Nat) (pos : Nat),
      2 ^ d ≤ pos + 1 → pos + 1 ≤ 2 ^ (d + 1) - 1 → k ≤ d →
      2 ^ (d - k) ≤ ancestor pos k + 1 ∧
      ancestor pos k + 1 ≤ 2 ^ (d - k + 1) - 1 := by
  intro d k
  induction k generalizing d with
  | zero =>
    intro pos h_lo h_hi _h_le
    simp [ancestor]; exact ⟨h_lo, h_hi⟩
  | succ m ih =>
    intro pos h_lo h_hi h_le
    -- ancestor pos (m+1) = ancestor ((pos-1)/2) m. Apply IH at depth d-1.
    have hd : d ≥ 1 := by omega
    have hd_eq : d - 1 + 1 = d := by omega
    have h2dm1 : 2 ^ (d - 1) ≥ 1 := Nat.one_le_two_pow
    have h2d : 2 ^ d ≥ 1 := Nat.one_le_two_pow
    -- Two-power identity: 2^d = 2 * 2^(d-1).
    have hpow_d : (2 : Nat) ^ d = 2 * 2 ^ (d - 1) := by
      conv_lhs => rw [show d = (d - 1) + 1 from by omega]
      rw [pow_succ]; ring
    -- Two-power identity: 2^(d+1) = 2 * 2^d.
    have hpow_d1 : (2 : Nat) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    -- Bound: 2^(d-1) ≤ (pos-1)/2 + 1.
    have hpos_lo' : 2 ^ (d - 1) ≤ (pos - 1) / 2 + 1 := by
      have h1 : pos ≥ 2 * 2 ^ (d - 1) - 1 := by rw [hpow_d] at h_lo; omega
      have h2 : pos - 1 ≥ 2 * 2 ^ (d - 1) - 2 := by omega
      have h3 : (pos - 1) / 2 ≥ (2 * 2 ^ (d - 1) - 2) / 2 :=
        Nat.div_le_div_right h2
      have h4 : (2 * 2 ^ (d - 1) - 2) / 2 = 2 ^ (d - 1) - 1 := by
        have heq : 2 * 2 ^ (d - 1) - 2 = 2 * (2 ^ (d - 1) - 1) := by omega
        rw [heq]; rw [Nat.mul_div_cancel_left _ (by omega : (0 : Nat) < 2)]
      omega
    -- Bound: (pos-1)/2 + 1 ≤ 2^d - 1.
    have hpos_hi' : (pos - 1) / 2 + 1 ≤ 2 ^ ((d - 1) + 1) - 1 := by
      rw [hd_eq]
      have h1 : pos ≤ 2 * 2 ^ d - 2 := by rw [hpow_d1] at h_hi; omega
      have h2 : pos - 1 ≤ 2 * 2 ^ d - 3 := by omega
      have h3 : (pos - 1) / 2 ≤ (2 * 2 ^ d - 3) / 2 := Nat.div_le_div_right h2
      have h4 : (2 * 2 ^ d - 3) / 2 = 2 ^ d - 2 := by
        have heq : 2 * 2 ^ d - 3 = 1 + 2 * (2 ^ d - 2) := by omega
        rw [heq, Nat.add_mul_div_left _ _ (by omega : (0 : Nat) < 2)]; omega
      omega
    have hm_le : m ≤ d - 1 := by omega
    have ih_app := ih (d - 1) ((pos - 1) / 2) hpos_lo' hpos_hi' hm_le
    have h_anc_eq : ancestor pos (m + 1) = ancestor ((pos - 1) / 2) m := by
      simp [ancestor]
    rw [h_anc_eq]
    have hkm : d - (m + 1) = d - 1 - m := by omega
    rw [hkm]
    exact ih_app


/-- `ancestor pos (k+1) = (ancestor pos k - 1) / 2`. By induction on `k`. -/
theorem ancestor_succ_eq (pos : Nat) :
    ∀ k, ancestor pos (k + 1) = (ancestor pos k - 1) / 2 := by
  intro k
  induction k generalizing pos with
  | zero => simp [ancestor]
  | succ m ih =>
    show ancestor ((pos - 1) / 2) (m + 1) = (ancestor pos (m + 1) - 1) / 2
    rw [ih]
    rfl

/-- Chain precondition for `walkCopath_lifts_labelAt`: in a perfect binary tree
    on `2 ^ d` leaves, every ancestor of leaf `pos` for `k < d` is internal
    (positive and parent index < numLeaves). -/
theorem ancestor_chain_precondition
    (mc : MerkleCommitment H PerfectBinary)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (i : Nat) (h_i : i < mc.shape.numLeaves) :
    ∀ k, k < mc.shape.depth →
      ancestor (mc.shape.numLeaves - 1 + i) k > 0 ∧
      (ancestor (mc.shape.numLeaves - 1 + i) k - 1) / 2 + 1 <
        MerkleShape.numLeaves mc.shape := by
  intro k hk
  -- Position bounds for the leaf in a perfect binary on 2^d leaves.
  have h2d : 1 ≤ 2 ^ mc.shape.depth := Nat.one_le_two_pow
  have hpow_d1 : (2 : Nat) ^ (mc.shape.depth + 1) = 2 ^ mc.shape.depth * 2 := by
    rw [pow_succ]
  have h_pos_lo : 2 ^ mc.shape.depth ≤ mc.shape.numLeaves - 1 + i + 1 := by
    rw [← h_pow]; omega
  have h_pos_hi : mc.shape.numLeaves - 1 + i + 1 ≤ 2 ^ (mc.shape.depth + 1) - 1 := by
    rw [hpow_d1, ← h_pow]; omega
  -- ancestor pos k stays in [2^(d-k), 2^(d-k+1) - 1] when k ≤ d.
  have h_k_le : k ≤ mc.shape.depth := Nat.le_of_lt hk
  have h_bounds := ancestor_bounds_pow2 mc.shape.depth k
    (mc.shape.numLeaves - 1 + i) h_pos_lo h_pos_hi h_k_le
  -- (1) Positivity: 2^(d-k) ≥ 2 because d-k ≥ 1 (since k < d).
  have h_dk_pos : mc.shape.depth - k ≥ 1 := by omega
  have h_pow_ge_two : (2 : Nat) ^ (mc.shape.depth - k) ≥ 2 := by
    have heq : mc.shape.depth - k = (mc.shape.depth - k - 1) + 1 := by omega
    rw [heq, pow_succ]
    have h_le : 1 ≤ 2 ^ (mc.shape.depth - k - 1) := Nat.one_le_two_pow
    omega
  have h_anc_pos : ancestor (mc.shape.numLeaves - 1 + i) k > 0 := by
    have := h_bounds.1; omega
  refine ⟨h_anc_pos, ?_⟩
  -- (2) Parent bound: (ancestor pos k - 1)/2 + 1 = ancestor pos (k+1) + 1
  -- and ancestor pos (k+1) + 1 ≤ 2^(d-(k+1)+1) - 1 = 2^(d-k) - 1 ≤ 2^d - 1 < 2^d = numLeaves.
  have h_k1_le : k + 1 ≤ mc.shape.depth := hk
  have h_bounds_k1 := ancestor_bounds_pow2 mc.shape.depth (k + 1)
    (mc.shape.numLeaves - 1 + i) h_pos_lo h_pos_hi h_k1_le
  have h_anc_k1_eq : ancestor (mc.shape.numLeaves - 1 + i) (k + 1)
      = (ancestor (mc.shape.numLeaves - 1 + i) k - 1) / 2 :=
    ancestor_succ_eq _ k
  have h_anc_le : (ancestor (mc.shape.numLeaves - 1 + i) k - 1) / 2 + 1
      ≤ 2 ^ (mc.shape.depth - (k + 1) + 1) - 1 := by
    rw [← h_anc_k1_eq]; exact h_bounds_k1.2
  have h_dk1_eq : mc.shape.depth - (k + 1) + 1 = mc.shape.depth - k := by omega
  rw [h_dk1_eq] at h_anc_le
  have h_pow_mono : 2 ^ (mc.shape.depth - k) ≤ 2 ^ mc.shape.depth :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h_d_ge : 2 ^ mc.shape.depth ≥ 2 := by
    have : mc.shape.depth = (mc.shape.depth - 1) + 1 := by omega
    rw [this, pow_succ]
    have : 1 ≤ 2 ^ (mc.shape.depth - 1) := Nat.one_le_two_pow
    omega
  -- The chain: (anc - 1)/2 + 1 ≤ 2^(d-k) - 1 ≤ 2^d - 1 < 2^d = numLeaves.
  calc (ancestor (mc.shape.numLeaves - 1 + i) k - 1) / 2 + 1
      ≤ 2 ^ (mc.shape.depth - k) - 1 := h_anc_le
    _ ≤ 2 ^ mc.shape.depth - 1 := by omega
    _ < 2 ^ mc.shape.depth := by omega
    _ = mc.shape.numLeaves := h_pow.symm

theorem ancestor_at_depth_eq_zero
    (mc : MerkleCommitment H PerfectBinary)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (i : Nat) (h_i : i < mc.shape.numLeaves) :
    ancestor (mc.shape.numLeaves - 1 + i) mc.shape.depth = 0 := by
  have h2d : 1 ≤ 2 ^ mc.shape.depth := Nat.one_le_two_pow
  have hpow_d1 : (2 : Nat) ^ (mc.shape.depth + 1) = 2 ^ mc.shape.depth * 2 := by rw [pow_succ]
  have h_pos_lo : 2 ^ mc.shape.depth ≤ mc.shape.numLeaves - 1 + i + 1 := by
    rw [← h_pow]; omega
  have h_pos_hi : mc.shape.numLeaves - 1 + i + 1 ≤ 2 ^ (mc.shape.depth + 1) - 1 := by
    rw [hpow_d1, ← h_pow]; omega
  have h_bounds := ancestor_bounds_pow2 mc.shape.depth mc.shape.depth
    (mc.shape.numLeaves - 1 + i) h_pos_lo h_pos_hi (Nat.le_refl _)
  have h_lb := h_bounds.1
  have h_ub := h_bounds.2
  have h1 : (2 : Nat) ^ (mc.shape.depth - mc.shape.depth) = 1 := by simp
  have h2 : (2 : Nat) ^ (mc.shape.depth - mc.shape.depth + 1) = 2 := by simp
  rw [h1] at h_lb
  rw [h2] at h_ub
  omega

/-- Structural lemma: the inner copath walk emits siblings of ancestors. For a
    starting vertex `pos` such that the chain `ancestor pos k > 0` for all
    `k < fuel`, the result is `(List.range fuel).map (siblingOf ∘ ancestor pos)`. -/
theorem copathOf_go_eq_map_siblingOf_ancestor :
    ∀ (fuel : Nat) (pos : Nat),
      (∀ k, k < fuel → ancestor pos k > 0) →
      PerfectBinary.copathOf.go pos fuel =
        (List.range fuel).map
          (fun k => VertexId.mk (PerfectBinary.siblingOf (ancestor pos k))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos _h
    simp [PerfectBinary.copathOf.go]
  | succ m ih =>
    intro pos h_chain
    have h0 := h_chain 0 (by omega)
    have h_pos_ne : pos ≠ 0 := by
      have h0' : ancestor pos 0 > 0 := h0
      have : ancestor pos 0 = pos := by simp [ancestor]
      rw [this] at h0'
      omega
    unfold PerfectBinary.copathOf.go
    simp only [if_neg h_pos_ne]
    have ih_chain : ∀ k, k < m → ancestor ((pos - 1) / 2) k > 0 := by
      intro k hk
      have hh := h_chain (k + 1) (by omega)
      have heq : ancestor pos (k + 1) = ancestor ((pos - 1) / 2) k := by
        simp [ancestor]
      rw [heq] at hh
      exact hh
    rw [ih ((pos - 1) / 2) ih_chain]
    -- Goal: VertexId.mk (siblingOf pos) :: (range m).map ... =
    --   (range (m+1)).map (fun k => mk (sib (ancestor pos k)))
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    have h_head : PerfectBinary.siblingOf (ancestor pos 0) = PerfectBinary.siblingOf pos := by
      simp [ancestor]
    rw [show ancestor pos 0 = pos from rfl]
    -- After `range_succ_eq_map` + the head rewrite, the two lists agree
    -- pointwise via `ancestor (k+1) = ancestor ((pos-1)/2) k`, which is
    -- definitional. `congr 1` closes the residual element-wise equality.
    rfl

/-- The copath of leaf `i` in a perfect binary tree on `2 ^ d` leaves equals the
    list of siblings of ancestors of `pos = n - 1 + i`. -/
theorem copath_eq_siblingOf_ancestor
    (mc : MerkleCommitment H PerfectBinary)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (i : Nat) (h_i : i < mc.shape.numLeaves) :
    MerkleShape.copath mc.shape i =
      (List.range mc.shape.depth).map
        (fun k => VertexId.mk
          (PerfectBinary.siblingOf
            (ancestor (mc.shape.numLeaves - 1 + i) k))) := by
  show mc.shape.copathOf i = _
  unfold PerfectBinary.copathOf
  apply copathOf_go_eq_map_siblingOf_ancestor
  intro k hk
  exact (ancestor_chain_precondition mc h_pow i h_i k hk).1

/-- Bound: every ancestor `< 2 * numLeaves - 1` (i.e., a valid heap index in the
    full label vector). For `k ≤ depth`, `ancestor pos k + 1 ≤ 2^(depth-k+1) - 1
    ≤ 2^(depth+1) - 1 = 2 * numLeaves - 1`. -/
theorem ancestor_lt_total
    (mc : MerkleCommitment H PerfectBinary)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (i : Nat) (h_i : i < mc.shape.numLeaves) :
    ∀ k, k ≤ mc.shape.depth →
      ancestor (mc.shape.numLeaves - 1 + i) k < 2 * mc.shape.numLeaves - 1 := by
  intro k hk
  have h2d : 1 ≤ 2 ^ mc.shape.depth := Nat.one_le_two_pow
  have hpow_d1 : (2 : Nat) ^ (mc.shape.depth + 1) = 2 ^ mc.shape.depth * 2 := by rw [pow_succ]
  have h_pos_lo : 2 ^ mc.shape.depth ≤ mc.shape.numLeaves - 1 + i + 1 := by
    rw [← h_pow]; omega
  have h_pos_hi : mc.shape.numLeaves - 1 + i + 1 ≤ 2 ^ (mc.shape.depth + 1) - 1 := by
    rw [hpow_d1, ← h_pow]; omega
  have h_bounds := ancestor_bounds_pow2 mc.shape.depth k
    (mc.shape.numLeaves - 1 + i) h_pos_lo h_pos_hi hk
  have h_pow_mono : 2 ^ (mc.shape.depth - k + 1) ≤ 2 ^ (mc.shape.depth + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h_eq_n : 2 * mc.shape.numLeaves - 1 = 2 ^ (mc.shape.depth + 1) - 1 := by
    rw [hpow_d1, ← h_pow]; ring_nf
  rw [h_eq_n]
  omega

/-- Every sibling of an ancestor `< 2 * numLeaves - 1` provided the ancestor
    chain stays internal. Concretely, for `k < depth`, `siblingOf (ancestor pos
    k) < 2 * numLeaves - 1`. -/
theorem siblingOf_ancestor_lt_total
    (mc : MerkleCommitment H PerfectBinary)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (i : Nat) (h_i : i < mc.shape.numLeaves) :
    ∀ k, k < mc.shape.depth →
      PerfectBinary.siblingOf (ancestor (mc.shape.numLeaves - 1 + i) k) <
        2 * mc.shape.numLeaves - 1 := by
  intro k hk
  have h_k_le : k ≤ mc.shape.depth := Nat.le_of_lt hk
  have h2d : 1 ≤ 2 ^ mc.shape.depth := Nat.one_le_two_pow
  have hpow_d1 : (2 : Nat) ^ (mc.shape.depth + 1) = 2 ^ mc.shape.depth * 2 := by rw [pow_succ]
  have h_pos_lo : 2 ^ mc.shape.depth ≤ mc.shape.numLeaves - 1 + i + 1 := by
    rw [← h_pow]; omega
  have h_pos_hi : mc.shape.numLeaves - 1 + i + 1 ≤ 2 ^ (mc.shape.depth + 1) - 1 := by
    rw [hpow_d1, ← h_pow]; omega
  have h_bounds := ancestor_bounds_pow2 mc.shape.depth k
    (mc.shape.numLeaves - 1 + i) h_pos_lo h_pos_hi h_k_le
  have h_anc_pos : ancestor (mc.shape.numLeaves - 1 + i) k > 0 :=
    (ancestor_chain_precondition mc h_pow i h_i k hk).1
  set v := ancestor (mc.shape.numLeaves - 1 + i) k with hv_def
  have hv_ne : v ≠ 0 := by omega
  have h_pow_mono : 2 ^ (mc.shape.depth - k + 1) ≤ 2 ^ (mc.shape.depth + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold PerfectBinary.siblingOf
  simp only [if_neg hv_ne]
  by_cases hodd : v % 2 = 1
  · simp only [hodd, if_true]
    -- 2^(d-k+1) is even.
    have h_pow_even : 2 ∣ (2 : Nat) ^ (mc.shape.depth - k + 1) := by
      rw [pow_succ]; exact ⟨2 ^ (mc.shape.depth - k), by ring⟩
    have h_v_plus_1_even : (v + 1) % 2 = 0 := by omega
    have h_ub : v + 1 ≤ 2 ^ (mc.shape.depth - k + 1) - 1 := h_bounds.2
    have h_pow_odd : (2 ^ (mc.shape.depth - k + 1) - 1) % 2 = 1 := by
      obtain ⟨q, hq⟩ := h_pow_even
      rw [hq]
      have hq_pos : q ≥ 1 := by
        have h_le : 2 ≤ 2 ^ (mc.shape.depth - k + 1) := by
          rw [pow_succ]
          have h2dk : 1 ≤ 2 ^ (mc.shape.depth - k) := Nat.one_le_two_pow
          omega
        omega
      omega
    have h_v_lt : v + 1 ≤ 2 ^ (mc.shape.depth - k + 1) - 2 := by
      by_contra h
      push_neg at h
      have h_eq : v + 1 = 2 ^ (mc.shape.depth - k + 1) - 1 := by omega
      rw [h_eq] at h_v_plus_1_even
      omega
    have h_eq_n : 2 * mc.shape.numLeaves - 1 = 2 ^ (mc.shape.depth + 1) - 1 := by
      rw [hpow_d1, ← h_pow]; ring_nf
    rw [h_eq_n]
    omega
  · simp only [hodd, if_false]
    have h_anc_lt := ancestor_lt_total mc h_pow i h_i k h_k_le
    have h_anc_lt' : v < 2 * mc.shape.numLeaves - 1 := h_anc_lt
    omega

-- ---------------------------------------------------------------------------
-- Step 7: per-leaf reconstruction equals the root
-- ---------------------------------------------------------------------------

/-- For an honest opening of a single leaf `i`, the reconstructed root from the
    leaf's hash and the trapdoor's copath digests equals `labelAt mc msg salts 0`. -/
theorem reconstruct_eq_root
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (h_len : msg.length = mc.shape.numLeaves)
    (h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth)
    (h_n_pos : MerkleShape.numLeaves mc.shape > 0)
    (i : Nat) (h_i : i < mc.shape.numLeaves)
    (value : MerkleHasher.Symbol H)
    (h_value : msg[i]? = some value) :
    let salts : List (MerkleHasher.Salt H) :=
      List.replicate (MerkleShape.numLeaves mc.shape)
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
    let placeholder : MerkleHasher.Digest H :=
      MerkleHasher.hashNodes mc.hasher []
    let copath := MerkleShape.copath mc.shape i
    let digests := copath.map (fun v =>
      MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder)
    mc.reconstructRoot i value
        (MerkleCommitment.listGetD (mc.commit msg).snd.salts i
          (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H))
        digests = labelAt mc msg
          (List.replicate (MerkleShape.numLeaves mc.shape)
            (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)) 0 := by
  let n := MerkleShape.numLeaves mc.shape
  let d := mc.shape.depth
  let salts : List (MerkleHasher.Salt H) :=
    List.replicate n (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
  let placeholder : MerkleHasher.Digest H := MerkleHasher.hashNodes mc.hasher []
  let pos := n - 1 + i
  show mc.reconstructRoot i value
      (MerkleCommitment.listGetD (mc.commit msg).snd.salts i
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H))
      ((MerkleShape.copath mc.shape i).map (fun v =>
        MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder))
      = labelAt mc msg salts 0
  -- The salt list in the trapdoor equals `salts`.
  have h_salts_eq : (mc.commit msg).snd.salts = salts := by
    show (mc.commit msg).snd.salts = List.replicate n _
    unfold MerkleCommitment.commit
    rfl
  have h_salt_at_i :
      MerkleCommitment.listGetD (mc.commit msg).snd.salts i
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) =
      MerkleHasher.defaultSalt.default := by
    rw [h_salts_eq]
    unfold MerkleCommitment.listGetD
    show (List.replicate n (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H))[i]?.getD _ = _
    rw [List.getElem?_replicate]
    have h_i' : i < n := h_i
    simp [h_i']
  -- The copath as VertexId.val list equals `(List.range d).map (siblingOf ∘ ancestor pos)`.
  have h_copath := copath_eq_siblingOf_ancestor mc h_pow i h_i
  -- Translate trapdoor labels at copath into labelAt at the same vertex.
  have h_digests :
      (MerkleShape.copath mc.shape i).map (fun v =>
        MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder) =
      (List.range d).map (fun k =>
        labelAt mc msg salts (PerfectBinary.siblingOf (ancestor pos k))) := by
    rw [h_copath]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk_lt_d : k < d := List.mem_range.mp hk
    have h_sib_lt :
        PerfectBinary.siblingOf (ancestor pos k) < 2 * n - 1 :=
      siblingOf_ancestor_lt_total mc h_pow i h_i k hk_lt_d
    have h_lab :=
      trapdoor_labels_eq_labelAt mc msg h_n_pos
        (PerfectBinary.siblingOf (ancestor pos k)) h_sib_lt
    show MerkleCommitment.listGetD (mc.commit msg).snd.labels _ placeholder
        = mc.labelAt msg salts (PerfectBinary.siblingOf (ancestor pos k))
    unfold MerkleCommitment.listGetD
    show (mc.commit msg).snd.labels[PerfectBinary.siblingOf (ancestor pos k)]?.getD placeholder
        = mc.labelAt msg salts (PerfectBinary.siblingOf (ancestor pos k))
    rw [h_lab]
    rfl
  -- Reconstruct.
  unfold MerkleCommitment.reconstructRoot
  rw [h_salt_at_i, h_digests]
  -- We want: hashLeaf hasher value defaultSalt = labelAt mc msg salts pos.
  have h_pos_leaf : n ≤ pos + 1 := by
    show n ≤ n - 1 + i + 1
    omega
  have h_idx_eq : pos - (n - 1) = i := by
    show n - 1 + i - (n - 1) = i
    omega
  have h_msg_at : msg[pos - (n - 1)]? = some value := by
    rw [h_idx_eq]; exact h_value
  have h_salt_replicate :
      MerkleCommitment.listGetD salts (pos - (n - 1))
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) =
      MerkleHasher.defaultSalt.default := by
    rw [h_idx_eq]
    unfold MerkleCommitment.listGetD
    show (List.replicate n (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H))[i]?.getD _ = _
    rw [List.getElem?_replicate]
    have h_i' : i < n := h_i
    simp [h_i']
  have h_leaf_eq :
      MerkleHasher.hashLeaf mc.hasher value
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H) =
      labelAt mc msg salts pos := by
    rw [labelAt_leaf mc msg salts pos h_pos_leaf value h_msg_at]
    rw [h_salt_replicate]
  show walkCopath mc pos
    (MerkleHasher.hashLeaf mc.hasher value
      (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)) _ = _
  rw [h_leaf_eq]
  have h_chain := ancestor_chain_precondition mc h_pow i h_i
  rw [walkCopath_lifts_labelAt mc msg salts d pos h_chain]
  have h_zero := ancestor_at_depth_eq_zero mc h_pow i h_i
  show mc.labelAt msg salts
    (ancestor (mc.shape.numLeaves - 1 + i) mc.shape.depth) = _
  rw [h_zero]

/-- For `PerfectBinary` with `numLeaves = 2 ^ d`, `depth = d`. -/
theorem perfectBinary_depth_eq_of_pow2 (d : Nat) :
    PerfectBinary.depth (PerfectBinary.mk (2 ^ d)) = d := by
  show PerfectBinary.log2Floor (2 ^ d) = d
  induction d with
  | zero =>
    unfold PerfectBinary.log2Floor
    simp
  | succ m ih =>
    rw [pow_succ]
    unfold PerfectBinary.log2Floor
    have h_pow_pos : 2 ^ m * 2 > 1 := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    have h_not_le : ¬ (2 ^ m * 2 ≤ 1) := by omega
    simp only [h_not_le, dite_false]
    have hd : 2 ^ m * 2 / 2 = 2 ^ m := by simp
    rw [hd, ih]
    omega

/-- For PerfectBinary, when `numLeaves = 2 ^ d`, `numLeaves = 2 ^ depth`. -/
theorem perfectBinary_numLeaves_eq_pow2_depth
    (s : PerfectBinary) (d : Nat) (h : s.numLeaves = 2 ^ d) :
    s.numLeaves = 2 ^ s.depth := by
  show s.numLeaves = 2 ^ PerfectBinary.depth s
  have : PerfectBinary.depth s = PerfectBinary.depth (PerfectBinary.mk (2 ^ d)) := by
    show PerfectBinary.log2Floor s.numLeaves = PerfectBinary.log2Floor (2 ^ d)
    rw [h]
  rw [this, perfectBinary_depth_eq_of_pow2]
  exact h

/-- Auxiliary: the inner `for` loop in `check` returns `true` when every
    triple's reconstructed root agrees with the supplied root. Proved by
    induction on the list of triples. -/
private theorem check_forIn_eq_true
    {S : Type} [MerkleShape S]
    (mc : MerkleCommitment H S) (root : MerkleHasher.Digest H)
    (triples : List ((Nat × MerkleHasher.Symbol H) ×
                      (MerkleHasher.Salt H × List (MerkleHasher.Digest H))))
    (h_per :
      ∀ t ∈ triples,
        mc.reconstructRoot t.1.1 t.1.2 t.2.1 t.2.2 = root) :
    letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
    (Id.run (do
      for triple in triples do
        let ((i, value), (salt, copath)) := triple
        let r := mc.reconstructRoot i value salt copath
        if r ≠ root then return false
      return true : Id Bool)) = true := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  induction triples with
  | nil => rfl
  | cons t ts ih =>
    -- The loop on `t :: ts` reduces to: run body on `t`; if it returns,
    -- propagate; else continue on `ts`.
    have h_t : mc.reconstructRoot t.1.1 t.1.2 t.2.1 t.2.2 = root :=
      h_per t List.mem_cons_self
    have h_rest : ∀ t' ∈ ts,
        mc.reconstructRoot t'.1.1 t'.1.2 t'.2.1 t'.2.2 = root := by
      intro t' ht'; exact h_per t' (List.mem_cons_of_mem _ ht')
    have ih' := ih h_rest
    -- Body on `t` evaluates to `ForInStep.yield ()` because the guarded
    -- branch's predicate `r ≠ root` is false.
    obtain ⟨⟨i, value⟩, salt, copath⟩ := t
    have h_eq : mc.reconstructRoot i value salt copath = root := h_t
    simp only [List.forIn_cons, Id.run, h_eq, ne_eq, not_true_eq_false,
               if_false] at ih' ⊢
    -- Goal now reduces to the IH on `ts`.
    convert ih' using 1

/-- Universal completeness statement. Specialised to `PerfectBinary` shape
    (the only shape with real bodies at L1; other shapes wired in at L9).

    Precondition shape: the verifier-side `Opening` must be `(indices, msg|I)`
    — i.e., the values it claims at the queried indices match the prover's
    actual `msg`. -/
theorem mt_completeness
    (mc : MerkleCommitment H PerfectBinary)
    (msg : List (MerkleHasher.Symbol H))
    (h_len : msg.length = mc.shape.numLeaves)
    (h_pow2 : ∃ d, mc.shape.numLeaves = 2 ^ d)
    (op : Opening H)
    (h_in_range : ∀ i ∈ op.indices, i < mc.shape.numLeaves)
    (h_lengths : op.indices.length = op.values.length)
    (h_values_match :
      ∀ k (h : k < op.indices.length),
        op.values[k]? = msg[op.indices[k]]?) :
    let result := mc.commit msg
    let proof  := mc.open msg result.snd op.indices
    mc.check result.fst.root op proof = true := by
  letI : DecidableEq (MerkleHasher.Digest H) := MerkleHasher.decEqDigest
  -- Edge case: numLeaves = 0 ⇒ indices = [].
  by_cases h_n_zero : mc.shape.numLeaves = 0
  · -- Indices live in `< 0`, so `op.indices = []`.
    have h_inds_nil : op.indices = [] := by
      cases h_op : op.indices with
      | nil => rfl
      | cons a rest =>
        have ha : a < mc.shape.numLeaves :=
          h_in_range a (by rw [h_op]; exact List.mem_cons_self)
        rw [h_n_zero] at ha
        exact absurd ha (Nat.not_lt_zero _)
    -- Lengths force `values` and proof entries empty as well.
    have h_vals_nil : op.values = [] := by
      have : op.values.length = 0 := by
        rw [← h_lengths, h_inds_nil]; rfl
      exact List.length_eq_zero_iff.mp this
    -- Reduce `check` directly.
    show mc.check (mc.commit msg).fst.root op (mc.open msg (mc.commit msg).snd op.indices) = true
    unfold check «open»
    rw [h_inds_nil, h_vals_nil]
    rfl
  -- Main case: numLeaves > 0.
  · have h_n_pos : mc.shape.numLeaves > 0 := Nat.pos_of_ne_zero h_n_zero
    obtain ⟨d, h_pow_d⟩ := h_pow2
    have h_pow : mc.shape.numLeaves = 2 ^ mc.shape.depth :=
      perfectBinary_numLeaves_eq_pow2_depth mc.shape d h_pow_d
    -- Define `salts` and the root identity.
    let salts : List (MerkleHasher.Salt H) :=
      List.replicate mc.shape.numLeaves
        (MerkleHasher.defaultSalt.default : MerkleHasher.Salt H)
    have h_root := commit_root_eq_labelAt_zero mc msg h_n_pos
    show mc.check (mc.commit msg).fst.root op
        (mc.open msg (mc.commit msg).snd op.indices) = true
    -- Unfold `check`: both early-exit guards are false; pass to the for loop.
    unfold check
    -- The proof entries from `open` have length = indices.length.
    have h_open_len :
        (mc.open msg (mc.commit msg).snd op.indices).entries.length =
        op.indices.length := by
      show (op.indices.map _).length = _
      simp
    -- Both length checks are satisfied.
    simp only [Id.run]
    rw [if_neg (by exact (fun h => absurd h_lengths h))]
    rw [if_neg (by exact (fun h => absurd (h_open_len.symm) h))]
    -- Now we're at the `for` loop. Apply the helper.
    apply check_forIn_eq_true
    -- For each triple in zip, reconstruct equals the root.
    intro t ht
    -- Decompose the triple: it comes from `(indices.zip values).zip entries`.
    -- Find its index k.
    have h_in :
        t ∈ ((op.indices.zip op.values).zip
              (mc.open msg (mc.commit msg).snd op.indices).entries) := ht
    -- Use `List.mem_iff_get` to pull out an index k.
    obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem h_in
    -- Length of the zip is min of lengths = op.indices.length.
    have h_zlen :
        ((op.indices.zip op.values).zip
          (mc.open msg (mc.commit msg).snd op.indices).entries).length
          = op.indices.length := by
      rw [List.length_zip, List.length_zip, h_open_len, ← h_lengths]
      simp
    have hk_lt' : k < op.indices.length := h_zlen ▸ hk_lt
    -- Compute the kth element explicitly.
    have hk_lt_iv : k < (op.indices.zip op.values).length := by
      rw [List.length_zip, ← h_lengths]; simpa using hk_lt'
    have hk_lt_e :
        k < (mc.open msg (mc.commit msg).snd op.indices).entries.length := by
      rw [h_open_len]; exact hk_lt'
    have hk_lt_iv' : k < op.indices.length ∧ k < op.values.length := by
      refine ⟨hk_lt', ?_⟩; rw [← h_lengths]; exact hk_lt'
    have h_get_zip :
        ((op.indices.zip op.values).zip
            (mc.open msg (mc.commit msg).snd op.indices).entries)[k]'hk_lt
          = ((op.indices[k]'hk_lt', op.values[k]'(by rw [← h_lengths]; exact hk_lt')),
              (mc.open msg (mc.commit msg).snd op.indices).entries[k]'hk_lt_e) := by
      rw [List.getElem_zip, List.getElem_zip]
    -- Identify the kth open entry: it's `mkEntry op.indices[k]`.
    have h_open_entry :
        (mc.open msg (mc.commit msg).snd op.indices).entries[k]'hk_lt_e =
          (let defaultS : MerkleHasher.Salt H := MerkleHasher.defaultSalt.default
           let placeholder : MerkleHasher.Digest H :=
             MerkleHasher.hashNodes mc.hasher []
           let i := op.indices[k]'hk_lt'
           let copath := MerkleShape.copath mc.shape i
           let salt := MerkleCommitment.listGetD (mc.commit msg).snd.salts i defaultS
           let digests := copath.map
              (fun v => MerkleCommitment.listGetD (mc.commit msg).snd.labels v.val placeholder)
           (salt, digests)) := by
      show (op.indices.map _)[k]'(by simpa using hk_lt') = _
      rw [List.getElem_map]
    -- The triple `t` decomposes via `hk_eq`.
    rw [← hk_eq, h_get_zip]
    simp only
    rw [h_open_entry]
    simp only
    -- Now the goal is: reconstructRoot ... = root, with the labelled entry.
    -- Prepare hypotheses for `reconstruct_eq_root`.
    have h_i_lt : op.indices[k]'hk_lt' < mc.shape.numLeaves :=
      h_in_range _ (List.getElem_mem hk_lt')
    have h_value_eq :
        msg[op.indices[k]'hk_lt']? = some (op.values[k]'(by rw [← h_lengths]; exact hk_lt')) := by
      have := h_values_match k hk_lt'
      have h_v : op.values[k]? = some (op.values[k]'(by rw [← h_lengths]; exact hk_lt')) :=
        List.getElem?_eq_getElem _
      rw [h_v] at this
      exact this.symm
    have h_rec :=
      reconstruct_eq_root mc msg h_len h_pow h_n_pos
        (op.indices[k]'hk_lt') h_i_lt
        (op.values[k]'(by rw [← h_lengths]; exact hk_lt'))
        h_value_eq
    -- Combine `commit_root_eq_labelAt_zero` and `reconstruct_eq_root`.
    show mc.reconstructRoot _ _ _ _ = (mc.commit msg).fst.root
    rw [h_root]
    exact h_rec
end MerkleCommitment
