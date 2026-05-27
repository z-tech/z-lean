import VectorCommitment.Src.Merkle.Scheme

-- §20 path-pruning lemmas.

/-- §20 lemma:path-pruning-is-copaths-minus-paths.
    The derived vertex set equals the union of copaths minus the union of
    paths over `indices`. With our filter-based implementation this is
    definitional. -/
theorem path_pruning_is_copaths_minus_paths
    {H S : Type} [MerkleHasher H] [MerkleShape S]
    (mc : MerkleCommitment H S) (indices : List Nat) :
    mc.deriveVertexSet indices =
      (indices.flatMap (fun i => MerkleShape.copath mc.shape i)).filter
        (fun v => decide
          (v ∉ indices.flatMap (fun i => MerkleShape.path mc.shape i))) := by
  rfl

/-- §20 opening-proof size bound. The pruned vertex set is no larger than the
    union of copaths, since `deriveVertexSet I = copath(I) \ path(I)` is just
    `copath(I)` filtered by membership in `path(I)`. -/
theorem opening_proof_size_bound
    {H S : Type} [MerkleHasher H] [MerkleShape S]
    (mc : MerkleCommitment H S) (indices : List Nat) :
    (mc.deriveVertexSet indices).length ≤
      (indices.flatMap (fun i => MerkleShape.copath mc.shape i)).length := by
  rw [path_pruning_is_copaths_minus_paths]
  exact List.length_filter_le _ _
