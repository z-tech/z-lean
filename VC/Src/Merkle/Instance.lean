import VC.Src.Trait
import VC.Src.Merkle.Scheme

-- Bridge: the abstract `VectorCommitment` trait realized for `MerkleCommitment H S`.
-- Mirrors ark-mt/src/vc.rs.
--
-- Mapping notes:
--   * Merkle has no trusted-setup ceremony, so `UniversalParams`,
--     `CommitterKey`, and `VerifierKey` all carry the `MerkleCommitment H S`
--     itself. `setup` therefore needs to manufacture one from nothing — we
--     use `Classical.ofNonempty` and let downstream callers supply a
--     `Nonempty (MerkleCommitment H S)` witness (trivially provided whenever
--     `H` and `S` are `Nonempty`).
--   * `trim` is a no-op clone; the `len`/`queries` knobs don't shape Merkle.
--   * `commit`/`open`/`check` delegate straight to `MerkleCommitment.*`.
--   * `open` discards the typeclass-supplied `values` argument: the prover
--     already has the whole message in the `Trapdoor`.
--   * `check` rebuilds the `Opening` record from `(indices, values)`.

noncomputable instance {H S : Type} [MerkleHasher H] [MerkleShape S]
    [Nonempty (MerkleCommitment H S)] :
    VectorCommitment (MerkleCommitment H S) where
  Alphabet         := MerkleHasher.Symbol H
  Index            := Nat
  UniversalParams  := MerkleCommitment H S
  CommitterKey     := MerkleCommitment H S
  VerifierKey      := MerkleCommitment H S
  Commitment       := Committed H S
  CommitmentState  := Trapdoor H S
  Proof            := OpeningProof H
  setup _ _ _      := Classical.ofNonempty
  trim mc _ _      := (mc, mc)
  commit ck msg    := ck.commit msg
  «open» ck _ _ indices _ td := ck.open [] td indices
  check vk commitment indices values proof :=
    vk.check commitment.root { indices := indices, values := values } proof
