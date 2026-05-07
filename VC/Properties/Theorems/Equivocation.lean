import VC.Src.Merkle.Scheme

-- §12.7 equivocation lemma.

theorem mt_equivocation
    {H S : Type} [MerkleHasher H] [MerkleShape S]
    (mc : MerkleCommitment H S) :
    True := sorry
