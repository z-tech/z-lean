-- Marker / placeholder typeclasses for VectorCommitment data structures.
-- Mirrors ark-vc/src/data_structures.rs.

class Alphabet (A : Type) where

class UniversalParams (P : Type) where

class CommitterKey (K : Type) where

class VerifierKey (K : Type) where

class Commitment (C : Type) where

class HidingCommitment (C : Type) extends Commitment C where

class CommitmentState (S : Type) where

structure LabeledCommitment (C : Type) where
  label : String
  commitment : C
