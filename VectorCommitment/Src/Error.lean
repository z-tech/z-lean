-- Mirrors ark-mt/src/error.rs.

inductive OpeningError
  | LengthMismatch (indices values : Nat)
  | DuplicateIndex (index : Nat)
  | NotSorted (at_ : Nat)
  | IndexOutOfRange (index bound : Nat)
  deriving Repr

inductive CheckError
  | MalformedProof
  | LengthMismatch (expected got : Nat)
  deriving Repr
