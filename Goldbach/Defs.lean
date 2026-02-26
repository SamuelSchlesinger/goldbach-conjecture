import Mathlib.Data.Nat.Prime.Basic

namespace Goldbach

/-- A pair of primes `(p, q)` is a Goldbach decomposition of `n` when `p + q = n`. -/
def IsGoldbachPair (n p q : Nat) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- `n` satisfies the strong Goldbach property when it has a prime-sum decomposition. -/
def HasGoldbachDecomposition (n : Nat) : Prop :=
  ∃ p q : Nat, IsGoldbachPair n p q

end Goldbach
