import Goldbach.Defs

namespace Goldbach

/--
**Strong Goldbach conjecture**:
every even natural number `n >= 4` is a sum of two prime numbers.
-/
theorem strong_goldbach_conjecture :
    ∀ n : Nat, 4 ≤ n → Even n → HasGoldbachDecomposition n := by
  intro n hn4 hEven
  sorry

/-- Equivalent doubled-index form of Strong Goldbach. -/
theorem strong_goldbach_conjecture_double :
    ∀ k : Nat, 2 ≤ k → HasGoldbachDecomposition (k + k) := by
  intro k hk2
  apply strong_goldbach_conjecture (k + k)
  · have h2 : 2 + 2 ≤ k + k := Nat.add_le_add hk2 hk2
    simpa using h2
  · exact ⟨k, rfl⟩

end Goldbach
