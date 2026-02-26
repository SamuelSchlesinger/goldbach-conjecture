import Goldbach.Defs

namespace Goldbach

theorem IsGoldbachPair.symm {n p q : Nat} (h : IsGoldbachPair n p q) :
    IsGoldbachPair n q p := by
  rcases h with ⟨hp, hq, hpq⟩
  exact ⟨hq, hp, by simpa [Nat.add_comm] using hpq⟩

theorem HasGoldbachDecomposition.four_le {n : Nat} (h : HasGoldbachDecomposition n) :
    4 ≤ n := by
  rcases h with ⟨p, q, hpq⟩
  rcases hpq with ⟨hp, hq, hsum⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have h4 : 4 ≤ p + q := by
    calc
      4 = 2 + 2 := by decide
      _ ≤ p + q := Nat.add_le_add hp2 hq2
  simpa [hsum] using h4

theorem hasGoldbachDecomposition_double_of_prime {p : Nat} (hp : Nat.Prime p) :
    HasGoldbachDecomposition (p + p) := by
  exact ⟨p, p, hp, hp, rfl⟩

theorem hasGoldbachDecomposition_four : HasGoldbachDecomposition 4 := by
  refine ⟨2, 2, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_six : HasGoldbachDecomposition 6 := by
  refine ⟨3, 3, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_eight : HasGoldbachDecomposition 8 := by
  refine ⟨3, 5, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_ten : HasGoldbachDecomposition 10 := by
  refine ⟨3, 7, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_twelve : HasGoldbachDecomposition 12 := by
  refine ⟨5, 7, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_fourteen : HasGoldbachDecomposition 14 := by
  refine ⟨3, 11, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_sixteen : HasGoldbachDecomposition 16 := by
  refine ⟨3, 13, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_eighteen : HasGoldbachDecomposition 18 := by
  refine ⟨5, 13, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

theorem hasGoldbachDecomposition_twenty : HasGoldbachDecomposition 20 := by
  refine ⟨3, 17, ?_⟩
  exact ⟨by decide, by decide, by decide⟩

end Goldbach
