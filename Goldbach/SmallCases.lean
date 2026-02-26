import Goldbach.Basic
import Mathlib.Tactic.IntervalCases

namespace Goldbach

theorem hasGoldbachDecomposition_double_two_to_ten {k : Nat} (hk2 : 2 ≤ k) (hk10 : k ≤ 10) :
    HasGoldbachDecomposition (k + k) := by
  interval_cases k
  · simpa using hasGoldbachDecomposition_four
  · simpa using hasGoldbachDecomposition_six
  · simpa using hasGoldbachDecomposition_eight
  · simpa using hasGoldbachDecomposition_ten
  · simpa using hasGoldbachDecomposition_twelve
  · simpa using hasGoldbachDecomposition_fourteen
  · simpa using hasGoldbachDecomposition_sixteen
  · simpa using hasGoldbachDecomposition_eighteen
  · simpa using hasGoldbachDecomposition_twenty

theorem hasGoldbachDecomposition_even_four_to_twenty {n : Nat}
    (hn4 : 4 ≤ n) (hn20 : n ≤ 20) (hEven : Even n) :
    HasGoldbachDecomposition n := by
  interval_cases n
  · exact hasGoldbachDecomposition_four
  · exact False.elim ((by decide : ¬ Even 5) hEven)
  · exact hasGoldbachDecomposition_six
  · exact False.elim ((by decide : ¬ Even 7) hEven)
  · exact hasGoldbachDecomposition_eight
  · exact False.elim ((by decide : ¬ Even 9) hEven)
  · exact hasGoldbachDecomposition_ten
  · exact False.elim ((by decide : ¬ Even 11) hEven)
  · exact hasGoldbachDecomposition_twelve
  · exact False.elim ((by decide : ¬ Even 13) hEven)
  · exact hasGoldbachDecomposition_fourteen
  · exact False.elim ((by decide : ¬ Even 15) hEven)
  · exact hasGoldbachDecomposition_sixteen
  · exact False.elim ((by decide : ¬ Even 17) hEven)
  · exact hasGoldbachDecomposition_eighteen
  · exact False.elim ((by decide : ¬ Even 19) hEven)
  · exact hasGoldbachDecomposition_twenty

end Goldbach
