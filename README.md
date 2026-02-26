# Strong Goldbach Conjecture

A Lean 4 formalization scaffold for the strong Goldbach conjecture.

## The Conjecture

Every even integer `n >= 4` can be written as a sum of two primes.

In Lean:

`forall n : Nat, 4 <= n -> Even n -> HasGoldbachDecomposition n`.

## Structure

| Module | Contents | Sorry count |
|--------|----------|-------------|
| `Goldbach.Defs` | Core predicates: `IsGoldbachPair`, `HasGoldbachDecomposition` | 0 |
| `Goldbach.Basic` | Symmetry/lower-bound lemmas, infinite prime-doubling family, explicit decompositions for `4..20` | 0 |
| `Goldbach.SmallCases` | Finite-range theorem for even `n` with `4 <= n <= 20` | 0 |
| `Goldbach.Conjecture` | Main open statement and doubled-index equivalent form | 1 |

## Building

```sh
lake update && lake build
```
