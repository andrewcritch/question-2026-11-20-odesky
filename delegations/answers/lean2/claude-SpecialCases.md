VERDICT: PROVED. Both theorems in OdeskyLean/SpecialCases.lean have proofs with no sorry. `lake env lean OdeskyLean/SpecialCases.lean` gives no errors and no warnings.

## Changes
- File: `lean/OdeskyLean/SpecialCases.lean` only. The theorem statements, definitions, and hypotheses did not change. The diff removes only the two `sorry` lines, and it adds `Complex` to the `open` line.
- Added a private lemma, `charFunDual_gaussianReal_real`: for `L : StrongDual ℝ ℝ`, `charFunDual (gaussianReal m v) L = exp(L 1 * m * I - v * (L 1)^2 / 2)`.

## Proofs
- `const_profile`: `normSq = n * (c+c)^2`. So `profA = profB = 2 n c^2 / (4 n c^2) = 1/2`. `profC` and `profD` are 0, because `max (c - c) 0 = 0`. `field_simp` gets the nonzero denominators from `hc` and from `n ≠ 0`, which is in the context.
- `correlated_gaussian_law`: the map is a continuous linear map `T = A.prod B`. The proof uses `Measure.ext_of_charFunDual`, then `charFunDual_map`, then `charFunDual_prod` on each side, then `charFun_gaussianReal`. It writes `L (x, y) = x L(1,0) + y L(0,1)`. The remaining exponent identity is `(a(1+r) + b(r-1))^2 + (a+b)^2 s^2 = 2(1+r)a^2 + 2(1-r)b^2` with `s^2 = 1 - r^2`, and `linear_combination` closes it. The hypothesis `|r| < 1` gives `s^2 = 1 - r^2`.
