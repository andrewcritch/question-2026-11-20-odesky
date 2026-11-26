# Lean role prompt: prove the theorems in OdeskyLean/Spectral.lean

Hi! Thanks for helping. Other delegate agents prove other files of this Lean project in parallel. Work by yourself; do not wait for them or coordinate with them.

Your working directory is a Lean 4 project (Lean v4.28.0, Mathlib v4.28.0, prebuilt). The Lean tools are at `/Users/andrew/.elan/bin/`; run `/Users/andrew/.elan/bin/lake env lean OdeskyLean/Spectral.lean` to check your file. The file states part of a theorem about the symmetric and antisymmetric parts of a sum of rank-one bilinear forms; its docstrings say what each statement means.

Notes:
- Other files of the project may still contain `sorry`. You may use any theorem imported by your file, whether it is proved yet or not.
- Useful Mathlib: `LinearMap.charpoly`, `LinearMap.charpoly_toMatrix`, `Orthonormal.exists_orthonormalBasis_extension`, `OrthonormalBasis.sum_inner_mul_inner`, `Polynomial.roots_prod`, `Polynomial.roots_X_sub_C`. The lemmas `S_add`, `S_sub`, `T_add`, `T_sub`, `S_perp`, `T_perp`, `inner_add_sub` in `OdeskyLean/Geometry.lean` are proved and give the eigenvector equations.

You have **60 minutes**.

Prove every theorem in `OdeskyLean/Spectral.lean` without changing any theorem statement, definition, or hypothesis. You may add private lemmas to that file. Edit no other file. Check your work with `lake env lean OdeskyLean/Spectral.lean`; do not run `lake build`. A file with a remaining `sorry`, or with a changed statement, is not a result. Where a statement looks false or unprovable as written, stop and say why, with the smallest counterexample or obstruction you can find: a clear negative report has value; an overstated positive report has none. Write your report to `./answer_Spectral.md`, and lead with a one-line verdict.
