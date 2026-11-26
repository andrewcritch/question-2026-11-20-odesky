# Lean role prompt: prove the theorems in OdeskyLean/TheoremBFull.lean

Hi! Thanks for helping. Other delegate agents prove other files of this Lean project in parallel. Work by yourself; do not wait for them or coordinate with them.

Your working directory is a Lean 4 project (Lean v4.28.0, Mathlib v4.28.0, prebuilt). The Lean tools are at `/Users/andrew/.elan/bin/`; run `/Users/andrew/.elan/bin/lake env lean OdeskyLean/TheoremBFull.lean` to check your file. The file states part of a theorem about the symmetric and antisymmetric parts of a sum of rank-one bilinear forms; its docstrings say what each statement means.

Notes:
- Other files of the project may still contain `sorry`. You may use any theorem imported by your file, whether it is proved yet or not.
- The module docstring of the file gives the proof route. Use `exists_orthonormal_near`, `formL_perturb`, `formLt_perturb`, `formL_bound`, `weyl_abs`, `lists_at_limit`, `gprof_at_limit`, `gram_slln`, `gaussian_prod_integrable`, `gaussian_second_moment`. You may use theorems of imported files whether or not they are proved yet. This file is the largest; split it into private lemmas.

You have **60 minutes**.

Prove every theorem in `OdeskyLean/TheoremBFull.lean` without changing any theorem statement, definition, or hypothesis. You may add private lemmas to that file. Edit no other file. Check your work with `lake env lean OdeskyLean/TheoremBFull.lean`; do not run `lake build`. A file with a remaining `sorry`, or with a changed statement, is not a result. Where a statement looks false or unprovable as written, stop and say why, with the smallest counterexample or obstruction you can find: a clear negative report has value; an overstated positive report has none. Write your report to `./answer_TheoremBFull.md`, and lead with a one-line verdict.
