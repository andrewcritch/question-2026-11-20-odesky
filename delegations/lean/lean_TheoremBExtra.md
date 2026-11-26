# Lean role prompt: prove the theorems in OdeskyLean/TheoremBExtra.lean

Hi! Thanks for helping. Other delegate agents prove other files of this Lean project in parallel. Work by yourself; do not wait for them or coordinate with them.

Your working directory is a Lean 4 project (Lean v4.28.0, Mathlib v4.28.0, prebuilt). The Lean tools are at `/Users/andrew/.elan/bin/`; run `/Users/andrew/.elan/bin/lake env lean OdeskyLean/TheoremBExtra.lean` to check your file. The file states part of a theorem about the symmetric and antisymmetric parts of a sum of rank-one bilinear forms; its docstrings say what each statement means.

Notes:
- Other files of the project may still contain `sorry`. You may use any theorem imported by your file, whether it is proved yet or not.
- The module docstring of the file gives the proof idea. All other files of the project are fully proved; use their theorems (`Main.lean`, `Profile.lean`, `Rearrangement.lean`, `Spectral.lean`, `Weyl.lean`, `GenProfile.lean`, `Probability.lean`, `Limit.lean`). Mathlib names worth searching: `LinearMap.IsSymmetric.eigenvalues`, `eigenvalues_antitone`, `eigenvectorBasis`, `Submodule.finrank_sup_add_finrank_inf_eq`, `LinearIsometryEquiv`, `LinearIsometry.extend`, `Matrix.charpoly_mul_comm_of_le`, `Matrix.det_fromBlocks`, `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.HasGaussianLaw`, `Measure.ext_of_charFun`, `charFun_gaussianReal`, `ProbabilityTheory.strong_law_ae_real`, `ratio_slln` (`Probability.lean`).

You have **75 minutes**.

Prove every theorem in `OdeskyLean/TheoremBExtra.lean` without changing any theorem statement, definition, or hypothesis. You may add private lemmas to that file. Edit no other file. Check your work with `lake env lean OdeskyLean/TheoremBExtra.lean`; do not run `lake build`. A file with a remaining `sorry`, or with a changed statement, is not a result. Where a statement looks false or unprovable as written, stop and say why, with the smallest counterexample or obstruction you can find: a clear negative report has value; an overstated positive report has none. Write your report to `./answer_TheoremBExtra.md`, and lead with a one-line verdict.
