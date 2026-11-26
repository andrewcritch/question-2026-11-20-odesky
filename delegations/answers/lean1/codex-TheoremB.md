PASS: Both theorems in `OdeskyLean/TheoremB.lean` are proved, with no remaining `sorry`.

`gram_limit` applies `gram_slln` with Gaussian integrability and second moments, then expands products of the linear combinations defining `qcol` and `kcol`. A private lemma handles this expansion and its limit.

`blocks_of_limit_gram` constructs blocks with `s_i = fv_i + gv_i`, `u_i = k_i / √s_i`, and `v_i = q_i / √s_i`. The Gram hypotheses give unit vectors and orthogonality between distinct blocks. The tilt is `(fv_i - gv_i) / (fv_i + gv_i)`, which gives the strict tilt bound and the required values of `α` and `β`.

All existing theorem statements, definitions, and hypotheses are unchanged. No other Lean file was edited.

Validation: `/Users/andrew/.elan/bin/lake env lean OdeskyLean/TheoremB.lean` completed with exit code 0 and no warnings or errors. No `lake build` was run.
