VERDICT: PROVED. All three theorems in `OdeskyLean/TheoremAExtra.lean` are proved. No `sorry` remains, and no statement changed.

## Check

- Command: `cd lean && lake env lean OdeskyLean/TheoremAExtra.lean`. Result: no errors, no warnings.
- `#print axioms` for each of the three theorems gives only `[propext, Classical.choice, Quot.sound]`.
- Edits are in `lean/OdeskyLean/TheoremAExtra.lean` only. The theorem statements are the same. The only line outside a proof that changed is `open Finset` -> `open Finset RealInnerProductSpace`, which the `⟪·,·⟫` notation needs.

## Added private lemmas

- `lists_sorted'`: a copy of the private `lists_sorted` in `Main.lean`. It says `lp = α ∘ σ` and `lm = β ∘ τ`.
- `nL_eq'`: `nL b = normSq α β`. It is not used, but it is harmless.
- `nL_pos`: `0 < nL b` when `n ≥ 1`. It follows from `frob_L` and `s_i > 0`.

## Proofs

- `main_d_eq_zero_iff`, `main_c_eq_zero_iff`: replace `lp, lm` with the sorted `α, β`. Then `pd = 0` holds iff its numerator is 0, because `nL > 0`. `d_num_eq_zero_iff` / `c_num_eq_zero_iff` (in `Rearrangement.lean`) then give `β_i ≤ α_i` (resp. `α_i ≤ β_i`). These are the same as `t_i ≥ 0` (resp. `t_i ≤ 0`), because `α_i - β_i = s_i t_i` with `s_i > 0`.
- `theta_attained`: the construction uses `n = 1`, `N = 2`, `s = 1`, `u = (1,0)`, `v = (t, √(1-t²))`, and `t = √c - √d`. From `cd = 0` we get `t² = c + d = 1 - 2a < 1`, because `a > 0`. The spectral lists are `lp = α`, `lm = β`, `sv = √(αβ)`. These lists are trivially antitone on `Fin 1`, and their root conditions come from `roots_S_pos`, `roots_S_neg` and `roots_neg_T_sq_pos`. Since `‖L‖² = 1`, we get `pa = pb = 2αβ = (1 - t²)/2 = a`, `pc = max(t,0)² = c` and `pd = max(-t,0)² = d`. The last two use a case split on `c = 0` or `d = 0`.

## Caveats

None. The statements look correct as written.
