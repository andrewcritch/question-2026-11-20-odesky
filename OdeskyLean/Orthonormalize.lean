import Mathlib

/-!
# Layer 8 (gap G2): a nearby orthonormal family

If the Gram matrix of `x_1, …, x_m` is within `δ < 1` of the identity as a
quadratic form, then there is an orthonormal family `e` with
`‖∑ c_a (x_a - e_a)‖ ≤ δ |c|` for every coefficient vector `c`.

Proof idea: `e := G^{-1/2} x` (symmetric square root of the Gram matrix `G`);
then `∑ c_a (x_a - e_a) = ∑_b ((G^{1/2} - I) c)_b e_b`, and every eigenvalue `γ`
of `G` has `|√γ - 1| ≤ |γ - 1| ≤ δ`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {N m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_orthonormal_near (x : Fin m → V) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hG : ∀ c : Fin m → ℝ,
      |∑ a, ∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)| ≤ δ * ∑ a, c a ^ 2) :
    ∃ e : Fin m → V, Orthonormal ℝ e ∧
      ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2) := by
  sorry

end Odesky
