import OdeskyLean.GenProfile

/-!
# Layer 10 (gap G2): perturbing the rows perturbs the form

Rows `q_i = ∑_a AQ_{ia} x_a`, `k_i = ∑_a AK_{ia} x_a` are fixed combinations of
vectors `x_a`. Replacing `x` by an orthonormal family `e` with
`‖∑ c_a (x_a - e_a)‖ ≤ δ |c|` moves `L` and `Lᵀ` by at most
`δ (2 + δ) κ` in operator norm, with `κ = ∑_i |AQ_i| |AK_i|`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Row `i` is `∑_a A_{ia} x_a`. -/
noncomputable def comb (A : Fin n → Fin m → ℝ) (x : Fin m → V) (i : Fin n) : V :=
  ∑ a, A i a • x a

/-- `κ = ∑_i |AQ_i| |AK_i|`, with Euclidean norms of the coefficient rows. -/
noncomputable def kappa (AQ AK : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, Real.sqrt (∑ a, AQ i a ^ 2) * Real.sqrt (∑ a, AK i a ^ 2)

theorem formL_perturb (AQ AK : Fin n → Fin m → ℝ) (x e : Fin m → V) (he : Orthonormal ℝ e)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hxe : ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2)) (y : V) :
    ‖formL (comb AQ x) (comb AK x) y - formL (comb AQ e) (comb AK e) y‖ ≤
      δ * (2 + δ) * kappa AQ AK * ‖y‖ := by
  sorry

theorem formLt_perturb (AQ AK : Fin n → Fin m → ℝ) (x e : Fin m → V) (he : Orthonormal ℝ e)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hxe : ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2)) (y : V) :
    ‖formLt (comb AQ x) (comb AK x) y - formLt (comb AQ e) (comb AK e) y‖ ≤
      δ * (2 + δ) * kappa AQ AK * ‖y‖ := by
  sorry

/-- For an orthonormal family, `‖L y‖ ≤ κ ‖y‖` and `‖Lᵀ y‖ ≤ κ ‖y‖`. -/
theorem formL_bound (AQ AK : Fin n → Fin m → ℝ) (e : Fin m → V) (he : Orthonormal ℝ e) (y : V) :
    ‖formL (comb AQ e) (comb AK e) y‖ ≤ kappa AQ AK * ‖y‖ ∧
      ‖formLt (comb AQ e) (comb AK e) y‖ ≤ kappa AQ AK * ‖y‖ := by
  sorry

end Odesky
