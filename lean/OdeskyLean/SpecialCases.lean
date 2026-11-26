import OdeskyLean.Profile
import Mathlib

/-!
# Special cases of the ensemble

* `const_profile`: for constant `f = g = c`, the profile of `L_∞` is the midpoint
  `(½, ½, 0, 0)` of `Θ`.
* `correlated_gaussian_law`: the question's correlated Gaussian model is the case
  of constant `f, g`. For independent standard Gaussians `X, Y` and `|r| < 1`, let
  `K := rX + √(1-r²)Y`. Then `(X + K, K - X)` has the law of two independent
  centered Gaussians with variances `2(1+r)` and `2(1-r)`, i.e., the law of
  `(2√f P, 2√g M)` entrywise with `f = (1+r)/2`, `g = (1-r)/2`, so `f/g = (1+r)/(1-r)`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Odesky

theorem const_profile {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) (σ τ : Equiv.Perm (Fin n)) :
    profA (fun _ : Fin n => c) (fun _ : Fin n => c) = 1 / 2 ∧
      profB (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 1 / 2 ∧
      profC (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 0 ∧
      profD (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 0 := by
  sorry

theorem correlated_gaussian_law (r : ℝ) (hr : |r| < 1) (v₁ v₂ : NNReal)
    (hv₁ : (v₁ : ℝ) = 2 * (1 + r)) (hv₂ : (v₂ : ℝ) = 2 * (1 - r)) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => (p.1 + (r * p.1 + Real.sqrt (1 - r ^ 2) * p.2),
          (r * p.1 + Real.sqrt (1 - r ^ 2) * p.2) - p.1)) =
      (gaussianReal 0 v₁).prod (gaussianReal 0 v₂) := by
  sorry

end Odesky
