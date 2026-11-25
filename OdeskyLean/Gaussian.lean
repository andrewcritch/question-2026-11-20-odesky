import Mathlib

/-!
# Layer 6 (gap G3): Gaussian moments for the stacked columns

A random vector with independent standard Gaussian coordinates satisfies the
hypotheses `hint` and `hmom` of `Odesky.gram_slln`: every product of two
coordinates is integrable, and `E[Z_a Z_b] = 1` if `a = b`, else `0`.
-/

open MeasureTheory ProbabilityTheory

namespace Odesky

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem gaussian_prod_integrable [IsProbabilityMeasure μ] {m : ℕ} (Z : Ω → (Fin m → ℝ))
    (hmeas : Measurable Z)
    (hind : iIndepFun (fun a ω => Z ω a) μ)
    (hgauss : ∀ a, μ.map (fun ω => Z ω a) = gaussianReal 0 1) :
    ∀ a b, Integrable (fun ω => Z ω a * Z ω b) μ := by
  sorry

theorem gaussian_second_moment [IsProbabilityMeasure μ] {m : ℕ} (Z : Ω → (Fin m → ℝ))
    (hmeas : Measurable Z)
    (hind : iIndepFun (fun a ω => Z ω a) μ)
    (hgauss : ∀ a, μ.map (fun ω => Z ω a) = gaussianReal 0 1) :
    ∀ a b, ∫ ω, Z ω a * Z ω b ∂μ = if a = b then 1 else 0 := by
  sorry

end Odesky
