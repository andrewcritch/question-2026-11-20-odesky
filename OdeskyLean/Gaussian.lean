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
  have hLp : ∀ a, MemLp (fun ω => Z ω a) 2 μ := by
    intro a
    have h := memLp_id_gaussianReal (μ := 0) (v := 1) 2
    rw [← hgauss a] at h
    exact h.comp_of_map ((measurable_pi_apply a).comp hmeas).aemeasurable
  intro a b
  exact (hLp a).integrable_mul (hLp b)

theorem gaussian_second_moment [IsProbabilityMeasure μ] {m : ℕ} (Z : Ω → (Fin m → ℝ))
    (hmeas : Measurable Z)
    (hind : iIndepFun (fun a ω => Z ω a) μ)
    (hgauss : ∀ a, μ.map (fun ω => Z ω a) = gaussianReal 0 1) :
    ∀ a b, ∫ ω, Z ω a * Z ω b ∂μ = if a = b then 1 else 0 := by
  have hcoord : ∀ a, Measurable (fun ω => Z ω a) :=
    fun a => (measurable_pi_apply a).comp hmeas
  have hmean : ∀ a, ∫ ω, Z ω a ∂μ = 0 := by
    intro a
    have h := integral_map (μ := μ) (hcoord a).aemeasurable
      (f := fun x : ℝ => x) (by fun_prop)
    rw [hgauss a] at h
    simpa using h.symm
  intro a b
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable] at h
    simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at h
    have hmap := integral_map (μ := μ) (hcoord a).aemeasurable
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [hgauss a] at hmap
    simpa only [pow_two] using hmap.symm.trans h
  · rw [if_neg hab]
    calc
      (∫ ω, Z ω a * Z ω b ∂μ) =
          (∫ ω, Z ω a ∂μ) * (∫ ω, Z ω b ∂μ) :=
        (hind.indepFun hab).integral_fun_mul_eq_mul_integral
          (hcoord a).aestronglyMeasurable (hcoord b).aestronglyMeasurable
      _ = 0 := by rw [hmean a, zero_mul]

end Odesky
