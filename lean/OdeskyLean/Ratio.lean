import Mathlib

/-!
# The fixed-ratio comparison in the caveats

For `κ ≥ 1` and constants `f, g > 0`, let `x := (f-g)²/(f+g)²`, the iterated-limit
value of `1 - 2a`. The numerically observed fixed-ratio value is
`y := (1 + 1/κ)(f-g)² / ((f+g)² + (f-g)²/κ)`. Then `y = x (1 + 1/κ)/(1 + x/κ)`, and
`x ≤ y ≤ x (1 + 1/κ)`: the relative difference is at most `1/κ`.
-/

namespace Odesky

theorem fixed_ratio_bound (κ f g : ℝ) (hκ : 1 ≤ κ) (hf : 0 < f) (hg : 0 < g) :
    let x := (f - g) ^ 2 / (f + g) ^ 2
    let y := (1 + 1 / κ) * (f - g) ^ 2 / ((f + g) ^ 2 + (f - g) ^ 2 / κ)
    x ≤ y ∧ y ≤ x * (1 + 1 / κ) := by
  intro x y
  have hκ0 : 0 < κ := by linarith
  have hs : 0 < (f + g) ^ 2 := by positivity
  have hd : 0 ≤ (f - g) ^ 2 := sq_nonneg _
  have hle : (f - g) ^ 2 ≤ (f + g) ^ 2 := by nlinarith
  have hden : 0 < (f + g) ^ 2 + (f - g) ^ 2 / κ := by positivity
  constructor
  · simp only [x, y]
    rw [div_le_div_iff₀ hs hden]
    have : (f - g) ^ 2 * ((f + g) ^ 2 + (f - g) ^ 2 / κ) ≤
        (1 + 1 / κ) * (f - g) ^ 2 * (f + g) ^ 2 := by
      have h1 : (f - g) ^ 2 * ((f - g) ^ 2 / κ) ≤ (f - g) ^ 2 * ((f + g) ^ 2 / κ) := by
        apply mul_le_mul_of_nonneg_left _ hd
        exact div_le_div_of_nonneg_right hle hκ0.le
      have e1 : (f - g) ^ 2 * ((f + g) ^ 2 + (f - g) ^ 2 / κ) =
          (f - g) ^ 2 * (f + g) ^ 2 + (f - g) ^ 2 * ((f - g) ^ 2 / κ) := by ring
      have e2 : (1 + 1 / κ) * (f - g) ^ 2 * (f + g) ^ 2 =
          (f - g) ^ 2 * (f + g) ^ 2 + (f - g) ^ 2 * ((f + g) ^ 2 / κ) := by ring
      linarith [h1, e1, e2]
    linarith
  · simp only [x, y]
    rw [div_le_iff₀ hden]
    have h2 : 0 ≤ (f - g) ^ 2 / (f + g) ^ 2 * (1 + 1 / κ) * ((f - g) ^ 2 / κ) := by positivity
    have h3 : (f - g) ^ 2 / (f + g) ^ 2 * (1 + 1 / κ) * (f + g) ^ 2 =
        (1 + 1 / κ) * (f - g) ^ 2 := by field_simp
    nlinarith [h2, h3]

end Odesky
