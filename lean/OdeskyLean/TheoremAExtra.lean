import OdeskyLean.Main

/-!
# Theorem 1, remaining items, for the operator

* `main_d_eq_zero_iff`, `main_c_eq_zero_iff`: Theorem 1(3), second part, as a
  statement about the operator `L`: if the blocks are similarly ordered, then
  `d = 0` iff every tilt is `≥ 0`, and `c = 0` iff every tilt is `≤ 0`.
* `theta_attained`: Theorem 1(5): every point `(a, a, c, d)` of `Θ` with `a > 0`
  (i.e., every point of `Θ` other than `(0,0,1,0)` and `(0,0,0,1)`) is the profile
  of a form in normal form, here with one block in `ℝ²`.
-/

open Finset

namespace Odesky

namespace OrthoBlocks

variable {n N : ℕ} (B : OrthoBlocks n N)
variable (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))

/-- Theorem 1(3): `d = 0` iff every tilt is `≥ 0`. -/
theorem main_d_eq_zero_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pd b lp lm = 0 ↔ ∀ i, 0 ≤ B.t i := by
  sorry

/-- Theorem 1(3): `c = 0` iff every tilt is `≤ 0`. -/
theorem main_c_eq_zero_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pc b lp lm = 0 ↔ ∀ i, B.t i ≤ 0 := by
  sorry

end OrthoBlocks

/-- Theorem 1(5): every point of `Θ` other than its two endpoints is the profile
of a form in normal form. The point is `(a, a, c, d)` with `a > 0`,
`c, d ≥ 0`, `c d = 0` and `2a + c + d = 1`. -/
theorem theta_attained (a c d : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c * d = 0) (hsum : 2 * a + c + d = 1) :
    ∃ B : OrthoBlocks 1 2, (∀ i, |B.t i| < 1) ∧
      SimilarlyOrdered B.α B.β ∧ ((∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0)) ∧
      ∃ lp lm sv : Fin 1 → ℝ, B.SpectralLists lp lm sv ∧
        ∀ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
          B.pa b = a ∧ B.pb b lp lm = a ∧ B.pc b lp lm = c ∧ B.pd b lp lm = d := by
  sorry

end Odesky
