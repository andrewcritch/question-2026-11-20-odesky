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

open MeasureTheory ProbabilityTheory Finset Complex

namespace Odesky

theorem const_profile {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) (σ τ : Equiv.Perm (Fin n)) :
    profA (fun _ : Fin n => c) (fun _ : Fin n => c) = 1 / 2 ∧
      profB (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 1 / 2 ∧
      profC (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 0 ∧
      profD (fun _ : Fin n => c) (fun _ : Fin n => c) σ τ = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hN : normSq (fun _ : Fin n => c) (fun _ : Fin n => c) = n * (c + c) ^ 2 := by
    simp [normSq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [profA, hN, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  · simp only [profB, hN, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  · simp [profC]
  · simp [profD]

private lemma charFunDual_gaussianReal_real (m : ℝ) (v : NNReal) (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal m v) L = cexp ((L 1) * m * I - v * (L 1) ^ 2 / 2) := by
  have hL : L = (L 1) • ContinuousLinearMap.id ℝ ℝ := by
    ext; simp
  conv_lhs => rw [hL, ← charFun_map_eq_charFunDual_smul, ContinuousLinearMap.coe_id', Measure.map_id]
  rw [charFun_gaussianReal]

theorem correlated_gaussian_law (r : ℝ) (hr : |r| < 1) (v₁ v₂ : NNReal)
    (hv₁ : (v₁ : ℝ) = 2 * (1 + r)) (hv₂ : (v₂ : ℝ) = 2 * (1 - r)) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => (p.1 + (r * p.1 + Real.sqrt (1 - r ^ 2) * p.2),
          (r * p.1 + Real.sqrt (1 - r ^ 2) * p.2) - p.1)) =
      (gaussianReal 0 v₁).prod (gaussianReal 0 v₂) := by
  set s := Real.sqrt (1 - r ^ 2) with hs
  have hs2 : s ^ 2 = 1 - r ^ 2 := by
    rw [hs, Real.sq_sqrt]
    have := abs_lt.mp hr
    nlinarith
  let A : ℝ × ℝ →L[ℝ] ℝ := ((1 + r) • ContinuousLinearMap.fst ℝ ℝ ℝ) + s • ContinuousLinearMap.snd ℝ ℝ ℝ
  let B : ℝ × ℝ →L[ℝ] ℝ := ((r - 1) • ContinuousLinearMap.fst ℝ ℝ ℝ) + s • ContinuousLinearMap.snd ℝ ℝ ℝ
  let T : ℝ × ℝ →L[ℝ] ℝ × ℝ := A.prod B
  have hT : (fun p : ℝ × ℝ => (p.1 + (r * p.1 + s * p.2), (r * p.1 + s * p.2) - p.1)) = ⇑T := by
    funext p
    simp [T, A, B]
    constructor <;> ring
  rw [hT]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod]
  simp only [charFunDual_gaussianReal_real]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hL : ∀ x y : ℝ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
    intro x y
    have : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp [T, A, B, hv₁, hv₂]
  rw [hL (1 + r) (r - 1), hL s s]
  push_cast
  have hs2' : ((s : ℂ)) ^ 2 = 1 - (r : ℂ) ^ 2 := by exact_mod_cast hs2
  linear_combination (-(↑(L (1, 0)) + ↑(L (0, 1)) : ℂ) ^ 2 / 2) * hs2'

end Odesky
