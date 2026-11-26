import OdeskyLean.Profile
import OdeskyLean.LogDet
import OdeskyLean.Congruence

/-!
# Small identities used in the prose of the answer

* `weighted_tilt`: with `t = (f-g)/(f+g)` and `f + g > 0`,
  `(f+g)² t|t| = (f-g)|f-g|` (the "weighted mean of `t|t|`" reading of Theorem 2).
* `logratio_sum_zero`: for linearly independent stacked rows, the log-ratios
  `r_j = log σ(T)_j - ½ log(λ₊,j λ₋,j)` sum to zero.
* `eq_zero_of_sum_zero_of_const`: if such numbers sum to zero and are all equal,
  they are all zero (relation (1) can fail only through their spread).
* `const_one_sub_two_a`: for constant `f, g > 0`, the limit form has
  `1 - 2a = (f-g)²/(f+g)²`.
-/

open Finset RealInnerProductSpace

namespace Odesky

theorem weighted_tilt (f g : ℝ) (h : 0 < f + g) :
    (f + g) ^ 2 * ((f - g) / (f + g) * |(f - g) / (f + g)|) = (f - g) * |f - g| := by
  rw [abs_div, abs_of_pos h]
  field_simp

theorem logratio_sum_zero {n N : ℕ} (hN : 2 * n ≤ N) (q k : Fin n → EuclideanSpace ℝ (Fin N))
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∑ j, (Real.log (sigT q k j) - (1 / 2) * Real.log (lamP q k j * lamM q k j)) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, logdet_identity hN q k hli, sub_self]

theorem eq_zero_of_sum_zero_of_const {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hsum : ∑ i, r i = 0)
    (c : ℝ) (hc : ∀ i, r i = c) : ∀ i, r i = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have : (n : ℝ) * c = 0 := by
    rw [← hsum, Finset.sum_congr rfl (fun i _ => hc i)]
    simp
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hn)
    · exact h
  intro i
  rw [hc i, hc0]

theorem const_one_sub_two_a {n : ℕ} [NeZero n] (f g : ℝ) (hf : 0 < f) (hg : 0 < g) :
    1 - 2 * profA (fun _ : Fin n => f) (fun _ : Fin n => g) = (f - g) ^ 2 / (f + g) ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < (f + g) ^ 2 := by positivity
  simp only [profA, normSq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Congruence of the operator: transporting the rows by an isometry `O` conjugates
`L` by `O`, i.e., `L' (O x) = O (L x)`. With `exists_isometry_of_same_W` this is
`L' = O L O⁻¹` for forms with the same `(Σ, W)`. -/
theorem formL_isometry {n N : ℕ} (O : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (q k : Fin n → EuclideanSpace ℝ (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    formL (fun i => O (q i)) (fun i => O (k i)) (O x) = O (formL q k x) := by
  simp [formL, LinearMap.sum_apply, map_sum, map_smul, LinearIsometryEquiv.inner_map_map]

end Odesky
