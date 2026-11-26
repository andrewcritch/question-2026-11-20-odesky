import OdeskyLean.GenProfile

/-!
# The identities of §1, for every form

Write `L = ∑_i σ_i u_i v_iᵀ` with `σ_i > 0` and orthonormal families `u`, `v`
(the decomposition from the nonzero singular values). In the notation of
`GenProfile.lean`, `L x = ∑ ⟪q_i, x⟫ k_i` with rows `q_i = σ_i v_i` and `k_i = u_i`.
Let `W_ij = ⟪u_i, v_j⟫`, `t_i = W_ii`, `F = ∑ σ_i²`,
`m₂ = ∑ σ_i² t_i² / F`, and `q = ∑_{i≠j} σ_i σ_j W_ij W_ji / F`.

* `gA_identity`: `a = (1 - m₂ - q)/2`.
* `gprof_sum_eq_one`: for `2n ≤ N`, `a + b + c + d = 1`. The proof needs that `S`
  has at most `n` positive and at most `n` negative eigenvalues: `⟪S x, x⟫ =
  ∑ ⟪q_i, x⟫⟪k_i, x⟫` vanishes on the subspace `{x : ⟪q_i, x⟫ = 0 ∀ i}` of
  codimension at most `n`, so that subspace meets the span of the eigenvectors with
  positive eigenvalues only in `0`; similarly for negative eigenvalues. Then the
  first `n` sorted eigenvalues hold every positive eigenvalue, the last `n` hold
  every negative one, and `‖S‖² = ∑ λ₊² + ∑ λ₋² = ‖L‖² - ‖T‖²`.
* `gA_sub_gB_identity`: `a - b = c + d - m₂ - q`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- `W_ij = ⟪u_i, v_j⟫`. -/
noncomputable def Wm (u v : Fin n → V) (i j : Fin n) : ℝ := ⟪u i, v j⟫

/-- `F = ∑ σ_i²`. -/
noncomputable def Fsq (σ : Fin n → ℝ) : ℝ := ∑ i, σ i ^ 2

/-- `m₂ = ∑ σ_i² W_ii² / F`. -/
noncomputable def m2 (σ : Fin n → ℝ) (u v : Fin n → V) : ℝ :=
  (∑ i, σ i ^ 2 * Wm u v i i ^ 2) / Fsq σ

/-- `q = ∑_{i≠j} σ_i σ_j W_ij W_ji / F`. -/
noncomputable def qrec (σ : Fin n → ℝ) (u v : Fin n → V) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else σ i * σ j * Wm u v i j * Wm u v j i) / Fsq σ

theorem gA_identity [NeZero n] (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (u v : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u = (1 - m2 σ u v - qrec σ u v) / 2 := by
  sorry

theorem gprof_sum_eq_one [NeZero n] (hN : 2 * n ≤ N) (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i)
    (u v : Fin n → V) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u + gB (fun i => σ i • v i) u +
      gC (fun i => σ i • v i) u + gD (fun i => σ i • v i) u = 1 := by
  sorry

theorem gA_sub_gB_identity [NeZero n] (hN : 2 * n ≤ N) (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i)
    (u v : Fin n → V) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u - gB (fun i => σ i • v i) u =
      gC (fun i => σ i • v i) u + gD (fun i => σ i • v i) u - m2 σ u v - qrec σ u v := by
  sorry

end Odesky
