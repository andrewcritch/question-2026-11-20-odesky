import OdeskyLean.GenProfile

/-!
# `(Σ, W)` determines the form up to orthogonal congruence, and so the profile

Forms `L = ∑ σ_i u_i v_iᵀ` and `L' = ∑ σ_i u'_i v'_iᵀ` with the same `σ`, orthonormal
families `u, v, u', v'`, and the same cosine matrix `W_ij = ⟪u_i, v_j⟫ = ⟪u'_i, v'_j⟫`:

* `exists_isometry_of_same_W`: some linear isometry `O` of `ℝᴺ` maps `u_i ↦ u'_i`
  and `v_i ↦ v'_i`, so `L' = O L O⁻¹`.
* `gprof_isometry`: the profile and the relation-(1) error are invariant under
  `(q, k) ↦ (O ∘ q, O ∘ k)` for a linear isometry `O`.
* `gprof_eq_of_same_W`: hence the profile and the relation-(1) error of `L` and `L'`
  are equal.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_isometry_of_same_W (u v u' v' : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) (hu' : Orthonormal ℝ u') (hv' : Orthonormal ℝ v')
    (hW : ∀ i j, ⟪u i, v j⟫ = ⟪u' i, v' j⟫) :
    ∃ O : V ≃ₗᵢ[ℝ] V, ∀ i, O (u i) = u' i ∧ O (v i) = v' i := by
  sorry

theorem gprof_isometry (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    gA (fun i => O (q i)) (fun i => O (k i)) = gA q k ∧
    gB (fun i => O (q i)) (fun i => O (k i)) = gB q k ∧
    gC (fun i => O (q i)) (fun i => O (k i)) = gC q k ∧
    gD (fun i => O (q i)) (fun i => O (k i)) = gD q k ∧
    gErr (fun i => O (q i)) (fun i => O (k i)) = gErr q k := by
  sorry

theorem gprof_eq_of_same_W (σ : Fin n → ℝ) (u v u' v' : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) (hu' : Orthonormal ℝ u') (hv' : Orthonormal ℝ v')
    (hW : ∀ i j, ⟪u i, v j⟫ = ⟪u' i, v' j⟫) :
    gA (fun i => σ i • v' i) u' = gA (fun i => σ i • v i) u ∧
    gB (fun i => σ i • v' i) u' = gB (fun i => σ i • v i) u ∧
    gC (fun i => σ i • v' i) u' = gC (fun i => σ i • v i) u ∧
    gD (fun i => σ i • v' i) u' = gD (fun i => σ i • v i) u ∧
    gErr (fun i => σ i • v' i) u' = gErr (fun i => σ i • v i) u := by
  sorry

end Odesky
