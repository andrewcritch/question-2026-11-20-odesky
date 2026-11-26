import OdeskyLean.GenProfile
import OdeskyLean.Congruence

/-!
# From a head `L = Kᵀ Q` to the singular-value form used in §1

* `gprof_of_formL_eq`: the profile, the spectral lists and the relation-(1) error
  depend only on the operator `L`, not on the rows that represent it.
* `exists_svd_rows`: every `L = Kᵀ Q` of rank `n` (with `n` rows) can be written as
  `L = ∑ σ_i u_i v_iᵀ` with `σ_i > 0` and orthonormal families `u`, `v`, i.e.,
  `formL (σ • v) u = formL q k`.
* `lists_isometry`: the spectral lists `λ₊`, `λ₋`, `σ(T)` are invariant under an
  isometry of `ℝᴺ`, so relation (1) itself (not only its error) is invariant under
  orthogonal congruence.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

theorem gprof_of_formL_eq (q k q' k' : Fin n → V) (h : formL q k = formL q' k') :
    lamP q' k' = lamP q k ∧ lamM q' k' = lamM q k ∧ sigT q' k' = sigT q k ∧
    gA q' k' = gA q k ∧ gB q' k' = gB q k ∧ gC q' k' = gC q k ∧ gD q' k' = gD q k ∧
    gErr q' k' = gErr q k := by
  sorry

theorem exists_svd_rows (q k : Fin n → V)
    (hrank : Module.finrank ℝ (LinearMap.range (formL q k)) = n) :
    ∃ (σ : Fin n → ℝ) (u v : Fin n → V), (∀ i, 0 < σ i) ∧ Orthonormal ℝ u ∧
      Orthonormal ℝ v ∧ formL (fun i => σ i • v i) u = formL q k := by
  sorry

theorem lists_isometry (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    lamP (fun i => O (q i)) (fun i => O (k i)) = lamP q k ∧
    lamM (fun i => O (q i)) (fun i => O (k i)) = lamM q k ∧
    sigT (fun i => O (q i)) (fun i => O (k i)) = sigT q k := by
  sorry

end Odesky
