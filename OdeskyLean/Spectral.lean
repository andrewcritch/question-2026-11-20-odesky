import OdeskyLean.Geometry
import OdeskyLean.Rearrangement

/-!
# Layer 5 (gap G1): from eigenvector equations to spectra and norms

For an orthogonal sum of rank-one forms on `ℝᴺ` with `2n ≤ N` and every tilt
`|t_i| < 1`:

* the characteristic polynomial of `S` is `∏ (X - α_i)(X + β_i) · X^(N-2n)`, so
  the positive eigenvalues of `S` are the `α_i` and the negative ones are the
  `-β_i`, with multiplicity;
* the characteristic polynomial of `TᵀT = -T²` is `∏ (X - α_i β_i)² · X^(N-2n)`,
  so the singular values of `T`, each pair counted once, are the `√(α_i β_i)`;
* the squared Frobenius norms are `‖L‖² = ∑ s_i²`, `‖S‖² = ∑ (α_i² + β_i²)`,
  `‖T‖² = 2 ∑ α_i β_i`, computed in any orthonormal basis;
* a decreasing list with the same multiset of values as `α` is `α ∘ σ` for any
  decreasing sort `σ` of `α`.

These are the facts that `Profile.lean` takes as the definition of the profile.
-/

open Finset Polynomial RealInnerProductSpace

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A decreasing list is determined by its multiset of values. -/
theorem sorted_eq_of_multiset {m : ℕ} (α ℓ : Fin m → ℝ) (hℓ : Antitone ℓ)
    (hm : Multiset.map ℓ univ.val = Multiset.map α univ.val)
    {σ : Equiv.Perm (Fin m)} (hσ : SortsDesc α σ) : ℓ = α ∘ σ := by
  sorry

namespace OrthoBlocks

variable (B : OrthoBlocks n N)

/-- `L` as a linear map: `x ↦ ∑ s_i ⟪v_i, x⟫ u_i`. -/
noncomputable def Llin : V →ₗ[ℝ] V :=
  ∑ i, B.s i • (innerSL ℝ (B.v i) : V →L[ℝ] ℝ).toLinearMap.smulRight (B.u i)

/-- `Lᵀ` as a linear map: `x ↦ ∑ s_i ⟪u_i, x⟫ v_i`. -/
noncomputable def Ltlin : V →ₗ[ℝ] V :=
  ∑ i, B.s i • (innerSL ℝ (B.u i) : V →L[ℝ] ℝ).toLinearMap.smulRight (B.v i)

/-- `S = (L + Lᵀ)/2` as a linear map. -/
noncomputable def Slin : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (B.Llin + B.Ltlin)

/-- `T = (L - Lᵀ)/2` as a linear map. -/
noncomputable def Tlin : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (B.Llin - B.Ltlin)

theorem Llin_apply (x : V) : B.Llin x = B.L x := by
  sorry

theorem Slin_apply (x : V) : B.Slin x = B.S x := by
  sorry

theorem Tlin_apply (x : V) : B.Tlin x = B.T x := by
  sorry

/-- Characteristic polynomial of `S`. -/
theorem charpoly_S (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly =
      (∏ i, (X - C (B.α i)) * (X + C (B.β i))) * X ^ (N - 2 * n) := by
  sorry

/-- Characteristic polynomial of `TᵀT = -T²`. -/
theorem charpoly_neg_T_sq (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    (-(B.Tlin ∘ₗ B.Tlin)).charpoly =
      (∏ i, (X - C (B.α i * B.β i)) ^ 2) * X ^ (N - 2 * n) := by
  sorry

/-- The positive eigenvalues of `S`, with multiplicity, are the `α_i`. -/
theorem roots_S_pos (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly.roots.filter (fun x => 0 < x) = Multiset.map B.α univ.val := by
  sorry

/-- The negative eigenvalues of `S`, with multiplicity, are the `-β_i`. -/
theorem roots_S_neg (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly.roots.filter (fun x => x < 0) =
      Multiset.map (fun i => -B.β i) univ.val := by
  sorry

/-- The nonzero eigenvalues of `TᵀT`, with multiplicity, are the `α_i β_i`,
each twice. -/
theorem roots_neg_T_sq_pos (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    (-(B.Tlin ∘ₗ B.Tlin)).charpoly.roots.filter (fun x => 0 < x) =
      2 • Multiset.map (fun i => B.α i * B.β i) univ.val := by
  sorry

/-- `‖L‖² = ∑ s_i²` in any orthonormal basis. -/
theorem frob_L (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.L (b k)‖ ^ 2 = ∑ i, B.s i ^ 2 := by
  sorry

/-- `‖S‖² = ∑ (α_i² + β_i²)` in any orthonormal basis. -/
theorem frob_S (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.S (b k)‖ ^ 2 = ∑ i, (B.α i ^ 2 + B.β i ^ 2) := by
  sorry

/-- `‖T‖² = 2 ∑ α_i β_i` in any orthonormal basis. -/
theorem frob_T (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.T (b k)‖ ^ 2 = 2 * ∑ i, B.α i * B.β i := by
  sorry

end OrthoBlocks

end Odesky
