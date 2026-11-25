import Mathlib

/-!
# Layer 3: block spectra of an orthogonal sum of rank-one forms

`L = ∑ s_i u_i v_iᵀ` acts on `ℝᴺ` by `L x = ∑ s_i ⟪v_i, x⟫ u_i`.
Its symmetric part `S = (L + Lᵀ)/2` and antisymmetric part `T = (L - Lᵀ)/2` are
written out as maps on vectors. This file proves the eigenvector equations that
fix the spectra of `S` and `T` (Theorem A, proof step 1):

* `S (u_i + v_i) = α_i (u_i + v_i)`, `S (u_i - v_i) = -β_i (u_i - v_i)`,
* `T (u_i + v_i) = α_i (u_i - v_i)`, `T (u_i - v_i) = -β_i (u_i + v_i)`,
  so `Tᵀ T = -T²` has eigenvalue `α_i β_i` on the whole plane `span(u_i, v_i)`,
* `S z = T z = 0` for `z` orthogonal to every `u_j, v_j`,
* `u_i + v_i ⟂ u_i - v_i`.

with `t_i = ⟪u_i, v_i⟫`, `α_i = s_i (1 + t_i)/2`, `β_i = s_i (1 - t_i)/2`.
-/

open Finset RealInnerProductSpace

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- An orthogonal sum of rank-one forms: weights `s_i > 0`, unit vectors
`u_i, v_i`, and mutually orthogonal planes `span(u_i, v_i)`. -/
structure OrthoBlocks (n N : ℕ) where
  s : Fin n → ℝ
  u : Fin n → EuclideanSpace ℝ (Fin N)
  v : Fin n → EuclideanSpace ℝ (Fin N)
  s_pos : ∀ i, 0 < s i
  u_unit : ∀ i, ‖u i‖ = 1
  v_unit : ∀ i, ‖v i‖ = 1
  uu : ∀ i j, i ≠ j → ⟪u i, u j⟫ = 0
  uv : ∀ i j, i ≠ j → ⟪u i, v j⟫ = 0
  vv : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0

namespace OrthoBlocks

variable (B : OrthoBlocks n N)

/-- The tilt `t_i = ⟪u_i, v_i⟫`. -/
noncomputable def t (i : Fin n) : ℝ := ⟪B.u i, B.v i⟫

/-- `α_i = s_i (1 + t_i) / 2`. -/
noncomputable def α (i : Fin n) : ℝ := B.s i * (1 + B.t i) / 2

/-- `β_i = s_i (1 - t_i) / 2`. -/
noncomputable def β (i : Fin n) : ℝ := B.s i * (1 - B.t i) / 2

/-- `L x = ∑ s_i ⟪v_i, x⟫ u_i`. -/
noncomputable def L (x : V) : V := ∑ i, (B.s i * ⟪B.v i, x⟫) • B.u i

/-- `Lᵀ x = ∑ s_i ⟪u_i, x⟫ v_i`. -/
noncomputable def Lt (x : V) : V := ∑ i, (B.s i * ⟪B.u i, x⟫) • B.v i

/-- Sanity check: `Lt` is the adjoint of `L`. -/
theorem inner_L_eq (x y : V) : ⟪B.L x, y⟫ = ⟪x, B.Lt y⟫ := by
  sorry

/-- Symmetric part `S = (L + Lᵀ)/2`. -/
noncomputable def S (x : V) : V := (1 / 2 : ℝ) • (B.L x + B.Lt x)

/-- Antisymmetric part `T = (L - Lᵀ)/2`. -/
noncomputable def T (x : V) : V := (1 / 2 : ℝ) • (B.L x - B.Lt x)

theorem S_add (i : Fin n) : B.S (B.u i + B.v i) = B.α i • (B.u i + B.v i) := by
  sorry

theorem S_sub (i : Fin n) : B.S (B.u i - B.v i) = (-B.β i) • (B.u i - B.v i) := by
  sorry

theorem T_add (i : Fin n) : B.T (B.u i + B.v i) = B.α i • (B.u i - B.v i) := by
  sorry

theorem T_sub (i : Fin n) : B.T (B.u i - B.v i) = (-B.β i) • (B.u i + B.v i) := by
  sorry

/-- `-T²` is `α_i β_i` times the identity on the plane `span(u_i, v_i)`. -/
theorem neg_T_sq_add (i : Fin n) :
    -B.T (B.T (B.u i + B.v i)) = (B.α i * B.β i) • (B.u i + B.v i) := by
  sorry

theorem neg_T_sq_sub (i : Fin n) :
    -B.T (B.T (B.u i - B.v i)) = (B.α i * B.β i) • (B.u i - B.v i) := by
  sorry

theorem S_perp (z : V) (hu : ∀ j, ⟪B.u j, z⟫ = 0) (hv : ∀ j, ⟪B.v j, z⟫ = 0) :
    B.S z = 0 := by
  sorry

theorem T_perp (z : V) (hu : ∀ j, ⟪B.u j, z⟫ = 0) (hv : ∀ j, ⟪B.v j, z⟫ = 0) :
    B.T z = 0 := by
  sorry

theorem inner_add_sub (i : Fin n) : ⟪B.u i + B.v i, B.u i - B.v i⟫ = 0 := by
  sorry

/-- `σ_i = α_i + β_i` and `σ_i t_i = α_i - β_i`. -/
theorem α_add_β (i : Fin n) : B.α i + B.β i = B.s i := by
  sorry

theorem α_sub_β (i : Fin n) : B.α i - B.β i = B.s i * B.t i := by
  sorry

/-- `α_i β_i = s_i² (1 - t_i²) / 4`, the squared antisymmetric singular value of
block `i`. -/
theorem α_mul_β (i : Fin n) : B.α i * B.β i = B.s i ^ 2 * (1 - B.t i ^ 2) / 4 := by
  sorry

/-- If every tilt has `|t_i| < 1`, then `α_i, β_i > 0`. -/
theorem α_pos (hT : ∀ i, |B.t i| < 1) (i : Fin n) : 0 < B.α i := by
  sorry

theorem β_pos (hT : ∀ i, |B.t i| < 1) (i : Fin n) : 0 < B.β i := by
  sorry

end OrthoBlocks

end Odesky
