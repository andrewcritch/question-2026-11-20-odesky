import Mathlib

/-!
# Layer 3: block spectra of a sum of rank-one forms on orthogonal planes

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

/-- A sum of rank-one forms on orthogonal planes: weights `s_i > 0`, unit vectors
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
  simp only [L, Lt, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm x (B.v i)]
  ring

/-- Symmetric part `S = (L + Lᵀ)/2`. -/
noncomputable def S (x : V) : V := (1 / 2 : ℝ) • (B.L x + B.Lt x)

/-- Antisymmetric part `T = (L - Lᵀ)/2`. -/
noncomputable def T (x : V) : V := (1 / 2 : ℝ) • (B.L x - B.Lt x)

private lemma uu_self (i : Fin n) : ⟪B.u i, B.u i⟫ = 1 := by
  simp [B.u_unit]

private lemma vv_self (i : Fin n) : ⟪B.v i, B.v i⟫ = 1 := by
  simp [B.v_unit]

private lemma L_u (i : Fin n) : B.L (B.u i) = (B.s i * B.t i) • B.u i := by
  rw [L, Finset.sum_eq_single i]
  · rw [← real_inner_comm (B.v i) (B.u i)]; rfl
  · intro j _ hji
    rw [← real_inner_comm (B.v j) (B.u i), B.uv i j (Ne.symm hji)]
    simp
  · simp

private lemma L_v (i : Fin n) : B.L (B.v i) = B.s i • B.u i := by
  rw [L, Finset.sum_eq_single i]
  · simp [B.v_unit]
  · intro j _ hji
    simp [B.vv j i hji]
  · simp

private lemma Lt_u (i : Fin n) : B.Lt (B.u i) = B.s i • B.v i := by
  rw [Lt, Finset.sum_eq_single i]
  · simp [B.u_unit]
  · intro j _ hji
    simp [B.uu j i hji]
  · simp

private lemma Lt_v (i : Fin n) : B.Lt (B.v i) = (B.s i * B.t i) • B.v i := by
  rw [Lt, Finset.sum_eq_single i]
  · rfl
  · intro j _ hji
    simp [B.uv j i hji]
  · simp

private lemma L_add (x y : V) : B.L (x + y) = B.L x + B.L y := by
  simp [L, inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]

private lemma Lt_add (x y : V) : B.Lt (x + y) = B.Lt x + B.Lt y := by
  simp [Lt, inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]

private lemma L_sub (x y : V) : B.L (x - y) = B.L x - B.L y := by
  simp [L, inner_sub_right, mul_sub, sub_smul, Finset.sum_sub_distrib]

private lemma Lt_sub (x y : V) : B.Lt (x - y) = B.Lt x - B.Lt y := by
  simp [Lt, inner_sub_right, mul_sub, sub_smul, Finset.sum_sub_distrib]

private lemma T_smul (c : ℝ) (x : V) : B.T (c • x) = c • B.T x := by
  have hl : B.L (c • x) = c • B.L x := by
    simp only [L, real_inner_smul_right, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm]
  have hlt : B.Lt (c • x) = c • B.Lt x := by
    simp only [Lt, real_inner_smul_right, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm]
  rw [T, hl, hlt, ← smul_sub, smul_comm]
  rfl

theorem S_add (i : Fin n) : B.S (B.u i + B.v i) = B.α i • (B.u i + B.v i) := by
  rw [S, B.L_add, B.Lt_add, B.L_u, B.L_v, B.Lt_u, B.Lt_v]
  simp only [α, smul_add, smul_smul]
  module

theorem S_sub (i : Fin n) : B.S (B.u i - B.v i) = (-B.β i) • (B.u i - B.v i) := by
  rw [S, B.L_sub, B.Lt_sub, B.L_u, B.L_v, B.Lt_u, B.Lt_v]
  simp only [β, smul_sub]
  module

theorem T_add (i : Fin n) : B.T (B.u i + B.v i) = B.α i • (B.u i - B.v i) := by
  rw [T, B.L_add, B.Lt_add, B.L_u, B.L_v, B.Lt_u, B.Lt_v]
  simp only [α, smul_sub]
  module

theorem T_sub (i : Fin n) : B.T (B.u i - B.v i) = (-B.β i) • (B.u i + B.v i) := by
  rw [T, B.L_sub, B.Lt_sub, B.L_u, B.L_v, B.Lt_u, B.Lt_v]
  simp only [β, smul_add]
  module

/-- `-T²` is `α_i β_i` times the identity on the plane `span(u_i, v_i)`. -/
theorem neg_T_sq_add (i : Fin n) :
    -B.T (B.T (B.u i + B.v i)) = (B.α i * B.β i) • (B.u i + B.v i) := by
  rw [B.T_add, B.T_smul, B.T_sub]
  simp [smul_smul, add_comm]

theorem neg_T_sq_sub (i : Fin n) :
    -B.T (B.T (B.u i - B.v i)) = (B.α i * B.β i) • (B.u i - B.v i) := by
  rw [B.T_sub, B.T_smul, B.T_add]
  simp [smul_smul, mul_comm]

theorem S_perp (z : V) (hu : ∀ j, ⟪B.u j, z⟫ = 0) (hv : ∀ j, ⟪B.v j, z⟫ = 0) :
    B.S z = 0 := by
  simp [S, L, Lt, hu, hv]

theorem T_perp (z : V) (hu : ∀ j, ⟪B.u j, z⟫ = 0) (hv : ∀ j, ⟪B.v j, z⟫ = 0) :
    B.T z = 0 := by
  simp [T, L, Lt, hu, hv]

theorem inner_add_sub (i : Fin n) : ⟪B.u i + B.v i, B.u i - B.v i⟫ = 0 := by
  simp only [inner_add_left, inner_sub_right, B.uu_self, B.vv_self]
  rw [real_inner_comm (B.v i) (B.u i)]
  ring

/-- `σ_i = α_i + β_i` and `σ_i t_i = α_i - β_i`. -/
theorem α_add_β (i : Fin n) : B.α i + B.β i = B.s i := by
  unfold α β
  ring

theorem α_sub_β (i : Fin n) : B.α i - B.β i = B.s i * B.t i := by
  unfold α β
  ring

/-- `α_i β_i = s_i² (1 - t_i²) / 4`, the squared antisymmetric singular value of
block `i`. -/
theorem α_mul_β (i : Fin n) : B.α i * B.β i = B.s i ^ 2 * (1 - B.t i ^ 2) / 4 := by
  unfold α β
  ring

/-- If every tilt has `|t_i| < 1`, then `α_i, β_i > 0`. -/
theorem α_pos (hT : ∀ i, |B.t i| < 1) (i : Fin n) : 0 < B.α i := by
  unfold α
  exact div_pos (mul_pos (B.s_pos i) (by have := (abs_lt.mp (hT i)).1; linarith)) (by norm_num)

theorem β_pos (hT : ∀ i, |B.t i| < 1) (i : Fin n) : 0 < B.β i := by
  unfold β
  exact div_pos (mul_pos (B.s_pos i) (by have := (abs_lt.mp (hT i)).2; linarith)) (by norm_num)

end OrthoBlocks

end Odesky
