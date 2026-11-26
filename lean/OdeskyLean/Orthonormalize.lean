import Mathlib

/-!
# Layer 8 (gap G2): a nearby orthonormal family

If the Gram matrix of `x_1, …, x_m` is within `δ < 1` of the identity as a
quadratic form, then there is an orthonormal family `e` with
`‖∑ c_a (x_a - e_a)‖ ≤ δ |c|` for every coefficient vector `c`.

Proof idea: `e := G^{-1/2} x` (symmetric square root of the Gram matrix `G`);
then `∑ c_a (x_a - e_a) = ∑_b ((G^{1/2} - I) c)_b e_b`, and every eigenvalue `γ`
of `G` has `|√γ - 1| ≤ |γ - 1| ≤ δ`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {N m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

private lemma ob_cols (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (a a' : Fin m) :
    ∑ k, (b k) a * (b k) a' = if a = a' then 1 else 0 := by
  have := b.sum_inner_mul_inner (EuclideanSpace.single a 1) (EuclideanSpace.single a' 1)
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, mul_comm,
    eq_comm] using this

private lemma ob_rows (b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (k l : Fin m) :
    ∑ a, (b k) a * (b l) a = if k = l then 1 else 0 := by
  have := orthonormal_iff_ite.1 b.orthonormal k l
  rw [← this]; simp [PiLp.inner_apply, mul_comm]

private lemma quad_eq (x : Fin m → V) (c : Fin m → ℝ) :
    ∑ a, ∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)
      = ‖∑ a, c a • x a‖ ^ 2 - ∑ a, c a ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, mul_sub, sum_sub_distrib,
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  congr 1
  · apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; ring
  · apply sum_congr rfl; intro a _; ring

private lemma norm_sq_orth (y : Fin m → V) (γ : Fin m → ℝ)
    (hy : ∀ k l, ⟪y k, y l⟫ = if k = l then γ k else 0) (w : Fin m → ℝ) :
    ‖∑ k, w k • y k‖ ^ 2 = ∑ k, w k ^ 2 * γ k := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, hy, mul_ite, mul_zero,
    sum_ite_eq, mem_univ, if_true]
  apply sum_congr rfl; intro k _; ring

theorem exists_orthonormal_near (x : Fin m → V) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hG : ∀ c : Fin m → ℝ,
      |∑ a, ∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)| ≤ δ * ∑ a, c a ^ 2) :
    ∃ e : Fin m → V, Orthonormal ℝ e ∧
      ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2) := by
  set G : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => ⟪x a, x b⟫ with hGdef
  have hH : G.IsHermitian := by
    ext a b; simp [G, real_inner_comm]
  set B := hH.eigenvectorBasis
  set γ := hH.eigenvalues
  set u : Fin m → Fin m → ℝ := fun k a => (B k) a with hu
  have hP : ∀ a a', ∑ k, u k a * u k a' = if a = a' then 1 else 0 := ob_cols B
  have hO : ∀ k l, ∑ a, u k a * u l a = if k = l then 1 else 0 := ob_rows B
  have hev : ∀ l a, ∑ a', ⟪x a, x a'⟫ * u l a' = γ l * u l a := by
    intro l a
    have := congrFun (hH.mulVec_eigenvectorBasis l) a
    simpa [Matrix.mulVec, dotProduct, G, u] using this
  set y : Fin m → V := fun k => ∑ a, u k a • x a with hy
  have hyy : ∀ k l, ⟪y k, y l⟫ = if k = l then γ k else 0 := by
    intro k l
    simp only [y, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    have : ∀ a, ∑ a', u l a' * (u k a * ⟪x a, x a'⟫) = u k a * (γ l * u l a) := by
      intro a; rw [← hev l a, mul_sum]; apply sum_congr rfl; intro a' _; ring
    rw [sum_comm]
    simp only [this]
    have h2 : ∑ a, u k a * (γ l * u l a) = γ l * ∑ a, u k a * u l a := by
      rw [mul_sum]; apply sum_congr rfl; intro a _; ring
    rw [h2, hO]; split_ifs with h <;> simp [h]
  have hγ : ∀ k, |γ k - 1| ≤ δ := by
    intro k
    have h := hG (u k)
    rw [quad_eq, ← sq_abs] at h
    have h1 : ‖y k‖ ^ 2 = γ k := by
      rw [← real_inner_self_eq_norm_sq, hyy]; simp
    have h2 : ∑ a, u k a ^ 2 = 1 := by
      have := hO k k; simp only [if_true] at this; rw [← this]
      apply sum_congr rfl; intro a _; ring
    simpa [y, h1, h2] using h
  have hγpos : ∀ k, 0 < γ k := by
    intro k; have := hγ k; rw [abs_le] at this; linarith
  set e : Fin m → V := fun a => ∑ k, (u k a / Real.sqrt (γ k)) • y k with he
  have hx : ∀ a, x a = ∑ k, u k a • y k := by
    intro a
    simp only [y, smul_sum, smul_smul]
    rw [sum_comm]
    simp only [← sum_smul, hP, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, if_true]
  refine ⟨e, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro a a'
    simp only [e, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hyy,
      mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    rw [← hP]
    apply sum_congr rfl; intro k _
    have hs := Real.mul_self_sqrt (hγpos k).le
    have hs0 : Real.sqrt (γ k) ≠ 0 := (Real.sqrt_pos.2 (hγpos k)).ne'
    generalize Real.sqrt (γ k) = s at hs hs0 ⊢
    rw [← hs]; field_simp
  · intro c
    set d : Fin m → ℝ := fun k => ∑ a, c a * u k a
    have hsum : ∑ a, c a • (x a - e a)
        = ∑ k, (d k * (1 - 1 / Real.sqrt (γ k))) • y k := by
      have : ∀ a, x a - e a = ∑ k, (u k a * (1 - 1 / Real.sqrt (γ k))) • y k := by
        intro a
        rw [hx a]
        simp only [e, ← sum_sub_distrib, ← sub_smul]
        apply sum_congr rfl; intro k _; congr 1; ring
      simp only [this, smul_sum, smul_smul]
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      simp only [d, ← sum_smul, sum_mul]
      congr 1; apply sum_congr rfl; intro a _; ring
    have hd : ∑ k, d k ^ 2 = ∑ a, c a ^ 2 := by
      have h1 : ∀ k, d k ^ 2 = ∑ a, ∑ a', c a * c a' * (u k a * u k a') := by
        intro k; simp only [d, sq, sum_mul_sum]
        apply sum_congr rfl; intro a _; apply sum_congr rfl; intro a' _; ring
      rw [sum_congr rfl (fun k _ => h1 k), sum_comm]
      apply sum_congr rfl; intro a _
      rw [sum_comm]
      simp only [← mul_sum, hP, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
      ring
    have hsq : ‖∑ a, c a • (x a - e a)‖ ^ 2 ≤ δ ^ 2 * ∑ a, c a ^ 2 := by
      rw [hsum, norm_sq_orth y γ hyy, ← hd, mul_sum]
      apply sum_le_sum; intro k _
      have hs := Real.sq_sqrt (hγpos k).le
      have hs0 : 0 < Real.sqrt (γ k) := Real.sqrt_pos.2 (hγpos k)
      have hrw : (d k * (1 - 1 / Real.sqrt (γ k))) ^ 2 * γ k
          = d k ^ 2 * (Real.sqrt (γ k) - 1) ^ 2 := by
        generalize Real.sqrt (γ k) = s at hs hs0 ⊢
        rw [← hs]; field_simp
      rw [hrw]
      have hb : (Real.sqrt (γ k) - 1) ^ 2 ≤ δ ^ 2 := by
        have h1 : |Real.sqrt (γ k) - 1| ≤ |γ k - 1| := by
          have : γ k - 1 = (Real.sqrt (γ k) - 1) * (Real.sqrt (γ k) + 1) := by
            linear_combination -hs
          rw [this, abs_mul]
          have : 1 ≤ |Real.sqrt (γ k) + 1| := by
            rw [abs_of_pos (by linarith)]; linarith
          nlinarith [abs_nonneg (Real.sqrt (γ k) - 1)]
        have := h1.trans (hγ k)
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [mul_comm (δ ^ 2)]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    calc ‖∑ a, c a • (x a - e a)‖ = Real.sqrt (‖∑ a, c a • (x a - e a)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (δ ^ 2 * ∑ a, c a ^ 2) := Real.sqrt_le_sqrt hsq
      _ = δ * Real.sqrt (∑ a, c a ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ0]

end Odesky
