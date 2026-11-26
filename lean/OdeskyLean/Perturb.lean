import OdeskyLean.GenProfile

/-!
# Layer 10 (gap G2): perturbing the rows perturbs the form

Rows `q_i = ∑_a AQ_{ia} x_a`, `k_i = ∑_a AK_{ia} x_a` are fixed combinations of
vectors `x_a`. Replacing `x` by an orthonormal family `e` with
`‖∑ c_a (x_a - e_a)‖ ≤ δ |c|` moves `L` and `Lᵀ` by at most
`δ (2 + δ) κ` in operator norm, with `κ = ∑_i |AQ_i| |AK_i|`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Row `i` is `∑_a A_{ia} x_a`. -/
noncomputable def comb (A : Fin n → Fin m → ℝ) (x : Fin m → V) (i : Fin n) : V :=
  ∑ a, A i a • x a

/-- `κ = ∑_i |AQ_i| |AK_i|`, with Euclidean norms of the coefficient rows. -/
noncomputable def kappa (AQ AK : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, Real.sqrt (∑ a, AQ i a ^ 2) * Real.sqrt (∑ a, AK i a ^ 2)

private lemma formL_apply' (q k : Fin n → V) (y : V) : formL q k y = ∑ i, ⟪q i, y⟫ • k i := by
  simp [formL, LinearMap.sum_apply]

private lemma formLt_eq (q k : Fin n → V) : formLt q k = formL k q := rfl

private lemma norm_comb_on (A : Fin n → Fin m → ℝ) (e : Fin m → V) (he : Orthonormal ℝ e)
    (i : Fin n) : ‖comb A e i‖ = Real.sqrt (∑ a, A i a ^ 2) := by
  rw [comb, norm_eq_sqrt_real_inner, he.inner_sum]
  simp [sq]

private lemma comb_sub (A : Fin n → Fin m → ℝ) (x e : Fin m → V) (i : Fin n) :
    comb A x i - comb A e i = ∑ a, A i a • (x a - e a) := by
  simp [comb, smul_sub, Finset.sum_sub_distrib]

/-- Generic perturbation bound for `formL`. -/
private lemma formL_perturb_gen (q k q' k' : Fin n → V) (α β : Fin n → ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hq : ∀ i, ‖q i - q' i‖ ≤ δ * α i) (hq' : ∀ i, ‖q' i‖ ≤ α i)
    (hk : ∀ i, ‖k i - k' i‖ ≤ δ * β i) (hk' : ∀ i, ‖k' i‖ ≤ β i) (y : V) :
    ‖formL q k y - formL q' k' y‖ ≤ δ * (2 + δ) * (∑ i, α i * β i) * ‖y‖ := by
  rw [formL_apply', formL_apply', ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hα : 0 ≤ α i := (norm_nonneg _).trans (hq' i)
  have hβ : 0 ≤ β i := (norm_nonneg _).trans (hk' i)
  have hy := norm_nonneg y
  have e1 : ⟪q i, y⟫ • k i - ⟪q' i, y⟫ • k' i
      = ⟪q i - q' i, y⟫ • k i + ⟪q' i, y⟫ • (k i - k' i) := by
    rw [inner_sub_left, sub_smul, smul_sub]; abel
  rw [e1]
  have hkn : ‖k i‖ ≤ (1 + δ) * β i := by
    have h2 : ‖k i‖ ≤ ‖k' i‖ + ‖k i - k' i‖ := by
      calc ‖k i‖ = ‖k' i + (k i - k' i)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    nlinarith [hk i, hk' i]
  have t1 : ‖⟪q i - q' i, y⟫ • k i‖ ≤ (δ * α i * ‖y‖) * ((1 + δ) * β i) := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul ?_ hkn (norm_nonneg _) (by positivity)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hq i) hy
  have t2 : ‖⟪q' i, y⟫ • (k i - k' i)‖ ≤ (α i * ‖y‖) * (δ * β i) := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul ?_ (hk i) (norm_nonneg _) (by positivity)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hq' i) hy
  refine (norm_add_le _ _).trans ?_
  nlinarith [t1, t2]

private lemma formL_bound_gen (q k : Fin n → V) (α β : Fin n → ℝ)
    (hq : ∀ i, ‖q i‖ ≤ α i) (hk : ∀ i, ‖k i‖ ≤ β i) (y : V) :
    ‖formL q k y‖ ≤ (∑ i, α i * β i) * ‖y‖ := by
  rw [formL_apply', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have hy := norm_nonneg y
  have hα : 0 ≤ α i := (norm_nonneg _).trans (hq i)
  calc |⟪q i, y⟫| * ‖k i‖ ≤ (α i * ‖y‖) * β i := by
        refine mul_le_mul ?_ (hk i) (norm_nonneg _) (by positivity)
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hq i) hy)
    _ = α i * β i * ‖y‖ := by ring

theorem formL_perturb (AQ AK : Fin n → Fin m → ℝ) (x e : Fin m → V) (he : Orthonormal ℝ e)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hxe : ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2)) (y : V) :
    ‖formL (comb AQ x) (comb AK x) y - formL (comb AQ e) (comb AK e) y‖ ≤
      δ * (2 + δ) * kappa AQ AK * ‖y‖ := by
  rw [kappa]
  refine formL_perturb_gen _ _ _ _ _ _ hδ0 (fun i => ?_) (fun i => (norm_comb_on AQ e he i).le)
    (fun i => ?_) (fun i => (norm_comb_on AK e he i).le) y
  · rw [comb_sub]; exact hxe _
  · rw [comb_sub]; exact hxe _

theorem formLt_perturb (AQ AK : Fin n → Fin m → ℝ) (x e : Fin m → V) (he : Orthonormal ℝ e)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hxe : ∀ c : Fin m → ℝ, ‖∑ a, c a • (x a - e a)‖ ≤ δ * Real.sqrt (∑ a, c a ^ 2)) (y : V) :
    ‖formLt (comb AQ x) (comb AK x) y - formLt (comb AQ e) (comb AK e) y‖ ≤
      δ * (2 + δ) * kappa AQ AK * ‖y‖ := by
  rw [formLt_eq, formLt_eq, kappa]
  simp_rw [mul_comm (Real.sqrt (∑ a, AQ _ a ^ 2))]
  refine formL_perturb_gen _ _ _ _ _ _ hδ0 (fun i => ?_) (fun i => (norm_comb_on AK e he i).le)
    (fun i => ?_) (fun i => (norm_comb_on AQ e he i).le) y
  · rw [comb_sub]; exact hxe _
  · rw [comb_sub]; exact hxe _

/-- For an orthonormal family, `‖L y‖ ≤ κ ‖y‖` and `‖Lᵀ y‖ ≤ κ ‖y‖`. -/
theorem formL_bound (AQ AK : Fin n → Fin m → ℝ) (e : Fin m → V) (he : Orthonormal ℝ e) (y : V) :
    ‖formL (comb AQ e) (comb AK e) y‖ ≤ kappa AQ AK * ‖y‖ ∧
      ‖formLt (comb AQ e) (comb AK e) y‖ ≤ kappa AQ AK * ‖y‖ := by
  refine ⟨?_, ?_⟩
  · rw [kappa]
    exact formL_bound_gen _ _ _ _ (fun i => (norm_comb_on AQ e he i).le)
      (fun i => (norm_comb_on AK e he i).le) y
  · rw [formLt_eq, kappa]
    simp_rw [mul_comm (Real.sqrt (∑ a, AQ _ a ^ 2))]
    exact formL_bound_gen _ _ _ _ (fun i => (norm_comb_on AK e he i).le)
      (fun i => (norm_comb_on AQ e he i).le) y

end Odesky
