import OdeskyLean.Geometry
import OdeskyLean.Rearrangement

/-!
# Layer 5 (gap G1): from eigenvector equations to spectra and norms

For a sum of rank-one forms on orthogonal planes on `ℝᴺ` with `2n ≤ N` and every tilt
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
  apply List.ofFn_injective
  apply List.Perm.eq_of_pairwise' hℓ.sortedGE_ofFn.pairwise hσ.sortedGE_ofFn.pairwise
  apply Multiset.coe_eq_coe.mp
  simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using
    hm.trans (by
      simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using
        (Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm α)).symm)

namespace OrthoBlocks

variable (B : OrthoBlocks n N)

private theorem charpoly_rank_one_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → V) (φ : ι → V →ₗ[ℝ] ℝ) (d : ι → ℝ)
    (h : ∀ i j, φ i (w j) = if i = j then d i else 0)
    (hN : Fintype.card ι ≤ N) :
    (∑ i, (φ i).smulRight (w i)).charpoly =
      (∏ i, (X - C (d i))) * X ^ (N - Fintype.card ι) := by
  classical
  let a : (ι → ℝ) →ₗ[ℝ] V :=
    ∑ i, (LinearMap.proj i).smulRight (w i)
  let c : V →ₗ[ℝ] (ι → ℝ) := LinearMap.pi φ
  let b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  let e := Pi.basisFun ℝ ι
  have hac : a ∘ₗ c = ∑ i, (φ i).smulRight (w i) := by
    ext x
    simp [a, c, LinearMap.sum_apply]
  have hca : LinearMap.toMatrix e e (c ∘ₗ a) = Matrix.diagonal d := by
    ext i j
    simp [e, a, c, h, Matrix.diagonal_apply]
  rw [← hac, ← LinearMap.charpoly_toMatrix _ b,
    LinearMap.toMatrix_comp b e b]
  rw [Matrix.charpoly_mul_comm_of_le _ _ (by simpa using hN)]
  rw [← LinearMap.toMatrix_comp e b e, hca, Matrix.charpoly_diagonal]
  simp [mul_comm]

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
  simp [Llin, L, LinearMap.sum_apply, smul_smul]

theorem Slin_apply (x : V) : B.Slin x = B.S x := by
  simp [Slin, S, B.Llin_apply, Ltlin, Lt, LinearMap.sum_apply, smul_smul]

theorem Tlin_apply (x : V) : B.Tlin x = B.T x := by
  simp [Tlin, T, B.Llin_apply, Ltlin, Lt, LinearMap.sum_apply, smul_smul]

private lemma inner_uu (i j : Fin n) :
    ⟪B.u i, B.u j⟫ = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j; simp [B.u_unit]
  · exact B.uu i j h

private lemma inner_vv (i j : Fin n) :
    ⟪B.v i, B.v j⟫ = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j; simp [B.v_unit]
  · exact B.vv i j h

private lemma inner_uv (i j : Fin n) :
    ⟪B.u i, B.v j⟫ = if i = j then B.t i else 0 := by
  split_ifs with h
  · subst j; rfl
  · exact B.uv i j h

private lemma inner_vu (i j : Fin n) :
    ⟪B.v i, B.u j⟫ = if i = j then B.t i else 0 := by
  rw [real_inner_comm, B.inner_uv]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

private noncomputable def frameVec : Fin n ⊕ Fin n → V :=
  Sum.elim (fun i => B.u i + B.v i) (fun i => B.u i - B.v i)

private noncomputable def frameS : Fin n ⊕ Fin n → V →ₗ[ℝ] ℝ :=
  Sum.elim
    (fun i => (B.s i / 4) • (innerSL ℝ (B.u i + B.v i)).toLinearMap)
    (fun i => (-B.s i / 4) • (innerSL ℝ (B.u i - B.v i)).toLinearMap)

private noncomputable def frameT : Fin n ⊕ Fin n → V →ₗ[ℝ] ℝ :=
  Sum.elim
    (fun i => (-B.s i / 4) • (innerSL ℝ (B.u i - B.v i)).toLinearMap)
    (fun i => (B.s i / 4) • (innerSL ℝ (B.u i + B.v i)).toLinearMap)

private lemma frameS_entry (i j : Fin n ⊕ Fin n) :
    B.frameS i (B.frameVec j) =
      if i = j then Sum.elim B.α (fun k => -B.β k) i else 0 := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [frameS, frameVec, Sum.elim_inl, Sum.elim_inr,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      smul_eq_mul, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      B.inner_uu, B.inner_uv, B.inner_vu, B.inner_vv, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, if_false]
  all_goals split_ifs <;> simp_all [α, β] <;> ring_nf <;> simp

private lemma Slin_frame : B.Slin = ∑ i, (B.frameS i).smulRight (B.frameVec i) := by
  apply LinearMap.ext
  intro x
  rw [B.Slin_apply]
  rw [LinearMap.sum_apply]
  simp only [Fintype.sum_sum_type, frameS, frameVec,
    Sum.elim_inl, Sum.elim_inr, LinearMap.smulRight_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
  simp only [S, L, Lt, Finset.smul_sum, ← Finset.sum_add_distrib,
    inner_add_left, inner_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  module

private lemma Tlin_frame : B.Tlin = ∑ i, (B.frameT i).smulRight (B.frameVec i) := by
  apply LinearMap.ext
  intro x
  rw [B.Tlin_apply]
  rw [LinearMap.sum_apply]
  simp only [Fintype.sum_sum_type, frameT, frameVec,
    Sum.elim_inl, Sum.elim_inr, LinearMap.smulRight_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
  simp only [T, L, Lt, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, inner_add_left, inner_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  module

private lemma frameNegTT_entry (i j : Fin n ⊕ Fin n) :
    (-(B.frameT i ∘ₗ B.Tlin)) (B.frameVec j) =
      if i = j then Sum.elim (fun k => B.α k * B.β k)
        (fun k => B.α k * B.β k) i else 0 := by
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, frameVec,
      Sum.elim_inl, Sum.elim_inr, B.Tlin_apply, B.T_add, B.T_sub]
    simp only [frameT, Sum.elim_inl, Sum.elim_inr, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_smul_right,
      smul_eq_mul, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      B.inner_uu, B.inner_uv, B.inner_vu, B.inner_vv, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, if_false]
    split_ifs <;> simp_all [α, β]
    all_goals ring_nf
    all_goals simp

private lemma negTT_frame : -(B.Tlin ∘ₗ B.Tlin) =
    ∑ i, (-(B.frameT i ∘ₗ B.Tlin)).smulRight (B.frameVec i) := by
  apply LinearMap.ext
  intro x
  change -(B.Tlin (B.Tlin x)) = _
  nth_rw 1 [B.Tlin_frame]
  simp [LinearMap.sum_apply, ← Finset.sum_neg_distrib, add_comm]

/-- Characteristic polynomial of `S`. -/
theorem charpoly_S (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly =
      (∏ i, (X - C (B.α i)) * (X + C (B.β i))) * X ^ (N - 2 * n) := by
  rw [B.Slin_frame]
  rw [charpoly_rank_one_sum _ _ _ B.frameS_entry (by simpa [two_mul] using hN)]
  simp [Fintype.prod_sum_type, sub_neg_eq_add, Finset.prod_mul_distrib, two_mul]

/-- Characteristic polynomial of `TᵀT = -T²`. -/
theorem charpoly_neg_T_sq (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    (-(B.Tlin ∘ₗ B.Tlin)).charpoly =
      (∏ i, (X - C (B.α i * B.β i)) ^ 2) * X ^ (N - 2 * n) := by
  rw [B.negTT_frame]
  rw [charpoly_rank_one_sum _ _ _ B.frameNegTT_entry (by simpa [two_mul] using hN)]
  simp [Fintype.prod_sum_type, Finset.prod_mul_distrib, pow_two, two_mul]

private lemma prod_linear_ne_zero {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i, (X - C (f i))) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (monic_X_sub_C (f i)).ne_zero)

private lemma roots_prod_linear {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i, (X - C (f i))).roots = Multiset.map f univ.val := by
  rw [Polynomial.roots_prod _ _ (prod_linear_ne_zero f)]
  simp only [roots_X_sub_C, Multiset.bind_singleton]

private lemma roots_S_all (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly.roots = Multiset.map B.α univ.val +
      Multiset.map (fun i => -B.β i) univ.val + (N - 2 * n) • ({0} : Multiset ℝ) := by
  rw [B.charpoly_S hT hN, Finset.prod_mul_distrib]
  have he : ∀ i, X + C (B.β i) = X - C (-B.β i) := by intro i; simp
  simp_rw [he]
  rw [roots_mul (mul_ne_zero (mul_ne_zero (prod_linear_ne_zero B.α)
    (prod_linear_ne_zero (fun i => -B.β i))) (pow_ne_zero _ X_ne_zero))]
  rw [roots_mul (mul_ne_zero (prod_linear_ne_zero B.α)
    (prod_linear_ne_zero (fun i => -B.β i)))]
  rw [roots_prod_linear, roots_prod_linear, roots_X_pow]

/-- The positive eigenvalues of `S`, with multiplicity, are the `α_i`. -/
theorem roots_S_pos (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly.roots.filter (fun x => 0 < x) = Multiset.map B.α univ.val := by
  rw [B.roots_S_all hT hN]
  simp only [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    lt_self_iff_false, ↓reduceIte, Multiset.empty_eq_zero, smul_zero, add_zero]
  rw [Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr, add_zero]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact not_lt_of_ge (le_of_lt (neg_neg_of_pos (B.β_pos hT i)))
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact B.α_pos hT i

/-- The negative eigenvalues of `S`, with multiplicity, are the `-β_i`. -/
theorem roots_S_neg (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    B.Slin.charpoly.roots.filter (fun x => x < 0) =
      Multiset.map (fun i => -B.β i) univ.val := by
  rw [B.roots_S_all hT hN]
  simp only [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    lt_self_iff_false, ↓reduceIte, Multiset.empty_eq_zero, smul_zero, add_zero]
  rw [Multiset.filter_eq_nil.mpr, zero_add, Multiset.filter_eq_self.mpr]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact neg_neg_of_pos (B.β_pos hT i)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact not_lt_of_ge (le_of_lt (B.α_pos hT i))

/-- The nonzero eigenvalues of `TᵀT`, with multiplicity, are the `α_i β_i`,
each twice. -/
theorem roots_neg_T_sq_pos (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    (-(B.Tlin ∘ₗ B.Tlin)).charpoly.roots.filter (fun x => 0 < x) =
      2 • Multiset.map (fun i => B.α i * B.β i) univ.val := by
  rw [B.charpoly_neg_T_sq hT hN, Finset.prod_pow]
  rw [roots_mul (mul_ne_zero (pow_ne_zero _
    (prod_linear_ne_zero (fun i => B.α i * B.β i))) (pow_ne_zero _ X_ne_zero))]
  rw [roots_pow, roots_prod_linear, roots_X_pow]
  simp only [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    lt_self_iff_false, ↓reduceIte, Multiset.empty_eq_zero, smul_zero, add_zero]
  congr 1
  apply Multiset.filter_eq_self.mpr
  intro x hx
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
  exact mul_pos (B.α_pos hT i) (B.β_pos hT i)

private lemma inner_LL (x : V) :
    ⟪B.L x, B.L x⟫ = ∑ i, B.s i ^ 2 * ⟪B.v i, x⟫ * ⟪B.v i, x⟫ := by
  simp only [L, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    B.inner_uu]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma inner_LtLt (x : V) :
    ⟪B.Lt x, B.Lt x⟫ = ∑ i, B.s i ^ 2 * ⟪B.u i, x⟫ * ⟪B.u i, x⟫ := by
  simp only [Lt, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    B.inner_vv]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma inner_LLt (x : V) :
    ⟪B.L x, B.Lt x⟫ = ∑ i, (B.s i ^ 2 * B.t i) * ⟪B.v i, x⟫ * ⟪B.u i, x⟫ := by
  simp only [L, Lt, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    B.inner_uv]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma parseval_sum (b : OrthonormalBasis (Fin N) ℝ V)
    (a : Fin n → ℝ) (v w : Fin n → V) :
    ∑ k, ∑ i, a i * ⟪v i, b k⟫ * ⟪w i, b k⟫ =
      ∑ i, a i * ⟪v i, w i⟫ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hc (k : Fin N) : ⟪w i, b k⟫ = ⟪b k, w i⟫ := real_inner_comm _ _
  simp_rw [mul_assoc, hc]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

private lemma sum_inner_LL (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ⟪B.L (b k), B.L (b k)⟫ = ∑ i, B.s i ^ 2 := by
  simp_rw [B.inner_LL]
  rw [parseval_sum]
  simp [B.v_unit]

private lemma sum_inner_LtLt (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ⟪B.Lt (b k), B.Lt (b k)⟫ = ∑ i, B.s i ^ 2 := by
  simp_rw [B.inner_LtLt]
  rw [parseval_sum]
  simp [B.u_unit]

private lemma sum_inner_LLt (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ⟪B.L (b k), B.Lt (b k)⟫ = ∑ i, B.s i ^ 2 * B.t i ^ 2 := by
  simp_rw [B.inner_LLt]
  rw [parseval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [B.inner_vu, if_pos rfl]
  ring

/-- `‖L‖² = ∑ s_i²` in any orthonormal basis. -/
theorem frob_L (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.L (b k)‖ ^ 2 = ∑ i, B.s i ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using B.sum_inner_LL b

/-- `‖S‖² = ∑ (α_i² + β_i²)` in any orthonormal basis. -/
theorem frob_S (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.S (b k)‖ ^ 2 = ∑ i, (B.α i ^ 2 + B.β i ^ 2) := by
  have hc (k : Fin N) : ⟪B.Lt (b k), B.L (b k)⟫ =
      ⟪B.L (b k), B.Lt (b k)⟫ := real_inner_comm _ _
  simp_rw [← real_inner_self_eq_norm_sq, S, real_inner_smul_left,
    real_inner_smul_right, inner_add_left, inner_add_right, hc]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [B.sum_inner_LL b, B.sum_inner_LtLt b, B.sum_inner_LLt b]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [α, β]
  ring

/-- `‖T‖² = 2 ∑ α_i β_i` in any orthonormal basis. -/
theorem frob_T (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ k, ‖B.T (b k)‖ ^ 2 = 2 * ∑ i, B.α i * B.β i := by
  have hc (k : Fin N) : ⟪B.Lt (b k), B.L (b k)⟫ =
      ⟪B.L (b k), B.Lt (b k)⟫ := real_inner_comm _ _
  simp_rw [← real_inner_self_eq_norm_sq, T, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right, hc]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [B.sum_inner_LL b, B.sum_inner_LtLt b, B.sum_inner_LLt b]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [α, β]
  ring

end OrthoBlocks

end Odesky
