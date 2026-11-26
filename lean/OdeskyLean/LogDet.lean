import OdeskyLean.GenProfile

/-!
# The log-determinant identity of §1

Rows `q_i, k_i ∈ ℝᴺ` (`L x = ∑ ⟪q_i, x⟫ k_i`, i.e., `L = Kᵀ Q`), with the `2n` rows
linearly independent and `2n ≤ N`. Let `G` be their `2n × 2n` Gram matrix.

* `lists_pos`: every `λ₊,j`, `λ₋,j` and `σ(T)_j` is positive.
* `prod_lam_eq_det`: `∏ λ₊,j λ₋,j = det G / 4ⁿ`.
* `prod_sig_eq_det`: `∏ σ(T)_j² = det G / 4ⁿ`.
* `logdet_identity`: hence `∑ log σ(T)_j = ½ ∑ log(λ₊,j λ₋,j)`.

Proof idea: `2S = Fᵀ J F` and `2T = Fᵀ Ω F` with `F` the stacked rows,
`J = [[0, I], [I, 0]]`, `Ω = [[0, -I], [I, 0]]`; the nonzero spectra of `2S` and `2T`
are those of `J G` and `Ω G` (`Matrix.charpoly_mul_comm_of_le`-type facts), and
`|det J| = det Ω = 1`.
-/

open RealInnerProductSpace Finset

namespace Odesky


section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private def spanE {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (s : Set (Fin d)))

omit [FiniteDimensional ℝ E] in
private lemma spanE_dim {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) : Module.finrank ℝ (spanE b s) = s.card := by
  classical
  have h := finrank_span_eq_card (b.toBasis.linearIndependent.comp
    (fun i : s => (i : Fin d)) Subtype.val_injective)
  have he : Set.range (fun i : s => b (i : Fin d)) = b '' (s : Set (Fin d)) := by
    ext x
    simp
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => b (i : Fin d)))) = _ at h
  rw [he] at h
  simpa [spanE] using h

omit [FiniteDimensional ℝ E] in
private lemma spanE_coord {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) {x : E} (hx : x ∈ spanE b s)
    {i : Fin d} (hi : i ∉ s) : b.repr x i = 0 := by
  classical
  have h := b.toBasis.repr_support_subset_of_mem_span (s : Set (Fin d)) hx
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  simpa using hz

private lemma quadE {d : ℕ} (hd : Module.finrank ℝ E = d)
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (x : E) :
    ⟪A x, x⟫ = ∑ i, hA.eigenvalues hd i * ((hA.eigenvectorBasis hd).repr x i) ^ 2 := by
  rw [← (hA.eigenvectorBasis hd).sum_inner_mul_inner (A x) x]
  apply Finset.sum_congr rfl
  intro i _
  have he : ⟪A x, (hA.eigenvectorBasis hd) i⟫ =
      hA.eigenvalues hd i * (hA.eigenvectorBasis hd).repr x i := by
    calc
      _ = ⟪(hA.eigenvectorBasis hd) i, A x⟫ := real_inner_comm _ _
      _ = (hA.eigenvectorBasis hd).repr (A x) i :=
        ((hA.eigenvectorBasis hd).repr_apply_apply _ _).symm
      _ = _ := hA.eigenvectorBasis_apply_self_apply hd x i
  rw [he, ← OrthonormalBasis.repr_apply_apply]
  ring

omit [FiniteDimensional ℝ E] in
private lemma normE {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
  simpa [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
    (b.sum_sq_norm_inner_right x).symm

/-- Two subspaces whose dimensions sum past `d` meet nontrivially. -/
private lemma exists_common {d : ℕ} (hd : Module.finrank ℝ E = d) (U V' : Submodule ℝ E)
    (h : d < Module.finrank ℝ U + Module.finrank ℝ V') : ∃ x ∈ U, x ∈ V' ∧ x ≠ 0 := by
  have hne : U ⊓ V' ≠ ⊥ := by
    intro hh
    have he := Submodule.finrank_sup_add_finrank_inf_eq U V'
    have hl := Submodule.finrank_le (U ⊔ V')
    rw [hh, finrank_bot] at he
    rw [hd] at hl
    omega
  obtain ⟨x, hx, hx0⟩ := (U ⊓ V').ne_bot_iff.mp hne
  exact ⟨x, hx.1, hx.2, hx0⟩

/-- Min-max, positive side. -/
private lemma minmax_pos {d : ℕ} (hd : Module.finrank ℝ E = d) {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (U : Submodule ℝ E)
    (hpos : ∀ x ∈ U, x ≠ 0 → 0 < ⟪A x, x⟫) (k : Fin d)
    (hk : k.val + 1 ≤ Module.finrank ℝ U) : 0 < hA.eigenvalues hd k := by
  classical
  by_contra hneg
  push_neg at hneg
  let P := spanE (hA.eigenvectorBasis hd) (Finset.Ici k)
  have hP : Module.finrank ℝ P = d - k.val := by
    simpa [P, Fin.card_Ici] using spanE_dim (hA.eigenvectorBasis hd) (Finset.Ici k)
  obtain ⟨x, hxU, hxP, hx0⟩ := exists_common hd U P (by have := k.isLt; omega)
  have h1 := hpos x hxU hx0
  have h2 : ⟪A x, x⟫ ≤ 0 := by
    rw [quadE hd hA]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : k ≤ i
    · exact mul_nonpos_of_nonpos_of_nonneg ((hA.eigenvalues_antitone hd hi).trans hneg)
        (sq_nonneg _)
    · rw [spanE_coord _ (Finset.Ici k) hxP (by simpa using hi)]
      simp
  linarith

/-- Min-max, negative side. -/
private lemma minmax_neg {d : ℕ} (hd : Module.finrank ℝ E = d) {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (U : Submodule ℝ E)
    (hneg : ∀ x ∈ U, x ≠ 0 → ⟪A x, x⟫ < 0) (k : Fin d)
    (hk : d ≤ k.val + Module.finrank ℝ U) : hA.eigenvalues hd k < 0 := by
  classical
  by_contra hpos
  push_neg at hpos
  let P := spanE (hA.eigenvectorBasis hd) (Finset.Iic k)
  have hP : Module.finrank ℝ P = k.val + 1 := by
    simpa [P, Fin.card_Iic] using spanE_dim (hA.eigenvectorBasis hd) (Finset.Iic k)
  obtain ⟨x, hxU, hxP, hx0⟩ := exists_common hd U P (by omega)
  have h1 := hneg x hxU hx0
  have h2 : 0 ≤ ⟪A x, x⟫ := by
    rw [quadE hd hA]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ≤ k
    · exact mul_nonneg (hpos.trans (hA.eigenvalues_antitone hd hi)) (sq_nonneg _)
    · rw [spanE_coord _ (Finset.Iic k) hxP (by simpa using hi)]
      simp
  linarith

omit [FiniteDimensional ℝ E] in
/-- The determinant of a restriction, from coefficients in a spanning independent family. -/
private lemma det_restrict_coeffs {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → E}
    (hli : LinearIndependent ℝ f) (A : E →ₗ[ℝ] E)
    (hW : ∀ x ∈ Submodule.span ℝ (Set.range f), A x ∈ Submodule.span ℝ (Set.range f))
    (M : Matrix ι ι ℝ) (hM : ∀ b, A (f b) = ∑ a, M a b • f a) :
    LinearMap.det (A.restrict hW) = M.det := by
  let bW := Module.Basis.span hli
  rw [← LinearMap.det_toMatrix bW]
  congr 1
  ext a b
  rw [LinearMap.toMatrix_apply]
  have : A.restrict hW (bW b) = ∑ a, M a b • bW a := by
    apply Subtype.ext
    simp [bW, Module.Basis.span_apply, LinearMap.restrict_apply, hM]
  rw [this, Module.Basis.repr_sum_self]

/-- The determinant of a restriction, from eigenvectors that span the subspace. -/
private lemma det_restrict_eigen {d : ℕ} (hd : Module.finrank ℝ E = d) {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (W : Submodule ℝ E) (hW : ∀ x ∈ W, A x ∈ W)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : ι → Fin d)
    (hg : Function.Injective g)
    (hcard : Fintype.card ι = Module.finrank ℝ W)
    (hmem : ∀ a, hA.eigenvectorBasis hd (g a) ∈ W) :
    LinearMap.det (A.restrict hW) = ∏ a, hA.eigenvalues hd (g a) := by
  let v : ι → W := fun a => ⟨hA.eigenvectorBasis hd (g a), hmem a⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp W.subtype
    exact (hA.eigenvectorBasis hd).toBasis.linearIndependent.comp g hg
  let bW := basisOfLinearIndependentOfCardEqFinrank hv hcard
  rw [← LinearMap.det_toMatrix bW]
  have : LinearMap.toMatrix bW bW (A.restrict hW) =
      Matrix.diagonal (fun a => hA.eigenvalues hd (g a)) := by
    ext a b
    rw [LinearMap.toMatrix_apply]
    have h1 : A.restrict hW (bW b) = hA.eigenvalues hd (g b) • bW b := by
      apply Subtype.ext
      simp [bW, v, LinearMap.restrict_apply, hA.apply_eigenvectorBasis]
    rw [h1, map_smul, bW.repr_self]
    simp only [Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · have hba : ¬ b = a := fun h => hab h.symm
      simp [hab, hba]
  rw [this, Matrix.det_diagonal]

/-- An injective skew map on a finite-dimensional space forces even dimension. -/
private lemma even_of_skew {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : F →ₗ[ℝ] F) (hT : ∀ x y, ⟪T x, y⟫ = -⟪x, T y⟫)
    (hinj : ∀ x, T x = 0 → x = 0) : Even (Module.finrank ℝ F) := by
  have hadj : LinearMap.adjoint T = -T := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [LinearMap.neg_apply, inner_neg_left, hT]
    ring
  let ob := stdOrthonormalBasis ℝ F
  have hdet : LinearMap.det (LinearMap.adjoint T) = LinearMap.det T := by
    rw [← LinearMap.det_toMatrix ob.toBasis, ← LinearMap.det_toMatrix ob.toBasis,
      LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  have hneg : LinearMap.det (-T) = (-1) ^ Module.finrank ℝ F * LinearMap.det T := by
    rw [show -T = (-1 : ℝ) • T by simp, LinearMap.det_smul]
  have hu : IsUnit T := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    exact hinj
  have hne : LinearMap.det T ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det T).mp hu).ne_zero
  rw [hadj, hneg] at hdet
  have h1 : ((-1 : ℝ)) ^ Module.finrank ℝ F = 1 := by
    have := mul_right_cancel₀ hne (hdet.trans (one_mul _).symm)
    exact this
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h1

/-- The eigenvalues of `-T²`, `T` skew, come in equal pairs while positive. -/
private lemma pair_eq {d : ℕ} (hd : Module.finrank ℝ E = d) (T : E →ₗ[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫ = -⟪x, T y⟫) (hA : (-(T ∘ₗ T)).IsSymmetric)
    (j : ℕ) (hj : 2 * j + 1 < d) (hpos : 0 < hA.eigenvalues hd ⟨2 * j, by omega⟩) :
    hA.eigenvalues hd ⟨2 * j + 1, hj⟩ = hA.eigenvalues hd ⟨2 * j, by omega⟩ := by
  classical
  set A := -(T ∘ₗ T) with hAdef
  set e := hA.eigenvectorBasis hd with he
  set lam := hA.eigenvalues hd with hlam
  set μ := lam ⟨2 * j, by omega⟩ with hμ
  let s : Finset (Fin d) := Finset.univ.filter (fun i => μ ≤ lam i)
  let U := spanE e s
  have ha : ∀ v ν, A v = ν • v → μ ≤ ν → v ∈ U := by
    intro v ν hv hν
    rw [← e.sum_repr v]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : μ ≤ lam i
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, by simpa [s] using hi, rfl⟩)
    · have h1 : lam i * e.repr v i = ν * e.repr v i := by
        rw [OrthonormalBasis.repr_apply_apply]
        have := hA (e i) v
        rw [hA.apply_eigenvectorBasis, hv, inner_smul_left, inner_smul_right] at this
        simp only [conj_trivial, RCLike.ofReal_real_eq_id, id] at this
        exact this
      have hne : lam i ≠ ν := by
        intro h; apply hi; rw [h]; exact hν
      have h2 : (lam i - ν) * e.repr v i = 0 := by rw [sub_mul, h1, sub_self]
      have h3 : e.repr v i = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      rw [h3, zero_smul]
      exact Submodule.zero_mem _
  have hb : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    have hle : U ≤ U.comap T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      simp only [Finset.mem_coe, s, Finset.mem_filter] at hi
      show T (e i) ∈ U
      apply ha (T (e i)) (lam i) _ hi.2
      have hc : A (T (e i)) = T (A (e i)) := by simp [hAdef]
      rw [hc, hA.apply_eigenvectorBasis, map_smul]
      rfl
    exact hle hx
  have hq : ∀ x ∈ U, μ * ‖x‖ ^ 2 ≤ ⟪A x, x⟫ := by
    intro x hx
    rw [quadE hd hA, normE e, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : μ ≤ lam i
    · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    · rw [spanE_coord e s hx (by simpa [s] using hi)]
      simp
  let F : U →ₗ[ℝ] U := T.restrict hb
  have hF : ∀ x y, ⟪F x, y⟫ = -⟪x, F y⟫ := by
    intro x y
    simp only [Submodule.coe_inner, F, LinearMap.restrict_apply]
    exact hT _ _
  have hFinj : ∀ x, F x = 0 → x = 0 := by
    intro x hx
    have hx' : T x = 0 := by
      have := congrArg Subtype.val hx
      simpa [F, LinearMap.restrict_apply] using this
    have h1 := hq x x.2
    have h2 : A x = 0 := by simp [hAdef, hx']
    rw [h2, inner_zero_left] at h1
    have h3 : ‖(x : E)‖ ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : (x : E) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (le_antisymm h3 (sq_nonneg _))
      simpa using this
    exact Subtype.ext this
  have hev := even_of_skew F hF hFinj
  have hU : Module.finrank ℝ U = s.card := spanE_dim e s
  rw [hU] at hev
  apply le_antisymm (hA.eigenvalues_antitone hd (by simp [Fin.le_def]))
  by_contra hlt
  push_neg at hlt
  have hs : s = Finset.Iic ⟨2 * j, by omega⟩ := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hi
      by_contra hc
      push_neg at hc
      have : (⟨2 * j + 1, hj⟩ : Fin d) ≤ i := by
        rw [Fin.lt_def] at hc; rw [Fin.le_def]; simp at hc ⊢; omega
      have := hA.eigenvalues_antitone hd this
      linarith
    · intro hi
      exact hA.eigenvalues_antitone hd hi
  rw [hs, Fin.card_Iic] at hev
  simp at hev

end General

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The rows of `Q` followed by the rows of `K`. -/
def stackRows (q k : Fin n → V) : Fin n ⊕ Fin n → V := Sum.elim q k

/-- Gram matrix of the stacked rows. -/
noncomputable def gramRows (q k : Fin n → V) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => ⟪stackRows q k a, stackRows q k b⟫

/-- The sign pattern of `Ω`. -/
private def sgnA : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)

private lemma formS_exp (q k : Fin n → V) (x : V) :
    formS q k x = ∑ a, ((1 / 2) * ⟪stackRows q k (Sum.swap a), x⟫) • stackRows q k a := by
  rw [Fintype.sum_sum_type]
  simp only [formS, formL, formLt, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
    stackRows, Sum.swap_inl, Sum.swap_inr, Sum.elim_inl, Sum.elim_inr, smul_add,
    Finset.smul_sum, smul_smul]
  rw [add_comm]

private lemma formT_exp (q k : Fin n → V) (x : V) :
    formT q k x = ∑ a, ((1 / 2) * sgnA a * ⟪stackRows q k (Sum.swap a), x⟫) •
      stackRows q k a := by
  rw [Fintype.sum_sum_type]
  simp only [formT, formL, formLt, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
    stackRows, Sum.swap_inl, Sum.swap_inr, Sum.elim_inl, Sum.elim_inr, smul_sub,
    Finset.smul_sum, smul_smul, sgnA]
  rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_smul]; congr 1; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring

private lemma mem_W_of_exp (q k : Fin n → V) (c : Fin n ⊕ Fin n → ℝ) :
    ∑ a, c a • stackRows q k a ∈ Submodule.span ℝ (Set.range (stackRows q k)) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private lemma formS_mem (q k : Fin n → V) (x : V) :
    formS q k x ∈ Submodule.span ℝ (Set.range (stackRows q k)) := by
  rw [formS_exp]; exact mem_W_of_exp q k _

private lemma formT_mem (q k : Fin n → V) (x : V) :
    formT q k x ∈ Submodule.span ℝ (Set.range (stackRows q k)) := by
  rw [formT_exp]; exact mem_W_of_exp q k _

private lemma negTT_mem (q k : Fin n → V) (x : V) :
    (-(formT q k ∘ₗ formT q k)) x ∈ Submodule.span ℝ (Set.range (stackRows q k)) := by
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  exact Submodule.neg_mem _ (formT_mem q k _)

private lemma formT_skew (q k : Fin n → V) (x y : V) :
    ⟪formT q k x, y⟫ = -⟪x, formT q k y⟫ := by
  have h1 := formLt_adjoint q k x y
  have h2 := formLt_adjoint q k y x
  simp only [formT, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, conj_trivial]
  rw [real_inner_comm x (formL q k y), real_inner_comm (formLt q k x) y] at h2
  linarith

/-- Matrices of `S` and `T` in the basis of stacked rows. -/
private noncomputable def matS (q k : Fin n → V) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => (1 / 2) * ⟪stackRows q k (Sum.swap a), stackRows q k b⟫

private noncomputable def matT (q k : Fin n → V) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => (1 / 2) * sgnA a * ⟪stackRows q k (Sum.swap a), stackRows q k b⟫

private lemma matS_spec (q k : Fin n → V) (b : Fin n ⊕ Fin n) :
    formS q k (stackRows q k b) = ∑ a, matS q k a b • stackRows q k a := by
  rw [formS_exp]; rfl

private lemma matT_spec (q k : Fin n → V) (b : Fin n ⊕ Fin n) :
    formT q k (stackRows q k b) = ∑ a, matT q k a b • stackRows q k a := by
  rw [formT_exp]; rfl

private lemma matTT_spec (q k : Fin n → V) (b : Fin n ⊕ Fin n) :
    (-(formT q k ∘ₗ formT q k)) (stackRows q k b) =
      ∑ c, (-(matT q k * matT q k)) c b • stackRows q k c := by
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, matT_spec, map_sum, map_smul,
    Finset.smul_sum, smul_smul, Matrix.neg_apply, Matrix.mul_apply, neg_smul, Finset.sum_smul,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_)
  rw [mul_comm]

local notation "I1" => (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "Z0" => (0 : Matrix (Fin n) (Fin n) ℝ)

private lemma det_J : (Matrix.fromBlocks Z0 I1 I1 Z0).det = (-1) ^ n := by
  have h : Matrix.fromBlocks I1 I1 Z0 I1 *
      Matrix.fromBlocks Z0 I1 I1 Z0 = Matrix.fromBlocks I1 I1 I1 Z0 := by
    rw [Matrix.fromBlocks_multiply]; simp
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁] at h2
  simpa [Matrix.det_neg] using h2

private lemma det_Om :
    (Matrix.fromBlocks Z0 (-I1) I1 Z0).det = 1 := by
  have h : Matrix.fromBlocks I1 I1 Z0 I1 *
      Matrix.fromBlocks Z0 (-I1) I1 Z0 = Matrix.fromBlocks I1 (-I1) I1 Z0 := by
    rw [Matrix.fromBlocks_multiply]; simp
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁] at h2
  simpa using h2

private lemma det_matS (q k : Fin n → V) :
    (matS q k).det = (1 / 2) ^ (n + n) * ((-1) ^ n * (gramRows q k).det) := by
  have h : matS q k = (1 / 2 : ℝ) •
      (Matrix.fromBlocks Z0 I1 I1 Z0 * gramRows q k) := by
    ext a b
    rcases a with i | i <;>
      simp [matS, gramRows, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_smul, Matrix.det_mul, det_J]
  simp

private lemma det_matT (q k : Fin n → V) :
    (matT q k).det = (1 / 2) ^ (n + n) * (gramRows q k).det := by
  have h : matT q k = (1 / 2 : ℝ) •
      (Matrix.fromBlocks Z0 (-I1) I1 Z0 * gramRows q k) := by
    ext a b
    rcases a with i | i <;>
      simp [matT, gramRows, sgnA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_smul, Matrix.det_mul, det_Om]
  simp

private lemma exists_dual (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k)) :
    ∃ v : Fin n ⊕ Fin n → V, (∀ a, v a ∈ Submodule.span ℝ (Set.range (stackRows q k))) ∧
      ∀ a b, ⟪stackRows q k b, v a⟫ = if a = b then 1 else 0 := by
  classical
  set W := Submodule.span ℝ (Set.range (stackRows q k))
  let bW := Module.Basis.span hli
  refine ⟨fun a => ((InnerProductSpace.toDual ℝ W).symm
    (LinearMap.toContinuousLinearMap (bW.coord a)) : W), fun a => Submodule.coe_mem _, ?_⟩
  intro a b
  have hb : stackRows q k b = ((bW b : W) : V) := by simp [bW, Module.Basis.span_apply]
  rw [hb, real_inner_comm, ← Submodule.coe_inner, InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [bW.repr_self b, Finsupp.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

private lemma eq_zero_of_perp (q k : Fin n → V) {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range (stackRows q k)))
    (h : ∀ a, ⟪stackRows q k a, x⟫ = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have : ⟪∑ a, c a • stackRows q k a, ∑ a, c a • stackRows q k a⟫ = 0 := by
    rw [sum_inner]; simp only [inner_smul_left, conj_trivial, h, mul_zero, Finset.sum_const_zero]
  exact inner_self_eq_zero.mp this

private lemma quad_S (q k : Fin n → V) (x : V) :
    ⟪formS q k x, x⟫ = ∑ i, ⟪q i, x⟫ * ⟪k i, x⟫ := by
  rw [formS_exp, sum_inner, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, conj_trivial, stackRows, Sum.swap_inl, Sum.swap_inr,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-- The family `v(inl i) + ε v(inr i)`. -/
private lemma sign_family (q k : Fin n → V) (v : Fin n ⊕ Fin n → V)
    (hdual : ∀ a b, ⟪stackRows q k b, v a⟫ = if a = b then 1 else 0) (ε : ℝ)
    (c : Fin n → ℝ) (j : Fin n) :
    ⟪q j, ∑ i, c i • (v (Sum.inl i) + ε • v (Sum.inr i))⟫ = c j ∧
      ⟪k j, ∑ i, c i • (v (Sum.inl i) + ε • v (Sum.inr i))⟫ = ε * c j := by
  have hq : ∀ a, ⟪q j, v a⟫ = if a = Sum.inl j then 1 else 0 := fun a => hdual a (Sum.inl j)
  have hk : ∀ a, ⟪k j, v a⟫ = if a = Sum.inr j then 1 else 0 := fun a => hdual a (Sum.inr j)
  constructor
  · simp [inner_sum, inner_add_right, inner_smul_right, hq]
  · simp [inner_sum, inner_add_right, inner_smul_right, hk, mul_comm]

private lemma sign_span (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k)) (ε : ℝ)
    (hε : ε ≠ 0) :
    ∃ U : Submodule ℝ V, Module.finrank ℝ U = n ∧
      ∀ x ∈ U, x ≠ 0 → 0 < ε * ⟪formS q k x, x⟫ := by
  obtain ⟨v, -, hdual⟩ := exists_dual q k hli
  let w : Fin n → V := fun i => v (Sum.inl i) + ε • v (Sum.inr i)
  have hw : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := (sign_family q k v hdual ε c j).1
    simp only [w] at hc
    rw [hc, inner_zero_right] at this
    exact this.symm
  refine ⟨Submodule.span ℝ (Set.range w), by rw [finrank_span_eq_card hw, Fintype.card_fin], ?_⟩
  intro x hx hx0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hc : c ≠ 0 := by
    rintro rfl; apply hx0; simp
  obtain ⟨j0, hj0⟩ : ∃ j, c j ≠ 0 := by
    by_contra h; push_neg at h; exact hc (funext h)
  rw [quad_S]
  simp only [w]
  have hs : ∑ i, ⟪q i, ∑ i, c i • (v (Sum.inl i) + ε • v (Sum.inr i))⟫ *
      ⟪k i, ∑ i, c i • (v (Sum.inl i) + ε • v (Sum.inr i))⟫ = ε * ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(sign_family q k v hdual ε c i).1, (sign_family q k v hdual ε c i).2]
    ring
  rw [hs, ← mul_assoc, ← sq]
  apply mul_pos (by positivity)
  exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j0, Finset.mem_univ _, by positivity⟩

private lemma eigS_pos (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k))
    (i : Fin N) (hi : i.val < n) : 0 < eigS q k i := by
  obtain ⟨U, hU, hpos⟩ := sign_span q k hli 1 one_ne_zero
  unfold eigS
  exact minmax_pos finrank_euclideanSpace_fin (formS_isSymmetric q k) U
    (fun x hx hx0 => by simpa using hpos x hx hx0) i (by omega)

private lemma eigS_neg (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k))
    (i : Fin N) (hi : N ≤ i.val + n) : eigS q k i < 0 := by
  obtain ⟨U, hU, hpos⟩ := sign_span q k hli (-1) (by norm_num)
  unfold eigS
  exact minmax_neg finrank_euclideanSpace_fin (formS_isSymmetric q k) U
    (fun x hx hx0 => by have := hpos x hx hx0; linarith) i (by omega)

private lemma negTT_pos (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k)) (x : V)
    (hx : x ∈ Submodule.span ℝ (Set.range (stackRows q k))) (hx0 : x ≠ 0) :
    0 < ⟪(-(formT q k ∘ₗ formT q k)) x, x⟫ := by
  have hTx : formT q k x ≠ 0 := by
    intro h0
    apply hx0
    apply eq_zero_of_perp q k hx
    intro b
    rw [formT_exp] at h0
    have hc := Fintype.linearIndependent_iff.mp hli _ h0 (Sum.swap b)
    rw [Sum.swap_swap] at hc
    have hs : sgnA (Sum.swap b) ≠ 0 := by rcases b with i | i <;> simp [sgnA]
    rcases mul_eq_zero.mp hc with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact hs h'
    · exact h
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, inner_neg_left]
  rw [formT_skew, neg_neg]
  exact real_inner_self_pos.mpr hTx

private lemma eigT2_pos (q k : Fin n → V) (hli : LinearIndependent ℝ (stackRows q k))
    (i : Fin N) (hi : i.val < 2 * n) : 0 < eigT2 q k i := by
  unfold eigT2
  exact minmax_pos finrank_euclideanSpace_fin (negTsq_isSymmetric q k)
    (Submodule.span ℝ (Set.range (stackRows q k)))
    (fun x hx hx0 => negTT_pos q k hli x hx hx0) i
    (by rw [finrank_span_eq_card hli]; simp; omega)

theorem lists_pos (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) (j : Fin n) :
    0 < lamP q k j ∧ 0 < lamM q k j ∧ 0 < sigT q k j := by
  have hj := j.isLt
  refine ⟨?_, ?_, ?_⟩
  · unfold lamP eigAt
    rw [dif_pos (by omega : (j : ℕ) < N)]
    exact lt_max_of_lt_left (eigS_pos q k hli _ (by simp))
  · unfold lamM eigAt
    rw [dif_pos (by omega : N - 1 - (j : ℕ) < N)]
    exact lt_max_of_lt_left (neg_pos.mpr (eigS_neg q k hli _ (by simp; omega)))
  · unfold sigT eigAt
    rw [dif_pos (by omega : 2 * (j : ℕ) < N)]
    exact Real.sqrt_pos.mpr (lt_max_of_lt_left (eigT2_pos q k hli _ (by simp)))

theorem prod_lam_eq_det (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∏ j, (lamP q k j * lamM q k j) = (gramRows q k).det / 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Matrix.det_isEmpty]
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  set W := Submodule.span ℝ (Set.range (stackRows q k)) with hWdef
  have hW : ∀ x ∈ W, formS q k x ∈ W := fun x _ => formS_mem q k x
  have hS := formS_isSymmetric q k
  have hd : Module.finrank ℝ V = N := finrank_euclideanSpace_fin
  let g : Fin n ⊕ Fin n → Fin N :=
    Sum.elim (fun j => ⟨j, by omega⟩) (fun j => ⟨N - 1 - j, by omega⟩)
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) h <;> simp [g, Fin.ext_iff] at h ⊢ <;> omega
  have hcard : Fintype.card (Fin n ⊕ Fin n) = Module.finrank ℝ W := by
    rw [finrank_span_eq_card hli]
  have hmem : ∀ a, hS.eigenvectorBasis hd (g a) ∈ W := by
    intro a
    have hne : hS.eigenvalues hd (g a) ≠ 0 := by
      rcases a with j | j
      · exact (eigS_pos q k hli _ (by simp [g])).ne'
      · exact (eigS_neg q k hli _ (by simp [g]; omega)).ne
    have h0 := hS.apply_eigenvectorBasis hd (g a)
    have h2 : hS.eigenvectorBasis hd (g a) = (hS.eigenvalues hd (g a))⁻¹ •
        formS q k (hS.eigenvectorBasis hd (g a)) := by
      rw [h0]; simp [smul_smul, hne]
    rw [h2]; exact W.smul_mem _ (formS_mem q k _)
  have h1 := det_restrict_eigen hd hS W hW g hg hcard hmem
  have h2 := det_restrict_coeffs hli (formS q k) hW (matS q k) (matS_spec q k)
  rw [h1, det_matS, Fintype.prod_sum_type] at h2
  have hP : ∀ j : Fin n, hS.eigenvalues hd (g (Sum.inl j)) = lamP q k j := by
    intro j
    have hpos : 0 < eigS q k ⟨j, by omega⟩ := eigS_pos q k hli _ (by simp)
    unfold lamP eigAt
    rw [dif_pos (by omega), max_eq_left hpos.le]
    rfl
  have hM : ∀ j : Fin n, hS.eigenvalues hd (g (Sum.inr j)) = -lamM q k j := by
    intro j
    have hneg : eigS q k ⟨N - 1 - j, by omega⟩ < 0 := eigS_neg q k hli _ (by simp; omega)
    unfold lamM eigAt
    rw [dif_pos (by omega), max_eq_left (by linarith), neg_neg]
    rfl
  simp only [hP, hM, Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h2
  rw [Finset.prod_mul_distrib]
  have h4 : (4 : ℝ) ^ n = 2 ^ (n + n) := by rw [pow_add, ← mul_pow]; norm_num
  rw [h4, eq_div_iff (by positivity)]
  have h5 : ((-1 : ℝ) ^ n) ≠ 0 := by simp
  have h6 : ((1 / 2 : ℝ) ^ (n + n)) * 2 ^ (n + n) = 1 := by
    rw [← mul_pow]; norm_num
  have := congrArg (fun t => t * 2 ^ (n + n)) h2
  simp only at this
  apply mul_left_cancel₀ h5
  calc (-1) ^ n * ((∏ j, lamP q k j) * (∏ j, lamM q k j) * 2 ^ (n + n))
      = (∏ j, lamP q k j) * ((-1) ^ n * ∏ j, lamM q k j) * 2 ^ (n + n) := by ring
    _ = (1 / 2) ^ (n + n) * ((-1) ^ n * (gramRows q k).det) * 2 ^ (n + n) := this
    _ = (-1) ^ n * (gramRows q k).det * ((1 / 2 : ℝ) ^ (n + n) * 2 ^ (n + n)) := by ring
    _ = (-1) ^ n * (gramRows q k).det := by rw [h6, mul_one]

theorem prod_sig_eq_det (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∏ j, sigT q k j ^ 2 = (gramRows q k).det / 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Matrix.det_isEmpty]
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  set W := Submodule.span ℝ (Set.range (stackRows q k)) with hWdef
  have hW : ∀ x ∈ W, (-(formT q k ∘ₗ formT q k)) x ∈ W := fun x _ => negTT_mem q k x
  have hA := negTsq_isSymmetric q k
  have hd : Module.finrank ℝ V = N := finrank_euclideanSpace_fin
  let g : Fin n ⊕ Fin n → Fin N :=
    Sum.elim (fun j => ⟨2 * j, by omega⟩) (fun j => ⟨2 * j + 1, by omega⟩)
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) h <;> simp [g, Fin.ext_iff] at h ⊢ <;> omega
  have hcard : Fintype.card (Fin n ⊕ Fin n) = Module.finrank ℝ W := by
    rw [finrank_span_eq_card hli]
  have hmem : ∀ a, hA.eigenvectorBasis hd (g a) ∈ W := by
    intro a
    have hne : hA.eigenvalues hd (g a) ≠ 0 := by
      rcases a with j | j
      · exact (eigT2_pos q k hli _ (by simp [g])).ne'
      · exact (eigT2_pos q k hli _ (by simp [g]; omega)).ne'
    have h0 := hA.apply_eigenvectorBasis hd (g a)
    have h2 : hA.eigenvectorBasis hd (g a) = (hA.eigenvalues hd (g a))⁻¹ •
        (-(formT q k ∘ₗ formT q k)) (hA.eigenvectorBasis hd (g a)) := by
      rw [h0]; simp [smul_smul, hne]
    rw [h2]; exact W.smul_mem _ (negTT_mem q k _)
  have h1 := det_restrict_eigen hd hA W hW g hg hcard hmem
  have h2 := det_restrict_coeffs hli _ hW (-(matT q k * matT q k)) (matTT_spec q k)
  rw [h1, Matrix.det_neg, Matrix.det_mul, det_matT, Fintype.prod_sum_type] at h2
  have hsig : ∀ j : Fin n, hA.eigenvalues hd (g (Sum.inl j)) = sigT q k j ^ 2 := by
    intro j
    have hpos : 0 < eigT2 q k ⟨2 * j, by omega⟩ := eigT2_pos q k hli _ (by simp)
    unfold sigT eigAt
    rw [dif_pos (by omega), max_eq_left hpos.le, Real.sq_sqrt hpos.le]
    rfl
  have hpair : ∀ j : Fin n, hA.eigenvalues hd (g (Sum.inr j)) = sigT q k j ^ 2 := by
    intro j
    rw [← hsig j]
    exact pair_eq hd (formT q k) (formT_skew q k) hA j (by omega)
      (eigT2_pos q k hli _ (by simp))
  simp only [hsig, hpair, Fintype.card_sum, Fintype.card_fin] at h2
  have hev : ((-1 : ℝ)) ^ (n + n) = 1 := by rw [← two_mul, pow_mul]; norm_num
  rw [hev, one_mul] at h2
  have hlam := prod_lam_eq_det hN q k hli
  have hnn : 0 ≤ (gramRows q k).det / 4 ^ n := by
    rw [← hlam]
    exact Finset.prod_nonneg fun j _ =>
      mul_nonneg (lists_pos hN q k hli j).1.le (lists_pos hN q k hli j).2.1.le
  have h4 : (4 : ℝ) ^ n = 2 ^ (n + n) := by rw [pow_add, ← mul_pow]; norm_num
  have h3 : (∏ j, sigT q k j ^ 2) ^ 2 = ((gramRows q k).det / 4 ^ n) ^ 2 := by
    rw [sq, h2, h4, one_div, inv_pow, div_eq_mul_inv]
    ring
  exact (pow_left_inj₀ (Finset.prod_nonneg fun j _ => sq_nonneg _) hnn two_ne_zero).mp h3

theorem logdet_identity (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∑ j, Real.log (sigT q k j) = (1 / 2) * ∑ j, Real.log (lamP q k j * lamM q k j) := by
  have hpos := lists_pos hN q k hli
  have h1 : ∑ j, Real.log (lamP q k j * lamM q k j) =
      Real.log (∏ j, (lamP q k j * lamM q k j)) :=
    (Real.log_prod fun j _ => (mul_pos (hpos j).1 (hpos j).2.1).ne').symm
  have h2 : ∑ j, Real.log (sigT q k j ^ 2) = Real.log (∏ j, sigT q k j ^ 2) :=
    (Real.log_prod fun j _ => (pow_pos (hpos j).2.2 2).ne').symm
  have h3 : ∑ j, Real.log (sigT q k j ^ 2) = 2 * ∑ j, Real.log (sigT q k j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.log_pow]; norm_num
  rw [h1, prod_lam_eq_det hN q k hli, ← prod_sig_eq_det hN q k hli, ← h2, h3]
  ring

end Odesky
