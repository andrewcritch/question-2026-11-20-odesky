import OdeskyLean.Congruence

/-!
# The profile does not change when `Q` and `K` are scaled together

* `eigenvalues_smul`: for a symmetric map `A` and `s > 0`, the sorted eigenvalues of
  `s • A` are `s` times those of `A`.
* `gprof_smul`: for `c ≠ 0`, the profile and the relation-(1) error of `(c q, c k)`
  equal those of `(q, k)`. With `c = √N`, this links the ensemble, whose entries
  are scaled by `1/√N`, to the question's unscaled Gaussian model.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The number of sorted eigenvalues equal to `c` is the dimension of the `c`-eigenspace. -/
private lemma card_eig_eq_finrank {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric) (c : ℝ) :
    (univ.filter (fun i => hA.eigenvalues finrank_euclideanSpace_fin i = c)).card =
      Module.finrank ℝ (Module.End.eigenspace A c) := by
  by_cases h : Module.End.HasEigenvalue A c
  · simpa using hA.card_filter_eigenvalues_eq finrank_euclideanSpace_fin h
  · have hbot : Module.End.eigenspace A c = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hne
      exact h (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hne⟩)
    rw [hbot, finrank_bot, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    apply h
    rw [← hi]
    exact hA.hasEigenvalue_eigenvalues finrank_euclideanSpace_fin i

private lemma eigenspace_smul (A : V →ₗ[ℝ] V) {s : ℝ} (hs : s ≠ 0) (c : ℝ) :
    Module.End.eigenspace (s • A) c = Module.End.eigenspace A (c / s) := by
  ext x
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, LinearMap.smul_apply]
  constructor
  · intro h
    have : A x = s⁻¹ • (s • A x) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [this, h, smul_smul, div_eq_inv_mul]
  · intro h
    rw [h, smul_smul, mul_div_cancel₀ c hs]

theorem eigenvalues_smul {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric) {s : ℝ} (hs : 0 < s)
    (hsA : (s • A).IsSymmetric) :
    hsA.eigenvalues finrank_euclideanSpace_fin =
      fun i => s * hA.eigenvalues finrank_euclideanSpace_fin i := by
  have hm : Multiset.map (hsA.eigenvalues finrank_euclideanSpace_fin) univ.val =
      Multiset.map (fun i => s * hA.eigenvalues finrank_euclideanSpace_fin i) univ.val := by
    ext c
    rw [Multiset.count_map, Multiset.count_map]
    have e1 := card_eig_eq_finrank hsA c
    have e2 := card_eig_eq_finrank hA (c / s)
    rw [eigenspace_smul A hs.ne' c, ← e2] at e1
    have hfilt : (univ.filter (fun i => s * hA.eigenvalues finrank_euclideanSpace_fin i = c)) =
        univ.filter (fun i => hA.eigenvalues finrank_euclideanSpace_fin i = c / s) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; rw [← h, mul_div_cancel_left₀ _ hs.ne']
      · intro h; rw [h, mul_div_cancel₀ c hs.ne']
    rw [← hfilt] at e1
    simp only [Finset.card, Finset.filter_val] at e1
    simpa only [eq_comm] using e1
  have hanti : Antitone (fun i => s * hA.eigenvalues finrank_euclideanSpace_fin i) :=
    fun i j hij => mul_le_mul_of_nonneg_left
      (hA.eigenvalues_antitone finrank_euclideanSpace_fin hij) hs.le
  apply List.ofFn_injective
  apply List.Perm.eq_of_pairwise'
    (hsA.eigenvalues_antitone finrank_euclideanSpace_fin).sortedGE_ofFn.pairwise
    hanti.sortedGE_ofFn.pairwise
  apply Multiset.coe_eq_coe.mp
  simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using hm

private lemma formL_smul (c : ℝ) (q k : Fin n → V) :
    formL (fun i => c • q i) (fun i => c • k i) = (c ^ 2) • formL q k := by
  ext1 x
  simp only [formL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [inner_smul_left, smul_smul]; ring_nf

private lemma formLt_smul (c : ℝ) (q k : Fin n → V) :
    formLt (fun i => c • q i) (fun i => c • k i) = (c ^ 2) • formLt q k := by
  ext1 x
  simp only [formLt, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [inner_smul_left, smul_smul]; ring_nf

private lemma formS_smul (c : ℝ) (q k : Fin n → V) :
    formS (fun i => c • q i) (fun i => c • k i) = (c ^ 2) • formS q k := by
  simp only [formS, formL_smul, formLt_smul, smul_add, smul_comm (c ^ 2) (1 / 2 : ℝ)]

private lemma formT_smul (c : ℝ) (q k : Fin n → V) :
    formT (fun i => c • q i) (fun i => c • k i) = (c ^ 2) • formT q k := by
  simp only [formT, formL_smul, formLt_smul, ← smul_sub, smul_comm (c ^ 2) (1 / 2 : ℝ)]

private lemma eigS_smul {c : ℝ} (hc : c ≠ 0) (q k : Fin n → V) :
    eigS (fun i => c • q i) (fun i => c • k i) = fun j => c ^ 2 * eigS q k j := by
  have hs : 0 < c ^ 2 := by positivity
  have hsym : ((c ^ 2) • formS q k).IsSymmetric := by
    rw [← formS_smul]; exact formS_isSymmetric _ _
  unfold eigS
  have h := eigenvalues_smul (formS_isSymmetric q k) hs hsym
  rw [← h]
  congr 1
  · exact formS_smul c q k

private lemma eigT2_smul {c : ℝ} (hc : c ≠ 0) (q k : Fin n → V) :
    eigT2 (fun i => c • q i) (fun i => c • k i) = fun j => c ^ 4 * eigT2 q k j := by
  have hs : 0 < c ^ 4 := by positivity
  have he : -(formT (fun i => c • q i) (fun i => c • k i) ∘ₗ
      formT (fun i => c • q i) (fun i => c • k i)) =
      (c ^ 4) • (-(formT q k ∘ₗ formT q k)) := by
    rw [formT_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, smul_neg]; ring_nf
  have hsym : ((c ^ 4) • (-(formT q k ∘ₗ formT q k))).IsSymmetric := by
    rw [← he]; exact negTsq_isSymmetric _ _
  unfold eigT2
  have h := eigenvalues_smul (negTsq_isSymmetric q k) hs hsym
  rw [← h]
  congr 1

private lemma eigAt_smul (s : ℝ) (v : Fin N → ℝ) (j : ℕ) :
    eigAt (fun i => s * v i) j = s * eigAt v j := by
  unfold eigAt; split_ifs <;> simp

private lemma max_mul_zero {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : max (s * x) 0 = s * max x 0 := by
  rw [← mul_zero s, ← mul_max_of_nonneg _ _ hs, mul_zero]

theorem gprof_smul {c : ℝ} (hc : c ≠ 0) (q k : Fin n → V) :
    gA (fun i => c • q i) (fun i => c • k i) = gA q k ∧
    gB (fun i => c • q i) (fun i => c • k i) = gB q k ∧
    gC (fun i => c • q i) (fun i => c • k i) = gC q k ∧
    gD (fun i => c • q i) (fun i => c • k i) = gD q k ∧
    gErr (fun i => c • q i) (fun i => c • k i) = gErr q k := by
  have hs : 0 < c ^ 2 := by positivity
  have hs4 : (c ^ 2) ^ 2 ≠ 0 := by positivity
  have hP : lamP (fun i => c • q i) (fun i => c • k i) = fun j => c ^ 2 * lamP q k j := by
    funext j; simp only [lamP, eigS_smul hc, eigAt_smul, max_mul_zero hs.le]
  have hM : lamM (fun i => c • q i) (fun i => c • k i) = fun j => c ^ 2 * lamM q k j := by
    funext j
    simp only [lamM, eigS_smul hc, eigAt_smul, ← mul_neg, max_mul_zero hs.le]
  have hT : sigT (fun i => c • q i) (fun i => c • k i) = fun j => c ^ 2 * sigT q k j := by
    funext j
    simp only [sigT, eigT2_smul hc, eigAt_smul]
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, max_mul_zero (by positivity), Real.sqrt_mul
      (by positivity), Real.sqrt_sq hs.le]
  have hL : frobL (fun i => c • q i) (fun i => c • k i) = (c ^ 2) ^ 2 * frobL q k := by
    simp only [frobL, inner_smul_left, inner_smul_right, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
  have hTT : frobT (fun i => c • q i) (fun i => c • k i) = (c ^ 2) ^ 2 * frobT q k := by
    simp only [frobT, hL, inner_smul_left, inner_smul_right, conj_trivial]
    rw [show ∑ i, ∑ j, c * (c * ⟪k i, q j⟫) * (c * (c * ⟪q i, k j⟫)) =
        (c ^ 2) ^ 2 * ∑ i, ∑ j, ⟪k i, q j⟫ * ⟪q i, k j⟫ by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [gA, hL, hTT]; rw [mul_div_mul_left _ _ hs4]
  · simp only [gB, hL, hP, hM]
    rw [show ∑ j, c ^ 2 * lamP q k j * (c ^ 2 * lamM q k j) =
        (c ^ 2) ^ 2 * ∑ j, lamP q k j * lamM q k j by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring]
    rw [mul_left_comm, mul_div_mul_left _ _ hs4]
  · simp only [gC, hL, hP, hM, ← mul_sub, max_mul_zero hs.le, mul_pow]
    rw [← Finset.mul_sum, mul_div_mul_left _ _ hs4]
  · simp only [gD, hL, hP, hM, ← mul_sub, max_mul_zero hs.le, mul_pow]
    rw [← Finset.mul_sum, mul_div_mul_left _ _ hs4]
  · simp only [gErr, hP, hM, hT]
    have hsq : ∀ j, Real.sqrt (c ^ 2 * lamP q k j * (c ^ 2 * lamM q k j)) =
        c ^ 2 * Real.sqrt (lamP q k j * lamM q k j) := by
      intro j
      rw [show c ^ 2 * lamP q k j * (c ^ 2 * lamM q k j) =
          (c ^ 2) ^ 2 * (lamP q k j * lamM q k j) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
    simp only [hsq, ← mul_sub, mul_pow]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), mul_div_mul_left _ _ (by positivity)]

end Odesky
