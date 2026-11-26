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

/-- Symmetric maps with eigenspaces of equal dimensions have equal sorted eigenvalues. -/
private lemma eig_eq_of_finrank {A B : V →ₗ[ℝ] V} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (h : ∀ c, Module.finrank ℝ (Module.End.eigenspace A c) =
      Module.finrank ℝ (Module.End.eigenspace B c)) :
    hA.eigenvalues finrank_euclideanSpace_fin = hB.eigenvalues finrank_euclideanSpace_fin := by
  have hm : Multiset.map (hA.eigenvalues finrank_euclideanSpace_fin) univ.val =
      Multiset.map (hB.eigenvalues finrank_euclideanSpace_fin) univ.val := by
    ext c
    rw [Multiset.count_map, Multiset.count_map]
    have e1 := card_eig_eq_finrank hA c
    have e2 := card_eig_eq_finrank hB c
    rw [h c] at e1
    rw [← e2] at e1
    simp only [Finset.card, Finset.filter_val] at e1
    simpa only [eq_comm] using e1
  apply List.ofFn_injective
  apply List.Perm.eq_of_pairwise'
    (hA.eigenvalues_antitone finrank_euclideanSpace_fin).sortedGE_ofFn.pairwise
    (hB.eigenvalues_antitone finrank_euclideanSpace_fin).sortedGE_ofFn.pairwise
  apply Multiset.coe_eq_coe.mp
  simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using hm

/-- If `A' ∘ O = O ∘ A`, the eigenspaces of `A'` are the images of those of `A`. -/
private lemma finrank_eigenspace_conj (O : V ≃ₗᵢ[ℝ] V) {A A' : V →ₗ[ℝ] V}
    (hc : ∀ x, A' (O x) = O (A x)) (c : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace A c) =
      Module.finrank ℝ (Module.End.eigenspace A' c) := by
  have he : Module.End.eigenspace A' c =
      (Module.End.eigenspace A c).map (O.toLinearEquiv : V →ₗ[ℝ] V) := by
    ext x
    rw [Submodule.mem_map_equiv, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
    constructor
    · intro hx
      apply O.injective
      have := hc (O.symm x)
      simp only [LinearIsometryEquiv.apply_symm_apply] at this
      simp [← this, hx]
    · intro hx
      have := hc (O.symm x)
      simp only [LinearIsometryEquiv.apply_symm_apply] at this
      have hx' : A (O.symm x) = c • O.symm x := by simpa using hx
      rw [this, hx', map_smul, LinearIsometryEquiv.apply_symm_apply]
  rw [he, LinearEquiv.finrank_map_eq]

private lemma formL_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) (x : V) :
    formL (fun i => O (q i)) (fun i => O (k i)) (O x) = O (formL q k x) := by
  simp [formL, LinearMap.sum_apply, map_sum, map_smul, LinearIsometryEquiv.inner_map_map]

private lemma formLt_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) (x : V) :
    formLt (fun i => O (q i)) (fun i => O (k i)) (O x) = O (formLt q k x) := by
  simp [formLt, LinearMap.sum_apply, map_sum, map_smul, LinearIsometryEquiv.inner_map_map]

private lemma formS_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) (x : V) :
    formS (fun i => O (q i)) (fun i => O (k i)) (O x) = O (formS q k x) := by
  simp [formS, formL_map, formLt_map, map_add, map_smul]

private lemma formT_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) (x : V) :
    formT (fun i => O (q i)) (fun i => O (k i)) (O x) = O (formT q k x) := by
  simp [formT, formL_map, formLt_map, map_sub, map_smul]

private lemma eigS_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    eigS (fun i => O (q i)) (fun i => O (k i)) = eigS q k := by
  unfold eigS
  exact (eig_eq_of_finrank _ _ (fun c => finrank_eigenspace_conj O (formS_map O q k) c)).symm

private lemma eigT2_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    eigT2 (fun i => O (q i)) (fun i => O (k i)) = eigT2 q k := by
  unfold eigT2
  refine (eig_eq_of_finrank _ _ (fun c => finrank_eigenspace_conj O ?_ c)).symm
  intro x
  simp [formT_map]

private lemma frobL_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    frobL (fun i => O (q i)) (fun i => O (k i)) = frobL q k := by
  simp [frobL, LinearIsometryEquiv.inner_map_map]

private lemma frobT_map (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    frobT (fun i => O (q i)) (fun i => O (k i)) = frobT q k := by
  simp [frobT, frobL, LinearIsometryEquiv.inner_map_map]


/-- Families with the same Gram matrix: some linear isometry of `V` maps one to the other. -/
private lemma exists_isometry_of_gram {ι : Type*} [Fintype ι] (w w' : ι → V)
    (hg : ∀ a b, ⟪w a, w b⟫ = ⟪w' a, w' b⟫) :
    ∃ O : V ≃ₗᵢ[ℝ] V, ∀ a, O (w a) = w' a := by
  classical
  set A : (ι → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ w with hAdef
  set B : (ι → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ w' with hBdef
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    have h2 : ‖B c‖ ^ 2 = ‖A c‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hAdef, hBdef,
        Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial, hg]
    nlinarith [norm_nonneg (B c), norm_nonneg (A c), sq_nonneg (‖B c‖ - ‖A c‖),
      sq_nonneg (‖B c‖ + ‖A c‖)]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let φ : LinearMap.range A →ₗ[ℝ] V :=
    (LinearMap.ker A).liftQ B hker ∘ₗ (A.quotKerEquivRange.symm : LinearMap.range A →ₗ[ℝ] _)
  have hφ : ∀ c, φ ⟨A c, LinearMap.mem_range_self A c⟩ = B c := by
    intro c
    simp [φ, LinearMap.quotKerEquivRange_symm_apply_image]
  let L : LinearMap.range A →ₗᵢ[ℝ] V :=
    { toLinearMap := φ
      norm_map' := by
        rintro ⟨x, c, rfl⟩
        change ‖φ ⟨A c, LinearMap.mem_range_self A c⟩‖ = ‖A c‖
        rw [hφ, hnorm] }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hwa : A (Pi.single a 1) = w a := by
    simp [hAdef, Fintype.linearCombination_apply, Pi.single_apply]
  have hwa' : B (Pi.single a 1) = w' a := by
    simp [hBdef, Fintype.linearCombination_apply, Pi.single_apply]
  have hmem : w a ∈ LinearMap.range A := ⟨_, hwa⟩
  change L.extend (w a) = w' a
  have := L.extend_apply ⟨w a, hmem⟩
  simp only at this
  rw [this]
  have hs : (⟨w a, hmem⟩ : LinearMap.range A) =
      ⟨A (Pi.single a 1), LinearMap.mem_range_self A _⟩ := Subtype.ext hwa.symm
  rw [hs]
  change φ _ = _
  rw [hφ, hwa']

theorem exists_isometry_of_same_W (u v u' v' : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) (hu' : Orthonormal ℝ u') (hv' : Orthonormal ℝ v')
    (hW : ∀ i j, ⟪u i, v j⟫ = ⟪u' i, v' j⟫) :
    ∃ O : V ≃ₗᵢ[ℝ] V, ∀ i, O (u i) = u' i ∧ O (v i) = v' i := by
  have hg : ∀ a b, ⟪Sum.elim u v a, Sum.elim u v b⟫ = ⟪Sum.elim u' v' a, Sum.elim u' v' b⟫ := by
    rintro (i | i) (j | j)
    · simp only [Sum.elim_inl]
      rw [orthonormal_iff_ite.mp hu, orthonormal_iff_ite.mp hu']
    · simp only [Sum.elim_inl, Sum.elim_inr, hW]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [real_inner_comm, hW, real_inner_comm]
    · simp only [Sum.elim_inr]
      rw [orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hv']
  obtain ⟨O, hO⟩ := exists_isometry_of_gram _ _ hg
  exact ⟨O, fun i => ⟨hO (Sum.inl i), hO (Sum.inr i)⟩⟩

theorem gprof_isometry (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    gA (fun i => O (q i)) (fun i => O (k i)) = gA q k ∧
    gB (fun i => O (q i)) (fun i => O (k i)) = gB q k ∧
    gC (fun i => O (q i)) (fun i => O (k i)) = gC q k ∧
    gD (fun i => O (q i)) (fun i => O (k i)) = gD q k ∧
    gErr (fun i => O (q i)) (fun i => O (k i)) = gErr q k := by
  have hP : lamP (fun i => O (q i)) (fun i => O (k i)) = lamP q k := by
    funext j; simp only [lamP, eigS_map]
  have hM : lamM (fun i => O (q i)) (fun i => O (k i)) = lamM q k := by
    funext j; simp only [lamM, eigS_map]
  have hT : sigT (fun i => O (q i)) (fun i => O (k i)) = sigT q k := by
    funext j; simp only [sigT, eigT2_map]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [gA, frobL_map, frobT_map]
  · simp only [gB, frobL_map, hP, hM]
  · simp only [gC, frobL_map, hP, hM]
  · simp only [gD, frobL_map, hP, hM]
  · simp only [gErr, hP, hM, hT]

theorem gprof_eq_of_same_W (σ : Fin n → ℝ) (u v u' v' : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) (hu' : Orthonormal ℝ u') (hv' : Orthonormal ℝ v')
    (hW : ∀ i j, ⟪u i, v j⟫ = ⟪u' i, v' j⟫) :
    gA (fun i => σ i • v' i) u' = gA (fun i => σ i • v i) u ∧
    gB (fun i => σ i • v' i) u' = gB (fun i => σ i • v i) u ∧
    gC (fun i => σ i • v' i) u' = gC (fun i => σ i • v i) u ∧
    gD (fun i => σ i • v' i) u' = gD (fun i => σ i • v i) u ∧
    gErr (fun i => σ i • v' i) u' = gErr (fun i => σ i • v i) u := by
  obtain ⟨O, hO⟩ := exists_isometry_of_same_W u v u' v' hu hv hu' hv' hW
  have h1 : (fun i => σ i • v' i) = fun i => O (σ i • v i) := by
    funext i; rw [map_smul, (hO i).2]
  have h2 : u' = fun i => O (u i) := by
    funext i; rw [(hO i).1]
  rw [h1, h2]
  exact gprof_isometry O _ _

end Odesky
