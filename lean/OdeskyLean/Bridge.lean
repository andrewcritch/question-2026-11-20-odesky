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


theorem gprof_of_formL_eq (q k q' k' : Fin n → V) (h : formL q k = formL q' k') :
    lamP q' k' = lamP q k ∧ lamM q' k' = lamM q k ∧ sigT q' k' = sigT q k ∧
    gA q' k' = gA q k ∧ gB q' k' = gB q k ∧ gC q' k' = gC q k ∧ gD q' k' = gD q k ∧
    gErr q' k' = gErr q k := by
  have ht : formLt q k = formLt q' k' := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [← formLt_adjoint, ← formLt_adjoint, h]
  have hs : formS q k = formS q' k' := by simp only [formS, h, ht]
  have hT : formT q k = formT q' k' := by simp only [formT, h, ht]
  have heS : eigS q k = eigS q' k' := by unfold eigS; congr 1
  have heT : eigT2 q k = eigT2 q' k' := by unfold eigT2; congr 2; rw [hT]
  have hp : lamP q' k' = lamP q k := by ext j; simp only [lamP, heS]
  have hm : lamM q' k' = lamM q k := by ext j; simp only [lamM, heS]
  have ht' : sigT q' k' = sigT q k := by ext j; simp only [sigT, heT]
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hf : frobL q' k' = frobL q k := by rw [← frobL_eq q' k' b, ← frobL_eq q k b, h]
  have hfT : frobT q' k' = frobT q k := by rw [← frobT_eq q' k' b, ← frobT_eq q k b, hT]
  exact ⟨hp, hm, ht', by simp [gA, hf, hfT], by simp [gB, hp, hm, hf],
    by simp [gC, hp, hm, hf], by simp [gD, hp, hm, hf], by simp [gErr, hp, hm, ht']⟩

theorem exists_svd_rows (q k : Fin n → V)
    (hrank : Module.finrank ℝ (LinearMap.range (formL q k)) = n) :
    ∃ (σ : Fin n → ℝ) (u v : Fin n → V), (∀ i, 0 < σ i) ∧ Orthonormal ℝ u ∧
      Orthonormal ℝ v ∧ formL (fun i => σ i • v i) u = formL q k := by
  classical
  let L := formL q k
  let A := formLt q k ∘ₗ L
  have hA : A.IsSymmetric := by
    intro x y
    change ⟪(formLt q k) (L x), y⟫ = ⟪x, (formLt q k) (L y)⟫
    rw [real_inner_comm, ← formLt_adjoint, real_inner_comm, formLt_adjoint]
  let b := hA.eigenvectorBasis finrank_euclideanSpace_fin
  let μ := hA.eigenvalues finrank_euclideanSpace_fin
  have hb : ∀ i, A (b i) = μ i • b i := hA.apply_eigenvectorBasis _
  have hip : ∀ i j, ⟪L (b i), L (b j)⟫ = μ j * ⟪b i, b j⟫ := by
    intro i j
    rw [formLt_adjoint]
    change ⟪b i, A (b j)⟫ = _
    rw [hb, inner_smul_right]
  let I := {i : Fin N // L (b i) ≠ 0}
  let u₀ : I → V := fun i => ‖L (b i)‖⁻¹ • L (b i)
  have hnorm : ∀ i : I, 0 < ‖L (b i)‖ := fun i => norm_pos_iff.mpr i.property
  have hu₀ : Orthonormal ℝ u₀ := by
    constructor
    · intro i
      simp [u₀, norm_smul, ne_of_gt (hnorm i)]
    · intro i j hij
      have hij' : (i : Fin N) ≠ j := fun h => hij (Subtype.ext h)
      simp [u₀, inner_smul_left, inner_smul_right, hip, b.orthonormal.inner_eq_zero hij']
  have hspan : Submodule.span ℝ (Set.range u₀) = LinearMap.range L := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (LinearMap.range L).smul_mem _ (LinearMap.mem_range_self L (b i))
    · rintro _ ⟨x, rfl⟩
      have he : L x = ∑ i, ⟪b i, x⟫ • L (b i) := by
        conv_lhs => rw [← b.sum_repr' x]
        rw [map_sum]
        simp only [map_smul]
      rw [he]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      by_cases hi : L (b i) = 0
      · simp [hi]
      · have hm := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := u₀) ⟨i, hi⟩)
        have he : L (b i) = ‖L (b i)‖ • u₀ ⟨i, hi⟩ := by
          simp [u₀, smul_smul, ne_of_gt (norm_pos_iff.mpr hi)]
        rw [he]
        exact Submodule.smul_mem _ _ hm
  have hcard : Fintype.card I = n := by
    rw [← finrank_span_eq_card hu₀.linearIndependent, hspan]
    exact hrank
  let e : Fin n ≃ I := (finCongr hcard.symm).trans (Fintype.equivFin I).symm
  refine ⟨fun i => ‖L (b (e i))‖, fun i => u₀ (e i), fun i => b (e i),
    fun i => hnorm (e i), hu₀.comp e e.injective,
    b.orthonormal.comp (fun i => (e i).val) (Subtype.val_injective.comp e.injective), ?_⟩
  apply LinearMap.ext
  intro x
  change (formL _ _) x = L x
  simp only [formL, LinearMap.sum_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_smul_left, conj_trivial]
  have hs : (∑ i : Fin n, (‖L (b (e i))‖ * ⟪b (e i), x⟫) • u₀ (e i)) =
      ∑ i : I, ⟪b i, x⟫ • L (b i) := by
    apply Fintype.sum_equiv e
    intro i
    simp only [u₀, smul_smul]
    congr 1
    field_simp [ne_of_gt (hnorm (e i))]
  rw [hs]
  have hall : (∑ i : I, ⟪b i, x⟫ • L (b i)) =
      ∑ i : Fin N, ⟪b i, x⟫ • L (b i) := by
    rw [← Finset.sum_filter_of_ne (p := fun i => L (b i) ≠ 0)]
    · exact (Finset.sum_subtype (univ.filter (fun i => L (b i) ≠ 0)) (by simp)
        (fun i => ⟪b i, x⟫ • L (b i))).symm
    · intro i _ hi
      contrapose! hi
      simp [hi]
  rw [hall]
  simp only [← map_smul, ← map_sum, b.sum_repr']

theorem lists_isometry (O : V ≃ₗᵢ[ℝ] V) (q k : Fin n → V) :
    lamP (fun i => O (q i)) (fun i => O (k i)) = lamP q k ∧
    lamM (fun i => O (q i)) (fun i => O (k i)) = lamM q k ∧
    sigT (fun i => O (q i)) (fun i => O (k i)) = sigT q k := by
  exact ⟨by ext j; simp only [lamP, eigS_map],
    by ext j; simp only [lamM, eigS_map], by ext j; simp only [sigT, eigT2_map]⟩

end Odesky
