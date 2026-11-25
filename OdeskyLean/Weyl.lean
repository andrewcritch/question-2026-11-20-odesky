import Mathlib

/-!
# Layer 7 (gap G2): Weyl's inequality for sorted eigenvalues

For symmetric operators `A, B` on a finite-dimensional real inner product space,
with eigenvalues sorted decreasingly (`LinearMap.IsSymmetric.eigenvalues`), a bound
`|⟪(A - B) x, x⟫| ≤ c ‖x‖²` gives `|λ_k(A) - λ_k(B)| ≤ c` for every `k`.

Proof idea (a reference formalization over `ℂ` is FLYWHEEL, `src/WeylInequality.lean`,
Apache-2.0): the span of the top `k+1` eigenvectors of `A` meets the span of the
eigenvectors `k, …, d-1` of `B` in a nonzero vector `x` (dimension count); then
`λ_k(A) ‖x‖² ≤ ⟪A x, x⟫ ≤ ⟪B x, x⟫ + c ‖x‖² ≤ (λ_k(B) + c) ‖x‖²`.
-/

open RealInnerProductSpace Finset Polynomial

namespace Odesky

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private def spectralSpan {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (s : Set (Fin d)))

omit [FiniteDimensional ℝ E] in
private lemma spectralSpan_dim {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) : Module.finrank ℝ (spectralSpan b s) = s.card := by
  classical
  have h := finrank_span_eq_card (b.toBasis.linearIndependent.comp
    (fun i : s => (i : Fin d)) Subtype.val_injective)
  have he : Set.range (fun i : s => b (i : Fin d)) = b '' (s : Set (Fin d)) := by
    ext x
    simp
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => b (i : Fin d)))) = _ at h
  rw [he] at h
  simpa [spectralSpan] using h

omit [FiniteDimensional ℝ E] in
private lemma spectralSpan_coord {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (s : Finset (Fin d)) {x : E} (hx : x ∈ spectralSpan b s)
    {i : Fin d} (hi : i ∉ s) : b.repr x i = 0 := by
  classical
  have h := b.toBasis.repr_support_subset_of_mem_span (s : Set (Fin d)) hx
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  simpa using hz

private lemma spectral_quadratic {d : ℕ} (hd : Module.finrank ℝ E = d)
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
private lemma spectral_norm {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
  simpa [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
    (b.sum_sq_norm_inner_right x).symm

/-- Weyl's inequality, one side. -/
theorem weyl_le {d : ℕ} (hd : Module.finrank ℝ E = d) {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c : ℝ}
    (hc : ∀ x, ⟪(A - B) x, x⟫ ≤ c * ‖x‖ ^ 2) (k : Fin d) :
    hA.eigenvalues hd k ≤ hB.eigenvalues hd k + c := by
  classical
  let U := spectralSpan (hA.eigenvectorBasis hd) (Iic k)
  let V := spectralSpan (hB.eigenvectorBasis hd) (Ici k)
  have hU : Module.finrank ℝ U = k.val + 1 := by
    simpa [U, Fin.card_Iic] using spectralSpan_dim (hA.eigenvectorBasis hd) (Iic k)
  have hV : Module.finrank ℝ V = d - k.val := by
    simpa [V, Fin.card_Ici] using spectralSpan_dim (hB.eigenvectorBasis hd) (Ici k)
  have hne : U ⊓ V ≠ ⊥ := by
    intro hh
    have he := Submodule.finrank_sup_add_finrank_inf_eq U V
    have hl := Submodule.finrank_le (U ⊔ V)
    rw [hh, finrank_bot, hU, hV, add_zero] at he
    rw [hd] at hl
    have hk := k.isLt
    omega
  obtain ⟨x, hx, hx0⟩ := (U ⊓ V).ne_bot_iff.mp hne
  have hlow : hA.eigenvalues hd k * ‖x‖ ^ 2 ≤ ⟪A x, x⟫ := by
    rw [spectral_quadratic hd hA, spectral_norm (hA.eigenvectorBasis hd), mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hi : i ≤ k
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hd hi) (sq_nonneg _)
    · rw [spectralSpan_coord _ (Iic k) hx.1 (by simpa using hi)]
      simp
  have hupp : ⟪B x, x⟫ ≤ hB.eigenvalues hd k * ‖x‖ ^ 2 := by
    rw [spectral_quadratic hd hB, spectral_norm (hB.eigenvectorBasis hd), mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hi : k ≤ i
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues_antitone hd hi) (sq_nonneg _)
    · rw [spectralSpan_coord _ (Ici k) hx.2 (by simpa using hi)]
      simp
  have hc' := hc x
  simp only [LinearMap.sub_apply, inner_sub_left] at hc'
  have hp : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith)

/-- Weyl's inequality: sorted eigenvalues move by at most the quadratic-form size
of the perturbation. -/
theorem weyl_abs {d : ℕ} (hd : Module.finrank ℝ E = d) {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c : ℝ}
    (hc : ∀ x, |⟪(A - B) x, x⟫| ≤ c * ‖x‖ ^ 2) (k : Fin d) :
    |hA.eigenvalues hd k - hB.eigenvalues hd k| ≤ c := by
  apply abs_le.mpr
  constructor
  · have h := weyl_le hd hB hA (c := c) (fun x => ?_) k
    · linarith
    have h := (abs_le.mp (hc x)).1
    simpa only [LinearMap.sub_apply, inner_sub_left] using (show
      ⟪B x, x⟫ - ⟪A x, x⟫ ≤ c * ‖x‖ ^ 2 by
        simp only [LinearMap.sub_apply, inner_sub_left] at h
        linarith)
  · have h := weyl_le hd hA hB (fun x => (le_abs_self _).trans (hc x)) k
    linarith

/-- The roots of the characteristic polynomial of a symmetric operator are its
sorted eigenvalues, with multiplicity. -/
theorem roots_charpoly_eq_eigenvalues {d : ℕ} (hd : Module.finrank ℝ E = d)
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) :
    A.charpoly.roots = Multiset.map (hA.eigenvalues hd) univ.val := by
  classical
  let b := (hA.eigenvectorBasis hd).toBasis
  have hmat : LinearMap.toMatrix b b A = Matrix.diagonal (hA.eigenvalues hd) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis,
      hA.apply_eigenvectorBasis hd, map_smul, Matrix.diagonal_apply]
    split_ifs with hij <;> simp_all
  rw [← A.charpoly_toMatrix b, hmat, Matrix.charpoly_diagonal]
  have he : (∏ i, (X - C (hA.eigenvalues hd i))) =
      ((univ.val.map (hA.eigenvalues hd)).map (fun a => X - C a)).prod := by
    simp [Finset.prod, Function.comp_def]
  rw [he, roots_multiset_prod_X_sub_C]

end Odesky
