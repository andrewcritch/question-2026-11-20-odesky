import OdeskyLean.GenProfile

/-!
# The identities of §1, for every form

Write `L = ∑_i σ_i u_i v_iᵀ` with `σ_i > 0` and orthonormal families `u`, `v`
(the decomposition from the nonzero singular values). In the notation of
`GenProfile.lean`, `L x = ∑ ⟪q_i, x⟫ k_i` with rows `q_i = σ_i v_i` and `k_i = u_i`.
Let `W_ij = ⟪u_i, v_j⟫`, `t_i = W_ii`, `F = ∑ σ_i²`,
`m₂ = ∑ σ_i² t_i² / F`, and `q = ∑_{i≠j} σ_i σ_j W_ij W_ji / F`.

* `gA_identity`: `a = (1 - m₂ - q)/2`.
* `gprof_sum_eq_one`: for `2n ≤ N`, `a + b + c + d = 1`. The proof needs that `S`
  has at most `n` positive and at most `n` negative eigenvalues: `⟪S x, x⟫ =
  ∑ ⟪q_i, x⟫⟪k_i, x⟫` vanishes on the subspace `{x : ⟪q_i, x⟫ = 0 ∀ i}` of
  codimension at most `n`, so that subspace meets the span of the eigenvectors with
  positive eigenvalues only in `0`; similarly for negative eigenvalues. Then the
  first `n` sorted eigenvalues hold every positive eigenvalue, the last `n` hold
  every negative one, and `‖S‖² = ∑ λ₊² + ∑ λ₋² = ‖L‖² - ‖T‖²`.
* `gA_sub_gB_identity`: `a - b = c + d - m₂ - q`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- `W_ij = ⟪u_i, v_j⟫`. -/
noncomputable def Wm (u v : Fin n → V) (i j : Fin n) : ℝ := ⟪u i, v j⟫

/-- `F = ∑ σ_i²`. -/
noncomputable def Fsq (σ : Fin n → ℝ) : ℝ := ∑ i, σ i ^ 2

/-- `m₂ = ∑ σ_i² W_ii² / F`. -/
noncomputable def m2 (σ : Fin n → ℝ) (u v : Fin n → V) : ℝ :=
  (∑ i, σ i ^ 2 * Wm u v i i ^ 2) / Fsq σ

/-- `q = ∑_{i≠j} σ_i σ_j W_ij W_ji / F`. -/
noncomputable def qrec (σ : Fin n → ℝ) (u v : Fin n → V) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else σ i * σ j * Wm u v i j * Wm u v j i) / Fsq σ


private lemma formL_apply' (q k : Fin n → V) (x : V) :
    formL q k x = ∑ i, ⟪q i, x⟫ • k i := by
  simp [formL, LinearMap.sum_apply]

private lemma formS_inner_self (q k : Fin n → V) (x : V) :
    ⟪formS q k x, x⟫ = ∑ i, ⟪q i, x⟫ * ⟪k i, x⟫ := by
  have h := formLt_adjoint q k x x
  have hL : ⟪formL q k x, x⟫ = ∑ i, ⟪q i, x⟫ * ⟪k i, x⟫ := by
    rw [formL_apply']
    simp only [sum_inner, inner_smul_left, conj_trivial]
  simp only [formS, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left,
    inner_add_left, conj_trivial]
  rw [real_inner_comm x (formLt q k x), ← h, hL]
  ring

/-- No `n+1` eigenvalues of `S` (at distinct indices) share a strict sign `ε`. -/
private lemma no_signed_block (q k : Fin n → V) (ε : ℝ) (s : Fin (n + 1) → Fin N)
    (hs : Function.Injective s) (hpos : ∀ j, 0 < ε * eigS q k (s j)) : False := by
  set hS := formS_isSymmetric q k
  set e := hS.eigenvectorBasis finrank_euclideanSpace_fin
  have he : Orthonormal ℝ (fun j => e (s j)) := e.orthonormal.comp s hs
  let Φ : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => (innerSL ℝ (q i) : V →L[ℝ] ℝ).toLinearMap ∘ₗ
      Fintype.linearCombination ℝ (fun j => e (s j)))
  have hk : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hk
  set x : V := ∑ j, c j • e (s j) with hx
  have hq : ∀ i, ⟪q i, x⟫ = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.mp hc) i
    simpa [Φ, Fintype.linearCombination_apply, hx] using this
  have h0 : ⟪formS q k x, x⟫ = 0 := by
    rw [formS_inner_self]; simp [hq]
  have hSx : formS q k x = ∑ j, (c j * eigS q k (s j)) • e (s j) := by
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    have := hS.apply_eigenvectorBasis finrank_euclideanSpace_fin (s j)
    rw [this, smul_smul]
    rfl
  have h1 : ⟪formS q k x, x⟫ = ∑ j, c j ^ 2 * eigS q k (s j) := by
    rw [hSx, hx, he.inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [conj_trivial]; ring
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc0 (funext h)
  obtain ⟨j0, hj0⟩ := hcne
  have hpos' : 0 < ∑ j, c j ^ 2 * (ε * eigS q k (s j)) := by
    refine Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (hpos j).le) ⟨j0, by simp, ?_⟩
    exact mul_pos (by positivity) (hpos j0)
  have : ∑ j, c j ^ 2 * (ε * eigS q k (s j)) = ε * ⟪formS q k x, x⟫ := by
    rw [h1, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [this, h0, mul_zero] at hpos'
  exact lt_irrefl _ hpos'


private lemma eigS_pos_part (q k : Fin n → V) (t : Fin N) (ht : n ≤ (t : ℕ)) :
    max (eigS q k t) 0 = 0 := by
  rcases le_or_gt (eigS q k t) 0 with h | h
  · exact max_eq_right h
  · exfalso
    have hanti := (formS_isSymmetric q k).eigenvalues_antitone finrank_euclideanSpace_fin
    refine no_signed_block q k 1 (fun j => ⟨j, by omega⟩) ?_ ?_
    · intro a b hab; simp only [Fin.mk.injEq] at hab; exact Fin.ext hab
    · intro j
      rw [one_mul]
      exact lt_of_lt_of_le h (hanti (Fin.le_iff_val_le_val.mpr (show (j : ℕ) ≤ t by omega)))

private lemma eigS_neg_part (q k : Fin n → V) (t : Fin N) (ht : (t : ℕ) + n < N) :
    max (-eigS q k t) 0 = 0 := by
  rcases le_or_gt (-eigS q k t) 0 with h | h
  · exact max_eq_right h
  · exfalso
    have hanti := (formS_isSymmetric q k).eigenvalues_antitone finrank_euclideanSpace_fin
    refine no_signed_block q k (-1) (fun j => ⟨N - 1 - j, by omega⟩) ?_ ?_
    · intro a b hab; simp only [Fin.mk.injEq] at hab; exact Fin.ext (by omega)
    · intro j
      have : eigS q k ⟨N - 1 - j, by omega⟩ ≤ eigS q k t :=
        hanti (Fin.le_iff_val_le_val.mpr (show (t : ℕ) ≤ N - 1 - j by omega))
      show 0 < -1 * eigS q k ⟨N - 1 - j, by omega⟩
      linarith

private lemma sum_lam_sq (q k : Fin n → V) (hn : n ≤ N) :
    ∑ j, (lamP q k j ^ 2 + lamM q k j ^ 2) = ∑ t, eigS q k t ^ 2 := by
  have hsplit : ∀ t, eigS q k t ^ 2 = max (eigS q k t) 0 ^ 2 + max (-eigS q k t) 0 ^ 2 := by
    intro t
    rcases le_total (eigS q k t) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · refine Fintype.sum_of_injective (fun j : Fin n => (⟨j, by omega⟩ : Fin N)) ?_ _ _ ?_ ?_
    · intro a b hab; simp only [Fin.mk.injEq] at hab; exact Fin.ext hab
    · intro t ht
      have : n ≤ (t : ℕ) := by
        by_contra h'
        exact ht ⟨⟨t, by omega⟩, rfl⟩
      rw [eigS_pos_part q k t this]; ring
    · intro j
      simp [lamP, eigAt, show (j : ℕ) < N by omega]
  · refine Fintype.sum_of_injective (fun j : Fin n => (⟨N - 1 - j, by omega⟩ : Fin N)) ?_ _ _ ?_ ?_
    · intro a b hab; simp only [Fin.mk.injEq] at hab; exact Fin.ext (by omega)
    · intro t ht
      have : (t : ℕ) + n < N := by
        by_contra h'
        exact ht ⟨⟨N - 1 - t, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [eigS_neg_part q k t this]; ring
    · intro j
      simp [lamM, eigAt, show N - 1 - (j : ℕ) < N by omega]

private lemma sum_eigS_sq (q k : Fin n → V) :
    ∑ t, eigS q k t ^ 2 = frobL q k - frobT q k := by
  set hS := formS_isSymmetric q k
  set e := hS.eigenvectorBasis finrank_euclideanSpace_fin
  have h1 : ∀ t, eigS q k t ^ 2 = ‖formS q k (e t)‖ ^ 2 := by
    intro t
    rw [hS.apply_eigenvectorBasis finrank_euclideanSpace_fin t, norm_smul, e.orthonormal.1 t]
    simp [eigS, sq_abs]
  have h2 : ∀ t, ‖formS q k (e t)‖ ^ 2 =
      (‖formL q k (e t)‖ ^ 2 + ‖formL k q (e t)‖ ^ 2) / 2 - ‖formT q k (e t)‖ ^ 2 := by
    intro t
    have hLt : formL k q = formLt q k := rfl
    rw [hLt]
    simp only [← real_inner_self_eq_norm_sq, formS, formT, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, conj_trivial]
    ring
  simp_rw [h1, h2]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, frobL_eq, frobL_eq,
    frobT_eq]
  have : frobL k q = frobL q k := by
    unfold frobL; simp_rw [mul_comm]
  rw [this]; ring

/-- For `n ≤ N`, `‖S‖² = ∑ λ₊² + ∑ λ₋²` and `a + b + c + d = 1` whenever `‖L‖ ≠ 0`. -/
private lemma gsum_general (q k : Fin n → V) (hn : n ≤ N) (hF : frobL q k ≠ 0) :
    gA q k + gB q k + gC q k + gD q k = 1 := by
  have key : ∀ j, 2 * (lamP q k j * lamM q k j) + (max (lamP q k j - lamM q k j) 0) ^ 2 +
      (max (lamM q k j - lamP q k j) 0) ^ 2 = lamP q k j ^ 2 + lamM q k j ^ 2 := by
    intro j
    rcases le_total (lamP q k j) (lamM q k j) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hsum : 2 * (∑ j, lamP q k j * lamM q k j) + ∑ j, (max (lamP q k j - lamM q k j) 0) ^ 2 +
      ∑ j, (max (lamM q k j - lamP q k j) 0) ^ 2 = frobL q k - frobT q k := by
    rw [← sum_eigS_sq, ← sum_lam_sq q k hn, ← Finset.sum_congr rfl (fun j _ => key j),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  unfold gA gB gC gD
  field_simp
  linarith


private lemma frobL_svd (σ : Fin n → ℝ) (u v : Fin n → V) (hu : Orthonormal ℝ u)
    (hv : Orthonormal ℝ v) : frobL (fun i => σ i • v i) u = Fsq σ := by
  rw [orthonormal_iff_ite] at hu hv
  unfold frobL Fsq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, inner_smul_right, conj_trivial, hu, hv]
  simp [ite_mul, mul_ite, sq]

private lemma trace_svd (σ : Fin n → ℝ) (u v : Fin n → V) :
    ∑ i, ∑ j, ⟪u i, σ j • v j⟫ * ⟪σ i • v i, u j⟫ =
      ∑ i, σ i ^ 2 * Wm u v i i ^ 2 +
        ∑ i, ∑ j, if i = j then 0 else σ i * σ j * Wm u v i j * Wm u v j i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ⟪u i, σ j • v j⟫ * ⟪σ i • v i, u j⟫ =
      (if i = j then σ i * σ j * Wm u v i j * Wm u v j i else 0) +
        (if i = j then 0 else σ i * σ j * Wm u v i j * Wm u v j i) := by
    intro j
    simp only [inner_smul_left, inner_smul_right, conj_trivial, Wm]
    rw [real_inner_comm (v i) (u j)]
    split_ifs <;> ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

private lemma Fsq_pos [NeZero n] (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) : 0 < Fsq σ :=
  Finset.sum_pos (fun i _ => pow_pos (hσ i) 2) Finset.univ_nonempty

theorem gA_identity [NeZero n] (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (u v : Fin n → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u = (1 - m2 σ u v - qrec σ u v) / 2 := by
  have hF := Fsq_pos σ hσ
  unfold gA frobT m2 qrec
  rw [trace_svd, frobL_svd σ u v hu hv]
  field_simp
  ring

theorem gprof_sum_eq_one [NeZero n] (hN : 2 * n ≤ N) (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i)
    (u v : Fin n → V) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u + gB (fun i => σ i • v i) u +
      gC (fun i => σ i • v i) u + gD (fun i => σ i • v i) u = 1 := by
  refine gsum_general _ _ (by omega) ?_
  rw [frobL_svd σ u v hu hv]
  exact (Fsq_pos σ hσ).ne'

theorem gA_sub_gB_identity [NeZero n] (hN : 2 * n ≤ N) (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i)
    (u v : Fin n → V) (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    gA (fun i => σ i • v i) u - gB (fun i => σ i • v i) u =
      gC (fun i => σ i • v i) u + gD (fun i => σ i • v i) u - m2 σ u v - qrec σ u v := by
  have h1 := gA_identity σ hσ u v hu hv
  have h2 := gprof_sum_eq_one hN σ hσ u v hu hv
  linarith

end Odesky
