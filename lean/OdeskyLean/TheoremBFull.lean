import OdeskyLean.Limit
import OdeskyLean.Perturb
import OdeskyLean.Orthonormalize
import OdeskyLean.Weyl
import OdeskyLean.Probability
import OdeskyLean.Gaussian

set_option linter.unusedSimpArgs false

/-!
# Theorem B in full (closes gap G2)

Fix `n`, `f(ρ_i) = fv i > 0`, `g(ρ_i) = gv i > 0` (conditioning on the latent
strengths). For each `N`, `x N : Fin (n + n) → ℝᴺ` are the rows of `[P; M]/√N`;
the rows of `Q` and `K` are

  `q_i = √fv_i x_i - √gv_i x_{n+i}`,   `k_i = √fv_i x_i + √gv_i x_{n+i}`.

* `profile_tendsto` (deterministic): if the Gram matrix of `x N` tends to the
  identity, then the profile of `L_N = K_Nᵀ Q_N` tends to the profile of Theorem A
  with `α = fv`, `β = gv`, and, if `(fv, gv)` is similarly ordered, the relation-(1)
  error tends to `0`.
* `theoremB_ae`: for i.i.d. columns of `[P; M]` with independent standard Gaussian
  coordinates, the same holds almost surely.

Proof route: by `exists_orthonormal_near`, for large `N` there is an orthonormal
family `e` near `x N`; the form built from `e` is the exact limit configuration
(`gprof_at_limit`, `lists_at_limit`); `formL_perturb` and `formLt_perturb` bound
the change in `S` and `TᵀT` as quadratic forms; `weyl_abs` moves each sorted
eigenvalue by at most that bound; the Frobenius norms are continuous in the Gram
matrix.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology RealInnerProductSpace

namespace Odesky

variable {n : ℕ}

/-- Rows of `Q`. -/
noncomputable def qOf {N : ℕ} (fv gv : Fin n → ℝ) (x : Fin (n + n) → EuclideanSpace ℝ (Fin N))
    (i : Fin n) : EuclideanSpace ℝ (Fin N) :=
  Real.sqrt (fv i) • x (Fin.castAdd n i) - Real.sqrt (gv i) • x (Fin.natAdd n i)

/-- Rows of `K`. -/
noncomputable def kOf {N : ℕ} (fv gv : Fin n → ℝ) (x : Fin (n + n) → EuclideanSpace ℝ (Fin N))
    (i : Fin n) : EuclideanSpace ℝ (Fin N) :=
  Real.sqrt (fv i) • x (Fin.castAdd n i) + Real.sqrt (gv i) • x (Fin.natAdd n i)

private lemma castAdd_ne_natAdd (i l : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

private lemma castAdd_eq_iff (i l : Fin n) : Fin.castAdd n i = Fin.castAdd n l ↔ i = l := by
  constructor
  · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · rintro rfl; rfl

private lemma natAdd_eq_iff (i l : Fin n) : Fin.natAdd n i = Fin.natAdd n l ↔ i = l := by
  constructor
  · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · rintro rfl; rfl

/-- Coefficients of `Q`. -/
private noncomputable def AQ (fv gv : Fin n → ℝ) (i : Fin n) (a : Fin (n + n)) : ℝ :=
  (if a = Fin.castAdd n i then Real.sqrt (fv i) else 0) +
    (if a = Fin.natAdd n i then -Real.sqrt (gv i) else 0)

/-- Coefficients of `K`. -/
private noncomputable def AK (fv gv : Fin n → ℝ) (i : Fin n) (a : Fin (n + n)) : ℝ :=
  (if a = Fin.castAdd n i then Real.sqrt (fv i) else 0) +
    (if a = Fin.natAdd n i then Real.sqrt (gv i) else 0)

private lemma qOf_eq_comb {N : ℕ} (fv gv : Fin n → ℝ) (x : Fin (n + n) → EuclideanSpace ℝ (Fin N)) :
    qOf fv gv x = comb (AQ fv gv) x := by
  funext i
  simp [comb, AQ, add_smul, sum_add_distrib, ite_smul, qOf, sub_eq_add_neg, neg_smul]

private lemma kOf_eq_comb {N : ℕ} (fv gv : Fin n → ℝ) (x : Fin (n + n) → EuclideanSpace ℝ (Fin N)) :
    kOf fv gv x = comb (AK fv gv) x := by
  funext i
  simp [comb, AK, add_smul, sum_add_distrib, ite_smul, kOf]

/-- Gram entries of the rows, as polynomials in the Gram matrix `G` of `x`. -/
private noncomputable def ipQQ (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ)
    (i l : Fin n) : ℝ :=
  Real.sqrt (fv i) * Real.sqrt (fv l) * G (Fin.castAdd n i) (Fin.castAdd n l)
  - Real.sqrt (fv i) * Real.sqrt (gv l) * G (Fin.castAdd n i) (Fin.natAdd n l)
  - Real.sqrt (gv i) * Real.sqrt (fv l) * G (Fin.natAdd n i) (Fin.castAdd n l)
  + Real.sqrt (gv i) * Real.sqrt (gv l) * G (Fin.natAdd n i) (Fin.natAdd n l)

private noncomputable def ipKK (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ)
    (i l : Fin n) : ℝ :=
  Real.sqrt (fv i) * Real.sqrt (fv l) * G (Fin.castAdd n i) (Fin.castAdd n l)
  + Real.sqrt (fv i) * Real.sqrt (gv l) * G (Fin.castAdd n i) (Fin.natAdd n l)
  + Real.sqrt (gv i) * Real.sqrt (fv l) * G (Fin.natAdd n i) (Fin.castAdd n l)
  + Real.sqrt (gv i) * Real.sqrt (gv l) * G (Fin.natAdd n i) (Fin.natAdd n l)

private noncomputable def ipQK (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ)
    (i l : Fin n) : ℝ :=
  Real.sqrt (fv i) * Real.sqrt (fv l) * G (Fin.castAdd n i) (Fin.castAdd n l)
  + Real.sqrt (fv i) * Real.sqrt (gv l) * G (Fin.castAdd n i) (Fin.natAdd n l)
  - Real.sqrt (gv i) * Real.sqrt (fv l) * G (Fin.natAdd n i) (Fin.castAdd n l)
  - Real.sqrt (gv i) * Real.sqrt (gv l) * G (Fin.natAdd n i) (Fin.natAdd n l)

private noncomputable def ipKQ (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ)
    (i l : Fin n) : ℝ :=
  Real.sqrt (fv i) * Real.sqrt (fv l) * G (Fin.castAdd n i) (Fin.castAdd n l)
  - Real.sqrt (fv i) * Real.sqrt (gv l) * G (Fin.castAdd n i) (Fin.natAdd n l)
  + Real.sqrt (gv i) * Real.sqrt (fv l) * G (Fin.natAdd n i) (Fin.castAdd n l)
  - Real.sqrt (gv i) * Real.sqrt (gv l) * G (Fin.natAdd n i) (Fin.natAdd n l)

private noncomputable def gram {N m : ℕ} (y : Fin m → EuclideanSpace ℝ (Fin N)) :
    Fin m → Fin m → ℝ := fun a b => ⟪y a, y b⟫

section gramlemmas
variable {N : ℕ} (fv gv : Fin n → ℝ) (y : Fin (n + n) → EuclideanSpace ℝ (Fin N))

private lemma inner_qq (i l : Fin n) :
    ⟪qOf fv gv y i, qOf fv gv y l⟫ = ipQQ fv gv (gram y) i l := by
  simp only [qOf, ipQQ, gram, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  ring

private lemma inner_kk (i l : Fin n) :
    ⟪kOf fv gv y i, kOf fv gv y l⟫ = ipKK fv gv (gram y) i l := by
  simp only [kOf, ipKK, gram, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  ring

private lemma inner_qk (i l : Fin n) :
    ⟪qOf fv gv y i, kOf fv gv y l⟫ = ipQK fv gv (gram y) i l := by
  simp only [qOf, kOf, ipQK, gram, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

private lemma inner_kq (i l : Fin n) :
    ⟪kOf fv gv y i, qOf fv gv y l⟫ = ipKQ fv gv (gram y) i l := by
  simp only [qOf, kOf, ipKQ, gram, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

end gramlemmas

/-- The identity Gram matrix. -/
private def idG (m : ℕ) : Fin m → Fin m → ℝ := fun a b => if a = b then 1 else 0

private lemma gram_orthonormal {N m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin N))
    (he : Orthonormal ℝ e) : gram e = idG m := by
  funext a b
  simp [gram, idG, orthonormal_iff_ite.mp he]

private lemma idG_cn (i l : Fin n) : idG (n + n) (Fin.castAdd n i) (Fin.natAdd n l) = 0 :=
  if_neg (castAdd_ne_natAdd i l)

private lemma idG_nc (i l : Fin n) : idG (n + n) (Fin.natAdd n i) (Fin.castAdd n l) = 0 :=
  if_neg (castAdd_ne_natAdd l i).symm

private lemma idG_cc (i l : Fin n) :
    idG (n + n) (Fin.castAdd n i) (Fin.castAdd n l) = if i = l then 1 else 0 := by
  unfold idG; simp only [castAdd_eq_iff]

private lemma idG_nn (i l : Fin n) :
    idG (n + n) (Fin.natAdd n i) (Fin.natAdd n l) = if i = l then 1 else 0 := by
  unfold idG; simp only [natAdd_eq_iff]

private lemma sqrt_mul_ite (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) (i l : Fin n) :
    Real.sqrt (u i) * Real.sqrt (u l) * (if i = l then (1 : ℝ) else 0) =
      if i = l then u i else 0 := by
  split_ifs with h
  · subst h; rw [mul_one, Real.mul_self_sqrt (hu i).le]
  · rw [mul_zero]

private lemma ipQQ_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (i l : Fin n) : ipQQ fv gv (idG _) i l = if i = l then fv i + gv i else 0 := by
  rw [ipQQ, idG_cn, idG_nc, idG_cc, idG_nn, sqrt_mul_ite fv hf, sqrt_mul_ite gv hg]
  split_ifs <;> ring

private lemma ipKK_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (i l : Fin n) : ipKK fv gv (idG _) i l = if i = l then fv i + gv i else 0 := by
  rw [ipKK, idG_cn, idG_nc, idG_cc, idG_nn, sqrt_mul_ite fv hf, sqrt_mul_ite gv hg]
  split_ifs <;> ring

private lemma ipQK_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (i l : Fin n) : ipQK fv gv (idG _) i l = if i = l then fv i - gv i else 0 := by
  rw [ipQK, idG_cn, idG_nc, idG_cc, idG_nn, sqrt_mul_ite fv hf, sqrt_mul_ite gv hg]
  split_ifs <;> ring

/-- Exact limit configuration built from an orthonormal family. -/
private lemma limit_config {N : ℕ} (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (e : Fin (n + n) → EuclideanSpace ℝ (Fin N)) (he : Orthonormal ℝ e) :
    (∀ i l, ⟪qOf fv gv e i, qOf fv gv e l⟫ = if i = l then fv i + gv i else 0) ∧
    (∀ i l, ⟪kOf fv gv e i, kOf fv gv e l⟫ = if i = l then fv i + gv i else 0) ∧
    (∀ i l, ⟪qOf fv gv e i, kOf fv gv e l⟫ = if i = l then fv i - gv i else 0) := by
  refine ⟨fun i l => ?_, fun i l => ?_, fun i l => ?_⟩
  · rw [inner_qq, gram_orthonormal e he, ipQQ_id fv gv hf hg]
  · rw [inner_kk, gram_orthonormal e he, ipKK_id fv gv hf hg]
  · rw [inner_qk, gram_orthonormal e he, ipQK_id fv gv hf hg]

section weylpart
variable {N : ℕ}

private lemma formLt_adjoint' (q k : Fin n → EuclideanSpace ℝ (Fin N)) (z y : EuclideanSpace ℝ (Fin N)) :
    ⟪formLt q k z, y⟫ = ⟪z, formL q k y⟫ := by
  rw [real_inner_comm, ← formLt_adjoint, real_inner_comm]

private lemma formT_apply (q k : Fin n → EuclideanSpace ℝ (Fin N)) (z : EuclideanSpace ℝ (Fin N)) :
    formT q k z = (1 / 2 : ℝ) • (formL q k z - formLt q k z) := by
  simp [formT]

private lemma formS_apply (q k : Fin n → EuclideanSpace ℝ (Fin N)) (z : EuclideanSpace ℝ (Fin N)) :
    formS q k z = (1 / 2 : ℝ) • (formL q k z + formLt q k z) := by
  simp [formS]

private lemma formT_skew (q k : Fin n → EuclideanSpace ℝ (Fin N)) (z y : EuclideanSpace ℝ (Fin N)) :
    ⟪formT q k z, y⟫ = -⟪z, formT q k y⟫ := by
  rw [formT_apply, formT_apply, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, formLt_adjoint, formLt_adjoint']
  simp only [RCLike.conj_to_real]
  ring

private lemma negTsq_quad (q k : Fin n → EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin N)) :
    ⟪(-(formT q k ∘ₗ formT q k)) y, y⟫ = ‖formT q k y‖ ^ 2 := by
  rw [LinearMap.neg_apply, LinearMap.comp_apply, inner_neg_left, formT_skew, neg_neg,
    real_inner_self_eq_norm_sq]

private lemma eigAt_close {v w : Fin N → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i - w i| ≤ c)
    (j : ℕ) : |eigAt v j - eigAt w j| ≤ c := by
  unfold eigAt
  split_ifs with hj
  · exact h _
  · simpa using hc

/-- Weyl step: closeness of the forms moves the spectral lists by a small amount. -/
private lemma eig_perturb (q k q' k' : Fin n → EuclideanSpace ℝ (Fin N)) {c κ : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hL : ∀ y, ‖formL q k y - formL q' k' y‖ ≤ c * ‖y‖)
    (hLt : ∀ y, ‖formLt q k y - formLt q' k' y‖ ≤ c * ‖y‖)
    (hB : ∀ y, ‖formL q' k' y‖ ≤ κ * ‖y‖ ∧ ‖formLt q' k' y‖ ≤ κ * ‖y‖) :
    (∀ j, |lamP q k j - lamP q' k' j| ≤ c) ∧ (∀ j, |lamM q k j - lamM q' k' j| ≤ c) ∧
      (∀ j : Fin n, |max (eigAt (eigT2 q k) (2 * (j : ℕ))) 0 -
        max (eigAt (eigT2 q' k') (2 * (j : ℕ))) 0| ≤ c * (2 * κ + c)) := by
  -- S
  have hS : ∀ y, |⟪(formS q k - formS q' k') y, y⟫| ≤ c * ‖y‖ ^ 2 := by
    intro y
    have h1 : (formS q k - formS q' k') y =
        (1 / 2 : ℝ) • ((formL q k y - formL q' k' y) + (formLt q k y - formLt q' k' y)) := by
      rw [LinearMap.sub_apply, formS_apply, formS_apply, ← smul_sub]
      congr 1; abel
    have h2 : ‖(formS q k - formS q' k') y‖ ≤ c * ‖y‖ := by
      rw [h1, norm_smul]
      have := norm_add_le (formL q k y - formL q' k' y) (formLt q k y - formLt q' k' y)
      have := hL y
      have := hLt y
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    calc |⟪(formS q k - formS q' k') y, y⟫| ≤ ‖(formS q k - formS q' k') y‖ * ‖y‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ c * ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = c * ‖y‖ ^ 2 := by ring
  have hW := weyl_abs finrank_euclideanSpace_fin (formS_isSymmetric q k)
    (formS_isSymmetric q' k') hS
  have hE : ∀ j : ℕ, |eigAt (eigS q k) j - eigAt (eigS q' k') j| ≤ c :=
    eigAt_close hc (fun i => hW i)
  -- T
  have hT : ∀ y, ‖formT q k y - formT q' k' y‖ ≤ c * ‖y‖ := by
    intro y
    have h1 : formT q k y - formT q' k' y =
        (1 / 2 : ℝ) • ((formL q k y - formL q' k' y) - (formLt q k y - formLt q' k' y)) := by
      rw [formT_apply, formT_apply, ← smul_sub]
      congr 1; abel
    rw [h1, norm_smul]
    have := norm_sub_le (formL q k y - formL q' k' y) (formLt q k y - formLt q' k' y)
    have := hL y
    have := hLt y
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hTb : ∀ y, ‖formT q' k' y‖ ≤ κ * ‖y‖ := by
    intro y
    rw [formT_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_sub_le (formL q' k' y) (formLt q' k' y)
    have := (hB y).1
    have := (hB y).2
    linarith
  have hT2 : ∀ y, |⟪(-(formT q k ∘ₗ formT q k) - -(formT q' k' ∘ₗ formT q' k')) y, y⟫| ≤
      (c * (2 * κ + c)) * ‖y‖ ^ 2 := by
    intro y
    rw [LinearMap.sub_apply, inner_sub_left, negTsq_quad, negTsq_quad]
    have ha := hT y
    have hb := hTb y
    have hd : |‖formT q k y‖ - ‖formT q' k' y‖| ≤ c * ‖y‖ :=
      (abs_norm_sub_norm_le _ _).trans ha
    have hy := norm_nonneg y
    have h0 := norm_nonneg (formT q k y)
    have h0' := norm_nonneg (formT q' k' y)
    have hsum : ‖formT q k y‖ + ‖formT q' k' y‖ ≤ (2 * κ + c) * ‖y‖ := by
      have := (abs_le.mp hd).2
      linarith
    have hfac : ‖formT q k y‖ ^ 2 - ‖formT q' k' y‖ ^ 2 =
        (‖formT q k y‖ - ‖formT q' k' y‖) * (‖formT q k y‖ + ‖formT q' k' y‖) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (add_nonneg h0 h0')]
    calc |‖formT q k y‖ - ‖formT q' k' y‖| * (‖formT q k y‖ + ‖formT q' k' y‖)
        ≤ (c * ‖y‖) * ((2 * κ + c) * ‖y‖) :=
          mul_le_mul hd hsum (add_nonneg h0 h0') (mul_nonneg hc hy)
      _ = (c * (2 * κ + c)) * ‖y‖ ^ 2 := by ring
  have hW2 := weyl_abs finrank_euclideanSpace_fin (negTsq_isSymmetric q k)
    (negTsq_isSymmetric q' k') hT2
  have hc2 : 0 ≤ c * (2 * κ + c) := mul_nonneg hc (by linarith)
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
  · exact (abs_max_sub_max_le_abs _ _ _).trans (hE j)
  · refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show -eigAt (eigS q k) (N - 1 - (j : ℕ)) - -eigAt (eigS q' k') (N - 1 - (j : ℕ)) =
      -(eigAt (eigS q k) (N - 1 - (j : ℕ)) - eigAt (eigS q' k') (N - 1 - (j : ℕ))) by ring,
      abs_neg]
    exact hE _
  · exact (abs_max_sub_max_le_abs _ _ _).trans (eigAt_close hc2 (fun i => hW2 i) _)

end weylpart

/-- Distance of the Gram matrix from the identity. -/
private noncomputable def gramErr {N m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∑ a, ∑ b, |⟪x a, x b⟫ - if a = b then 1 else 0|

private lemma gramErr_nonneg {N m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin N)) :
    0 ≤ gramErr x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

private lemma gram_quad_bound {N m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin N)) (c : Fin m → ℝ) :
    |∑ a, ∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)| ≤
      gramErr x * ∑ a, c a ^ 2 := by
  set S := ∑ a, c a ^ 2
  have hsq : ∀ a, c a ^ 2 ≤ S := fun a =>
    single_le_sum (f := fun a => c a ^ 2) (fun i _ => sq_nonneg (c i)) (mem_univ a)
  have hab : ∀ a b, |c a * c b| ≤ S := by
    intro a b
    rw [abs_mul]
    have h1 := hsq a
    have h2 := hsq b
    have : |c a| * |c b| ≤ (c a ^ 2 + c b ^ 2) / 2 := by
      have := sq_nonneg (|c a| - |c b|)
      have ea : |c a| ^ 2 = c a ^ 2 := sq_abs _
      have eb : |c b| ^ 2 = c b ^ 2 := sq_abs _
      nlinarith
    linarith
  calc |∑ a, ∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)|
      ≤ ∑ a, |∑ b, c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |c a * c b * (⟪x a, x b⟫ - if a = b then 1 else 0)| :=
        sum_le_sum fun a _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, S * |⟪x a, x b⟫ - if a = b then 1 else 0| := by
        apply sum_le_sum; intro a _; apply sum_le_sum; intro b _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hab a b) (abs_nonneg _)
    _ = gramErr x * S := by
        simp only [gramErr, mul_sum]
        rw [sum_mul]; apply sum_congr rfl; intro a _; rw [sum_mul]
        apply sum_congr rfl; intro b _; ring

private lemma kappa_nonneg {m : ℕ} (AQ' AK' : Fin n → Fin m → ℝ) : 0 ≤ kappa AQ' AK' :=
  sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- One step at a fixed `N`: the spectral lists are near their limits. -/
private lemma step_bounds [NeZero n] {N : ℕ} (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i)
    (hg : ∀ i, 0 < gv i) (x : Fin (n + n) → EuclideanSpace ℝ (Fin N))
    (hN : 2 * n ≤ N) (h1 : gramErr x < 1)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) {c : ℝ}
    (hcdef : c = gramErr x * (2 + gramErr x) * kappa (AQ fv gv) (AK fv gv)) :
    (∀ j, |lamP (qOf fv gv x) (kOf fv gv x) j - fv (σ j)| ≤ c) ∧
    (∀ j, |lamM (qOf fv gv x) (kOf fv gv x) j - gv (τ j)| ≤ c) ∧
    (SimilarlyOrdered fv gv → ∀ j : Fin n,
      |max (eigAt (eigT2 (qOf fv gv x) (kOf fv gv x)) (2 * (j : ℕ))) 0 - fv (σ j) * gv (τ j)|
        ≤ c * (2 * kappa (AQ fv gv) (AK fv gv) + c)) := by
  obtain ⟨e, he, hxe⟩ := exists_orthonormal_near x (gramErr_nonneg x) h1
    (fun c => gram_quad_bound x c)
  obtain ⟨hqq, hkk, hqk⟩ := limit_config fv gv hf hg e he
  obtain ⟨hP, hM, -, -, hS⟩ := lists_at_limit fv gv hf hg _ _ hqq hkk hqk hN hσ hτ
  have hδ := gramErr_nonneg x
  have hκ := kappa_nonneg (AQ fv gv) (AK fv gv)
  have hc : 0 ≤ c := hcdef ▸ mul_nonneg (mul_nonneg hδ (by linarith)) hκ
  have hL := formL_perturb (AQ fv gv) (AK fv gv) x e he hδ hxe
  have hLt := formLt_perturb (AQ fv gv) (AK fv gv) x e he hδ hxe
  have hB := formL_bound (AQ fv gv) (AK fv gv) e he
  rw [← qOf_eq_comb fv gv x, ← kOf_eq_comb fv gv x, ← qOf_eq_comb fv gv e,
    ← kOf_eq_comb fv gv e, ← hcdef] at hL hLt
  rw [← qOf_eq_comb fv gv e, ← kOf_eq_comb fv gv e] at hB
  obtain ⟨eP, eM, eT⟩ := eig_perturb (qOf fv gv x) (kOf fv gv x) (qOf fv gv e) (kOf fv gv e)
    hc hκ hL hLt hB
  refine ⟨fun j => ?_, fun j => ?_, fun hso j => ?_⟩
  · have := eP j; rw [hP] at this; exact this
  · have := eM j; rw [hM] at this; exact this
  · have h := hS hso j
    have hm : max (eigAt (eigT2 (qOf fv gv e) (kOf fv gv e)) (2 * (j : ℕ))) 0 =
        fv (σ j) * gv (τ j) := by
      unfold sigT at h
      exact (Real.sqrt_inj (le_max_right _ _)
        (mul_pos (hf _) (hg _)).le).mp h
    have := eT j
    rw [hm] at this
    exact this

private lemma ipKQ_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (i l : Fin n) : ipKQ fv gv (idG _) i l = if i = l then fv i - gv i else 0 := by
  rw [ipKQ, idG_cn, idG_nc, idG_cc, idG_nn, sqrt_mul_ite fv hf, sqrt_mul_ite gv hg]
  split_ifs <;> ring

private noncomputable def PhiL (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ) : ℝ :=
  ∑ i, ∑ j, ipKK fv gv G i j * ipQQ fv gv G i j

private noncomputable def PhiT (fv gv : Fin n → ℝ) (G : Fin (n + n) → Fin (n + n) → ℝ) : ℝ :=
  (PhiL fv gv G - ∑ i, ∑ j, ipKQ fv gv G i j * ipQK fv gv G i j) / 2

private lemma frobL_eq_Phi {N : ℕ} (fv gv : Fin n → ℝ) (y : Fin (n + n) → EuclideanSpace ℝ (Fin N)) :
    frobL (qOf fv gv y) (kOf fv gv y) = PhiL fv gv (gram y) := by
  simp only [frobL, PhiL, inner_kk, inner_qq]

private lemma frobT_eq_Phi {N : ℕ} (fv gv : Fin n → ℝ) (y : Fin (n + n) → EuclideanSpace ℝ (Fin N)) :
    frobT (qOf fv gv y) (kOf fv gv y) = PhiT fv gv (gram y) := by
  simp only [frobT, PhiT, frobL_eq_Phi, inner_kq, inner_qk]

private lemma PhiL_cont (fv gv : Fin n → ℝ) : Continuous (PhiL fv gv) := by
  unfold PhiL ipKK ipQQ
  fun_prop

private lemma PhiT_cont (fv gv : Fin n → ℝ) : Continuous (PhiT fv gv) := by
  unfold PhiT
  have := PhiL_cont fv gv
  unfold ipKQ ipQK
  fun_prop

private lemma sum_ite_sq (u v : Fin n → ℝ) :
    ∑ i, ∑ j, (if i = j then u i else 0) * (if i = j then v i else 0) = ∑ i, u i * v i := by
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

private lemma PhiL_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i) :
    PhiL fv gv (idG _) = normSq fv gv := by
  simp only [PhiL, ipKK_id fv gv hf hg, ipQQ_id fv gv hf hg, sum_ite_sq, normSq, sq]

private lemma PhiT_id (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i) :
    PhiT fv gv (idG _) = 2 * ∑ i, fv i * gv i := by
  simp only [PhiT, PhiL_id fv gv hf hg, ipKQ_id fv gv hf hg, ipQK_id fv gv hf hg, sum_ite_sq,
    normSq, ← sum_sub_distrib, sum_div, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

private lemma normSq_pos' [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i)
    (hg : ∀ i, 0 < gv i) : 0 < normSq fv gv :=
  Finset.sum_pos (fun i _ => sq_pos_of_pos (add_pos (hf i) (hg i))) Finset.univ_nonempty

private lemma tendsto_of_abs_le {u b : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ N in atTop, |u N - L| ≤ b N) : Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [Real.norm_eq_abs] using h) hb

/-- Theorem B, deterministic form. -/
theorem profile_tendsto [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i)
    (hg : ∀ i, 0 < gv i) (x : (N : ℕ) → Fin (n + n) → EuclideanSpace ℝ (Fin N))
    (hG : ∀ a b, Tendsto (fun N => ⟪x N a, x N b⟫) atTop (𝓝 (if a = b then 1 else 0)))
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    Tendsto (fun N => gA (qOf fv gv (x N)) (kOf fv gv (x N))) atTop (𝓝 (profA fv gv)) ∧
    Tendsto (fun N => gB (qOf fv gv (x N)) (kOf fv gv (x N))) atTop (𝓝 (profB fv gv σ τ)) ∧
    Tendsto (fun N => gC (qOf fv gv (x N)) (kOf fv gv (x N))) atTop (𝓝 (profC fv gv σ τ)) ∧
    Tendsto (fun N => gD (qOf fv gv (x N)) (kOf fv gv (x N))) atTop (𝓝 (profD fv gv σ τ)) ∧
    (SimilarlyOrdered fv gv →
      Tendsto (fun N => gErr (qOf fv gv (x N)) (kOf fv gv (x N))) atTop (𝓝 0)) := by
  -- Gram convergence
  have hGt : Tendsto (fun N => gram (x N)) atTop (𝓝 (idG _)) :=
    tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hG a b
  have hFL : Tendsto (fun N => frobL (qOf fv gv (x N)) (kOf fv gv (x N))) atTop
      (𝓝 (normSq fv gv)) := by
    simp only [frobL_eq_Phi]
    rw [← PhiL_id fv gv hf hg]
    exact ((PhiL_cont fv gv).tendsto _).comp hGt
  have hFT : Tendsto (fun N => frobT (qOf fv gv (x N)) (kOf fv gv (x N))) atTop
      (𝓝 (2 * ∑ i, fv i * gv i)) := by
    simp only [frobT_eq_Phi]
    rw [← PhiT_id fv gv hf hg]
    exact ((PhiT_cont fv gv).tendsto _).comp hGt
  have hne : normSq fv gv ≠ 0 := (normSq_pos' fv gv hf hg).ne'
  -- Gram error
  have hε : Tendsto (fun N => gramErr (x N)) atTop (𝓝 0) := by
    have : Tendsto (fun N => gramErr (x N)) atTop
        (𝓝 (∑ a : Fin (n + n), ∑ b : Fin (n + n),
          |(if a = b then (1 : ℝ) else 0) - if a = b then 1 else 0|)) := by
      unfold gramErr
      refine tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ => ?_
      exact ((hG a b).sub tendsto_const_nhds).abs
    simpa using this
  set κ := kappa (AQ fv gv) (AK fv gv)
  set cN : ℕ → ℝ := fun N => gramErr (x N) * (2 + gramErr (x N)) * κ with hcN
  have hc0 : Tendsto cN atTop (𝓝 0) := by
    have := ((hε.mul ((tendsto_const_nhds (x := (2 : ℝ))).add hε)).mul
      (tendsto_const_nhds (x := κ)))
    simpa [hcN] using this
  have hc1 : Tendsto (fun N => cN N * (2 * κ + cN N)) atTop (𝓝 0) := by
    have := hc0.mul ((tendsto_const_nhds (x := 2 * κ)).add hc0)
    simpa using this
  have hev : ∀ᶠ N in atTop, 2 * n ≤ N ∧ gramErr (x N) < 1 :=
    (eventually_ge_atTop (2 * n)).and (hε.eventually (gt_mem_nhds zero_lt_one))
  have hP : ∀ j, Tendsto (fun N => lamP (qOf fv gv (x N)) (kOf fv gv (x N)) j) atTop
      (𝓝 (fv (σ j))) := fun j =>
    tendsto_of_abs_le hc0 (hev.mono fun N hN =>
      (step_bounds fv gv hf hg (x N) hN.1 hN.2 hσ hτ rfl).1 j)
  have hM : ∀ j, Tendsto (fun N => lamM (qOf fv gv (x N)) (kOf fv gv (x N)) j) atTop
      (𝓝 (gv (τ j))) := fun j =>
    tendsto_of_abs_le hc0 (hev.mono fun N hN =>
      (step_bounds fv gv hf hg (x N) hN.1 hN.2 hσ hτ rfl).2.1 j)
  refine ⟨?_, ?_, ?_, ?_, fun hso => ?_⟩
  · exact hFT.div hFL hne
  · unfold gB profB
    refine Tendsto.div (tendsto_const_nhds.mul (tendsto_finset_sum _ fun j _ => ?_)) hFL hne
    exact (hP j).mul (hM j)
  · unfold gC profC
    refine Tendsto.div (tendsto_finset_sum _ fun j _ => ?_) hFL hne
    exact (((hP j).sub (hM j)).max tendsto_const_nhds).pow 2
  · unfold gD profD
    refine Tendsto.div (tendsto_finset_sum _ fun j _ => ?_) hFL hne
    exact (((hM j).sub (hP j)).max tendsto_const_nhds).pow 2
  · have hT : ∀ j, Tendsto (fun N => sigT (qOf fv gv (x N)) (kOf fv gv (x N)) j) atTop
        (𝓝 (Real.sqrt (fv (σ j) * gv (τ j)))) := fun j =>
      (tendsto_of_abs_le hc1 (hev.mono fun N hN =>
        (step_bounds fv gv hf hg (x N) hN.1 hN.2 hσ hτ rfl).2.2 hso j)).sqrt
    have hnum := (tendsto_finset_sum Finset.univ fun j _ =>
      ((hT j).sub (((hP j).mul (hM j)).sqrt)).pow 2).sqrt
    have hden := (tendsto_finset_sum Finset.univ fun j _ => (hT j).pow 2).sqrt
    have hpos : Real.sqrt (∑ j : Fin n, Real.sqrt (fv (σ j) * gv (τ j)) ^ 2) ≠ 0 := by
      refine (Real.sqrt_pos.2 ?_).ne'
      exact Finset.sum_pos (fun j _ => sq_pos_of_pos (Real.sqrt_pos.2
        (mul_pos (hf _) (hg _)))) Finset.univ_nonempty
    have := hnum.div hden hpos
    simpa using this

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Rows of `[P; M]/√N`: entry `j` of row `a` is `Z_j(a)/√N`. -/
noncomputable def colVec (Z : ℕ → Ω → (Fin (n + n) → ℝ)) (ω : Ω) (N : ℕ) (a : Fin (n + n)) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (fun j => Z j ω a / Real.sqrt N)

private lemma colVec_inner (Z : ℕ → Ω → (Fin (n + n) → ℝ)) (ω : Ω) (N : ℕ) (a b : Fin (n + n)) :
    ⟪colVec Z ω N a, colVec Z ω N b⟫ = (N : ℝ)⁻¹ * ∑ j ∈ range N, Z j ω a * Z j ω b := by
  simp only [colVec, PiLp.inner_apply, EuclideanSpace.equiv, RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (N : ℝ)⁻¹ * (Z j ω a * Z j ω b)) N]
  apply sum_congr rfl
  intro j _
  have hN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  change (Z j ω b / Real.sqrt N) * (Z j ω a / Real.sqrt N) = _
  rw [div_mul_div_comm, hN, div_eq_inv_mul, mul_comm (Z j ω b)]

/-- **Theorem B.** Almost surely, the profile of `L_N` tends to the profile of
Theorem A with `α = f(ρ)`, `β = g(ρ)`, and, if `(f(ρ), g(ρ))` is similarly
ordered, the relation-(1) error tends to `0`. -/
theorem theoremB_ae [IsProbabilityMeasure μ] [NeZero n] (fv gv : Fin n → ℝ)
    (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (Z : ℕ → Ω → (Fin (n + n) → ℝ))
    (hmeas : ∀ j, Measurable (Z j))
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ))
    (hident : ∀ j, IdentDistrib (Z j) (Z 0) μ μ)
    (hcoord : iIndepFun (fun a ω => Z 0 ω a) μ)
    (hgauss : ∀ a, μ.map (fun ω => Z 0 ω a) = gaussianReal 0 1)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun N => gA (qOf fv gv (colVec Z ω N)) (kOf fv gv (colVec Z ω N))) atTop
        (𝓝 (profA fv gv)) ∧
      Tendsto (fun N => gB (qOf fv gv (colVec Z ω N)) (kOf fv gv (colVec Z ω N))) atTop
        (𝓝 (profB fv gv σ τ)) ∧
      Tendsto (fun N => gC (qOf fv gv (colVec Z ω N)) (kOf fv gv (colVec Z ω N))) atTop
        (𝓝 (profC fv gv σ τ)) ∧
      Tendsto (fun N => gD (qOf fv gv (colVec Z ω N)) (kOf fv gv (colVec Z ω N))) atTop
        (𝓝 (profD fv gv σ τ)) ∧
      (SimilarlyOrdered fv gv →
        Tendsto (fun N => gErr (qOf fv gv (colVec Z ω N)) (kOf fv gv (colVec Z ω N))) atTop
          (𝓝 0)) := by
  have hint := gaussian_prod_integrable (Z 0) (hmeas 0) hcoord hgauss
  have hmom := gaussian_second_moment (Z 0) (hmeas 0) hcoord hgauss
  have h := gram_slln Z hmeas hindep hident hint hmom
  filter_upwards [h] with ω hω
  refine profile_tendsto fv gv hf hg (colVec Z ω) (fun a b => ?_) hσ hτ
  refine (hω a b).congr (fun N => ?_)
  rw [colVec_inner]

end Odesky
