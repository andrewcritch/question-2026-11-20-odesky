import Mathlib

/-!
# Layer 9 (gap G2): the profile of a general form `L = Kᵀ Q`

Rows `q_i, k_i ∈ ℝᴺ` (`i < n`) define `L x = ∑ ⟪q_i, x⟫ k_i`, i.e., `L = Kᵀ Q`.
The spectral lists use Mathlib's decreasingly sorted eigenvalues of `S` and of
`TᵀT = -T²`:

* `lamP j = max (λ_j(S)) 0`, the `j`-th largest positive eigenvalue of `S`;
* `lamM j = max (-λ_{N-1-j}(S)) 0`, the `j`-th largest absolute negative eigenvalue;
* `sigT j = √(max (λ_{2j}(TᵀT)) 0)`, the singular values of `T` counted once.

Indices out of range read as `0` (`eigAt`), so no hypothesis `2n ≤ N` is needed to
define them. The Frobenius norms are written through the Gram matrix and checked
against an orthonormal basis.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- `L x = ∑ ⟪q_i, x⟫ k_i`. -/
noncomputable def formL (q k : Fin n → V) : V →ₗ[ℝ] V :=
  ∑ i, (innerSL ℝ (q i) : V →L[ℝ] ℝ).toLinearMap.smulRight (k i)

/-- `Lᵀ x = ∑ ⟪k_i, x⟫ q_i`. -/
noncomputable def formLt (q k : Fin n → V) : V →ₗ[ℝ] V :=
  ∑ i, (innerSL ℝ (k i) : V →L[ℝ] ℝ).toLinearMap.smulRight (q i)

noncomputable def formS (q k : Fin n → V) : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (formL q k + formLt q k)

noncomputable def formT (q k : Fin n → V) : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (formL q k - formLt q k)

private lemma formL_apply (q k : Fin n → V) (x : V) :
    formL q k x = ∑ i, ⟪q i, x⟫ • k i := by
  simp [formL, LinearMap.sum_apply]

private lemma formLt_apply (q k : Fin n → V) (x : V) :
    formLt q k x = ∑ i, ⟪k i, x⟫ • q i := by
  simp [formLt, LinearMap.sum_apply]

private lemma sum_inner_gen (a c d e : Fin n → V) (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ t, ⟪∑ i, ⟪a i, b t⟫ • c i, ∑ j, ⟪d j, b t⟫ • e j⟫ =
      ∑ i, ∑ j, ⟪c i, e j⟫ * ⟪a i, d j⟫ := by
  have h : ∀ t, ⟪∑ i, ⟪a i, b t⟫ • c i, ∑ j, ⟪d j, b t⟫ • e j⟫ =
      ∑ i, ∑ j, ⟪c i, e j⟫ * (⟪a i, b t⟫ * ⟪b t, d j⟫) := by
    intro t
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (b t) (d j)]; ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem formLt_adjoint (q k : Fin n → V) (x y : V) :
    ⟪formL q k x, y⟫ = ⟪x, formLt q k y⟫ := by
  rw [formL_apply, formLt_apply]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x (q i)]; ring

theorem formS_isSymmetric (q k : Fin n → V) : (formS q k).IsSymmetric := by
  intro x y
  have h1 := formLt_adjoint q k x y
  have h2 := formLt_adjoint q k y x
  simp only [formS, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, conj_trivial]
  rw [real_inner_comm x (formL q k y), real_inner_comm (formLt q k x) y] at h2
  linarith

theorem negTsq_isSymmetric (q k : Fin n → V) : (-(formT q k ∘ₗ formT q k)).IsSymmetric := by
  have hT : ∀ x y, ⟪formT q k x, y⟫ = -⟪x, formT q k y⟫ := by
    intro x y
    have h1 := formLt_adjoint q k x y
    have h2 := formLt_adjoint q k y x
    simp only [formT, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
      inner_smul_right, inner_sub_left, inner_sub_right, conj_trivial]
    rw [real_inner_comm x (formL q k y), real_inner_comm (formLt q k x) y] at h2
    linarith
  intro x y
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, inner_neg_left, inner_neg_right]
  rw [hT, hT, neg_neg]

/-- Sorted eigenvalues of `S`. -/
noncomputable def eigS (q k : Fin n → V) : Fin N → ℝ :=
  (formS_isSymmetric q k).eigenvalues finrank_euclideanSpace_fin

/-- Sorted eigenvalues of `TᵀT = -T²`. -/
noncomputable def eigT2 (q k : Fin n → V) : Fin N → ℝ :=
  (negTsq_isSymmetric q k).eigenvalues finrank_euclideanSpace_fin

/-- Entry `j` of a list of length `N`, or `0` out of range. -/
def eigAt (v : Fin N → ℝ) (j : ℕ) : ℝ := if h : j < N then v ⟨j, h⟩ else 0

noncomputable def lamP (q k : Fin n → V) (j : Fin n) : ℝ := max (eigAt (eigS q k) (j : ℕ)) 0

noncomputable def lamM (q k : Fin n → V) (j : Fin n) : ℝ :=
  max (-eigAt (eigS q k) (N - 1 - (j : ℕ))) 0

noncomputable def sigT (q k : Fin n → V) (j : Fin n) : ℝ :=
  Real.sqrt (max (eigAt (eigT2 q k) (2 * (j : ℕ))) 0)

/-- `‖L‖² = ∑_{ij} ⟪k_i, k_j⟫ ⟪q_i, q_j⟫`. -/
noncomputable def frobL (q k : Fin n → V) : ℝ := ∑ i, ∑ j, ⟪k i, k j⟫ * ⟪q i, q j⟫

/-- `‖T‖² = (‖L‖² - tr L²)/2`, with `tr L² = ∑_{ij} ⟪k_i, q_j⟫ ⟪q_i, k_j⟫`. -/
noncomputable def frobT (q k : Fin n → V) : ℝ :=
  (frobL q k - ∑ i, ∑ j, ⟪k i, q j⟫ * ⟪q i, k j⟫) / 2

theorem frobL_eq (q k : Fin n → V) (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ t, ‖formL q k (b t)‖ ^ 2 = frobL q k := by
  simp_rw [formL_apply, ← real_inner_self_eq_norm_sq]
  rw [sum_inner_gen, frobL]

theorem frobT_eq (q k : Fin n → V) (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ t, ‖formT q k (b t)‖ ^ 2 = frobT q k := by
  have h : ∀ t, ‖formT q k (b t)‖ ^ 2 = (1 / 4 : ℝ) * (⟪formL q k (b t), formL q k (b t)⟫
      - 2 * ⟪formL q k (b t), formLt q k (b t)⟫ + ⟪formLt q k (b t), formLt q k (b t)⟫) := by
    intro t
    rw [← real_inner_self_eq_norm_sq]
    simp only [formT, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left,
      inner_smul_right, inner_sub_left, inner_sub_right, conj_trivial]
    rw [real_inner_comm (formLt q k (b t)) (formL q k (b t))]
    ring
  simp_rw [h, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp_rw [formL_apply, formLt_apply]
  rw [sum_inner_gen, sum_inner_gen, sum_inner_gen, frobT, frobL]
  have e : ∑ i, ∑ j, ⟪q i, q j⟫ * ⟪k i, k j⟫ = ∑ i, ∑ j, ⟪k i, k j⟫ * ⟪q i, q j⟫ := by
    simp_rw [mul_comm]
  rw [e]
  ring

/-- The profile `(a, b, c, d)` and the relation-(1) error of a general form. -/
noncomputable def gA (q k : Fin n → V) : ℝ := frobT q k / frobL q k

noncomputable def gB (q k : Fin n → V) : ℝ := 2 * (∑ j, lamP q k j * lamM q k j) / frobL q k

noncomputable def gC (q k : Fin n → V) : ℝ :=
  (∑ j, (max (lamP q k j - lamM q k j) 0) ^ 2) / frobL q k

noncomputable def gD (q k : Fin n → V) : ℝ :=
  (∑ j, (max (lamM q k j - lamP q k j) 0) ^ 2) / frobL q k

/-- `‖σ(T) - √(λ₊ λ₋)‖ / ‖σ(T)‖`. -/
noncomputable def gErr (q k : Fin n → V) : ℝ :=
  Real.sqrt (∑ j, (sigT q k j - Real.sqrt (lamP q k j * lamM q k j)) ^ 2) /
    Real.sqrt (∑ j, sigT q k j ^ 2)

end Odesky
