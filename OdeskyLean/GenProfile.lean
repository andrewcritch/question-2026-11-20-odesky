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

theorem formLt_adjoint (q k : Fin n → V) (x y : V) :
    ⟪formL q k x, y⟫ = ⟪x, formLt q k y⟫ := by
  sorry

theorem formS_isSymmetric (q k : Fin n → V) : (formS q k).IsSymmetric := by
  sorry

theorem negTsq_isSymmetric (q k : Fin n → V) : (-(formT q k ∘ₗ formT q k)).IsSymmetric := by
  sorry

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
  sorry

theorem frobT_eq (q k : Fin n → V) (b : OrthonormalBasis (Fin N) ℝ V) :
    ∑ t, ‖formT q k (b t)‖ ^ 2 = frobT q k := by
  sorry

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
