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

/-- Weyl's inequality, one side. -/
theorem weyl_le {d : ℕ} (hd : Module.finrank ℝ E = d) {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c : ℝ}
    (hc : ∀ x, ⟪(A - B) x, x⟫ ≤ c * ‖x‖ ^ 2) (k : Fin d) :
    hA.eigenvalues hd k ≤ hB.eigenvalues hd k + c := by
  sorry

/-- Weyl's inequality: sorted eigenvalues move by at most the quadratic-form size
of the perturbation. -/
theorem weyl_abs {d : ℕ} (hd : Module.finrank ℝ E = d) {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c : ℝ}
    (hc : ∀ x, |⟪(A - B) x, x⟫| ≤ c * ‖x‖ ^ 2) (k : Fin d) :
    |hA.eigenvalues hd k - hB.eigenvalues hd k| ≤ c := by
  sorry

/-- The roots of the characteristic polynomial of a symmetric operator are its
sorted eigenvalues, with multiplicity. -/
theorem roots_charpoly_eq_eigenvalues {d : ℕ} (hd : Module.finrank ℝ E = d)
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) :
    A.charpoly.roots = Multiset.map (hA.eigenvalues hd) univ.val := by
  sorry

end Odesky
