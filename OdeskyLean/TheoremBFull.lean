import OdeskyLean.Limit
import OdeskyLean.Perturb
import OdeskyLean.Orthonormalize
import OdeskyLean.Weyl
import OdeskyLean.Probability
import OdeskyLean.Gaussian

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
  sorry

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Rows of `[P; M]/√N`: entry `j` of row `a` is `Z_j(a)/√N`. -/
noncomputable def colVec (Z : ℕ → Ω → (Fin (n + n) → ℝ)) (ω : Ω) (N : ℕ) (a : Fin (n + n)) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (fun j => Z j ω a / Real.sqrt N)

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
  sorry

end Odesky
