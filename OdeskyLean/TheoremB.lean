import OdeskyLean.Probability
import OdeskyLean.Gaussian
import OdeskyLean.Geometry

/-!
# Theorem B: the ensemble's Gram matrix and its limit configuration

Condition on the latent strengths, so `fv i = f(ρ_i) > 0` and `gv i = g(ρ_i) > 0`
are fixed. Column `j` of `[P; M]` is `Z j : Ω → (Fin (n + n) → ℝ)`; its first
`n` coordinates are column `j` of `P` and its last `n` are column `j` of `M`.
Column `j` of `√N Q` and `√N K` is

  `q_j i = √fv_i P_ij - √gv_i M_ij`,   `k_j i = √fv_i P_ij + √gv_i M_ij`.

The Gram entries of the rows of `Q, K` are `N⁻¹ ∑_{j<N} q_j i q_j l`, etc.

* `gram_limit`: almost surely, `⟨Q_i, Q_l⟩ → δ_il (fv_i + gv_i)`,
  `⟨K_i, K_l⟩ → δ_il (fv_i + gv_i)`, `⟨Q_i, K_l⟩ → δ_il (fv_i - gv_i)`.
* `blocks_of_limit_gram`: rows with exactly these Gram entries form an
  orthogonal sum of rank-one forms `L = Kᵀ Q` with `α_i = fv_i`, `β_i = gv_i`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology RealInnerProductSpace

namespace Odesky

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Column `j` of `√N Q`. -/
noncomputable def qcol {n : ℕ} (fv gv : Fin n → ℝ) (z : Fin (n + n) → ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (fv i) * z (Fin.castAdd n i) - Real.sqrt (gv i) * z (Fin.natAdd n i)

/-- Column `j` of `√N K`. -/
noncomputable def kcol {n : ℕ} (fv gv : Fin n → ℝ) (z : Fin (n + n) → ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (fv i) * z (Fin.castAdd n i) + Real.sqrt (gv i) * z (Fin.natAdd n i)

/-- Theorem B, Gram step: the Gram matrix of the rows of `Q, K` converges almost
surely to that of the limit configuration. -/
theorem gram_limit [IsProbabilityMeasure μ] {n : ℕ} (fv gv : Fin n → ℝ)
    (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (Z : ℕ → Ω → (Fin (n + n) → ℝ))
    (hmeas : ∀ j, Measurable (Z j))
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ))
    (hident : ∀ j, IdentDistrib (Z j) (Z 0) μ μ)
    (hcoord : iIndepFun (fun a ω => Z 0 ω a) μ)
    (hgauss : ∀ a, μ.map (fun ω => Z 0 ω a) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ i l,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N,
          qcol fv gv (Z j ω) i * qcol fv gv (Z j ω) l) atTop
        (𝓝 (if i = l then fv i + gv i else 0)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N,
          kcol fv gv (Z j ω) i * kcol fv gv (Z j ω) l) atTop
        (𝓝 (if i = l then fv i + gv i else 0)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N,
          qcol fv gv (Z j ω) i * kcol fv gv (Z j ω) l) atTop
        (𝓝 (if i = l then fv i - gv i else 0)) := by
  sorry

/-- Theorem B, limit configuration: rows `q_i, k_i ∈ ℝᴺ` with
`⟪q_i, q_l⟫ = ⟪k_i, k_l⟫ = δ_il (fv_i + gv_i)` and `⟪q_i, k_l⟫ = δ_il (fv_i - gv_i)`
give an orthogonal sum of rank-one forms with `L x = ∑ ⟪q_i, x⟫ k_i`,
`α_i = fv_i` and `β_i = gv_i`. -/
theorem blocks_of_limit_gram {n N : ℕ} (fv gv : Fin n → ℝ)
    (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (q k : Fin n → EuclideanSpace ℝ (Fin N))
    (hqq : ∀ i l, ⟪q i, q l⟫ = if i = l then fv i + gv i else 0)
    (hkk : ∀ i l, ⟪k i, k l⟫ = if i = l then fv i + gv i else 0)
    (hqk : ∀ i l, ⟪q i, k l⟫ = if i = l then fv i - gv i else 0) :
    ∃ B : OrthoBlocks n N,
      (∀ x, B.L x = ∑ i, ⟪q i, x⟫ • k i) ∧ (∀ i, |B.t i| < 1) ∧
      (∀ i, B.α i = fv i) ∧ (∀ i, B.β i = gv i) := by
  sorry

end Odesky
