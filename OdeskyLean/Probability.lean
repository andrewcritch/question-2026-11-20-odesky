import Mathlib

/-!
# Layer 4: the probability steps of Theorem B

* `gram_slln`: the normalized Gram matrix of `N` i.i.d. columns converges almost
  surely to the identity (proof step 4: `PPᵀ/N → I`, `MMᵀ/N → I`, `PMᵀ/N → 0`,
  applied to the stacked columns of `[P; M]`).
* `limit_of_continuousAt`: a function of the Gram matrix that is continuous at
  the limit converges almost surely. The continuity of the profile and of the
  relation-(1) error in the Gram matrix is a hypothesis here, not a theorem.
* `ratio_slln`: the position on `Θ` (proof step 6): the ratio of two sample
  means converges almost surely to the ratio of the expectations.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Odesky

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Proof step 4 (Gram matrix). Columns `Z j : Ω → (Fin m → ℝ)` are pairwise
independent and identically distributed, every product of two coordinates of
`Z 0` is integrable, and `E[Z₀ a · Z₀ b] = 1` if `a = b`, else `0`. Then almost
surely, for all `a b`, `N⁻¹ ∑_{j<N} Z_j a · Z_j b → (1 if a = b else 0)`. -/
theorem gram_slln [IsProbabilityMeasure μ] {m : ℕ} (Z : ℕ → Ω → (Fin m → ℝ))
    (hmeas : ∀ j, Measurable (Z j))
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) μ))
    (hident : ∀ j, IdentDistrib (Z j) (Z 0) μ μ)
    (hint : ∀ a b, Integrable (fun ω => Z 0 ω a * Z 0 ω b) μ)
    (hmom : ∀ a b, ∫ ω, Z 0 ω a * Z 0 ω b ∂μ = if a = b then 1 else 0) :
    ∀ᵐ ω ∂μ, ∀ a b, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N, Z j ω a * Z j ω b) atTop
      (𝓝 (if a = b then 1 else 0)) := by
  classical
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  have hm : Measurable (fun z : Fin m → ℝ => z a * z b) :=
    (measurable_pi_apply a).mul (measurable_pi_apply b)
  have h := strong_law_ae_real (fun j ω => Z j ω a * Z j ω b) (hint a b)
    (fun i j hij => (hindep hij).comp hm hm)
    (fun j => (hident j).comp hm)
  simpa only [hmom a b, div_eq_mul_inv, mul_comm] using h

/-- Proof step 4 (continuity). If `G N ω → G∞` almost surely and `Φ` is
continuous at `G∞`, then `Φ (G N ω) → Φ G∞` almost surely. -/
theorem limit_of_continuousAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : ℕ → Ω → X) (Ginf : X) (Φ : X → Y) (hΦ : ContinuousAt Φ Ginf)
    (hG : ∀ᵐ ω ∂μ, Tendsto (fun N => G N ω) atTop (𝓝 Ginf)) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => Φ (G N ω)) atTop (𝓝 (Φ Ginf)) := by
  filter_upwards [hG] with ω hω
  exact hΦ.tendsto.comp hω

/-- Proof step 6 (position on `Θ`). Let `ρ_i` be pairwise independent and
identically distributed, `h₁ h₂ : ℝ → ℝ` measurable with `h₁ ∘ ρ₀`, `h₂ ∘ ρ₀`
integrable and `E h₂(ρ₀) > 0`. Then almost surely
`(∑_{i<n} h₁(ρ_i)) / (∑_{i<n} h₂(ρ_i)) → E h₁(ρ₀) / E h₂(ρ₀)`.
Theorem B uses `h₁ = (f-g)|f-g|` and `h₂ = (f+g)²`. -/
theorem ratio_slln [IsProbabilityMeasure μ] (ρ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ρ i))
    (hindep : Pairwise (fun i j => IndepFun (ρ i) (ρ j) μ))
    (hident : ∀ i, IdentDistrib (ρ i) (ρ 0) μ μ)
    (h₁ h₂ : ℝ → ℝ) (hm₁ : Measurable h₁) (hm₂ : Measurable h₂)
    (hi₁ : Integrable (fun ω => h₁ (ρ 0 ω)) μ) (hi₂ : Integrable (fun ω => h₂ (ρ 0 ω)) μ)
    (hpos : 0 < ∫ ω, h₂ (ρ 0 ω) ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ range n, h₁ (ρ i ω)) / (∑ i ∈ range n, h₂ (ρ i ω))) atTop
      (𝓝 ((∫ ω, h₁ (ρ 0 ω) ∂μ) / ∫ ω, h₂ (ρ 0 ω) ∂μ)) := by
  have hA := strong_law_ae_real (fun i ω => h₁ (ρ i ω)) hi₁
    (fun i j hij => (hindep hij).comp hm₁ hm₁)
    (fun i => (hident i).comp hm₁)
  have hB := strong_law_ae_real (fun i ω => h₂ (ρ i ω)) hi₂
    (fun i j hij => (hindep hij).comp hm₂ hm₂)
    (fun i => (hident i).comp hm₂)
  filter_upwards [hA, hB] with ω hAω hBω
  have hquot := hAω.div hBω (ne_of_gt hpos)
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  exact div_div_div_cancel_right₀ hn' _ _

end Odesky
