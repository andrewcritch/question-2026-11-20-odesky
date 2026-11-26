import OdeskyLean.Profile
import OdeskyLean.Probability

/-!
# Theorem 2, consequences and the limit of `c - d`

For the limit form `L_∞` (block eigenvalues `α_i = f(ρ_i)`, `β_i = g(ρ_i)`):

* `similarlyOrdered_of_monotone`: nondecreasing `f, g` give similarly ordered blocks.
* `limit_a_eq_b`: hence `a = b` for `L_∞`.
* `limit_mem_Theta`: if moreover `f - g` does not change sign, `π(L_∞) ∈ Θ`.
* `cd_eq_ratio`: `c(L_∞) - d(L_∞) = R_n := ∑ (f-g)|f-g|(ρ_i) / ∑ (f+g)²(ρ_i)`.
* `cd_limit_ae`: almost surely, as `n → ∞`, `c(L_∞) - d(L_∞)` converges to
  `E[(f-g)|f-g|(ρ)] / E[(f+g)²(ρ)]`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Odesky

theorem similarlyOrdered_of_monotone {n : ℕ} (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (x : Fin n → ℝ) : SimilarlyOrdered (f ∘ x) (g ∘ x) := by
  sorry

theorem limit_a_eq_b {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y) (x : Fin n → ℝ)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc (f ∘ x) σ) (hτ : SortsDesc (g ∘ x) τ) :
    profA (f ∘ x) (g ∘ x) = profB (f ∘ x) (g ∘ x) σ τ := by
  sorry

theorem limit_mem_Theta {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y)
    (hsign : (∀ y, g y ≤ f y) ∨ (∀ y, f y ≤ g y)) (x : Fin n → ℝ)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc (f ∘ x) σ) (hτ : SortsDesc (g ∘ x) τ) :
    profA (f ∘ x) (g ∘ x) = profB (f ∘ x) (g ∘ x) σ τ ∧
      profC (f ∘ x) (g ∘ x) σ τ * profD (f ∘ x) (g ∘ x) σ τ = 0 := by
  sorry

/-- `c - d` of the limit form `L_∞`, using a decreasing sort of each list. -/
noncomputable def cdOf (f g : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  profC (f ∘ x) (g ∘ x) (exists_sortsDesc (f ∘ x)).choose (exists_sortsDesc (g ∘ x)).choose -
    profD (f ∘ x) (g ∘ x) (exists_sortsDesc (f ∘ x)).choose (exists_sortsDesc (g ∘ x)).choose

theorem cd_eq_ratio {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y) (x : Fin n → ℝ) :
    cdOf f g x = (∑ i, (f (x i) - g (x i)) * |f (x i) - g (x i)|) /
      ∑ i, (f (x i) + g (x i)) ^ 2 := by
  sorry

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Theorem 2, last part: almost surely, as `n → ∞`, `c(L_∞) - d(L_∞)` for the
first `n + 1` latent strengths converges to `E[(f-g)|f-g|(ρ)] / E[(f+g)²(ρ)]`. -/
theorem cd_limit_ae [IsProbabilityMeasure μ] (ρ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ρ i))
    (hindep : Pairwise (fun i j => IndepFun (ρ i) (ρ j) μ))
    (hident : ∀ i, IdentDistrib (ρ i) (ρ 0) μ μ)
    (f g : ℝ → ℝ) (hfm : Measurable f) (hgm : Measurable g) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y)
    (hint : Integrable (fun ω => (f (ρ 0 ω) + g (ρ 0 ω)) ^ 2) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => cdOf f g (fun i : Fin (n + 1) => ρ i ω)) atTop
      (𝓝 ((∫ ω, (f (ρ 0 ω) - g (ρ 0 ω)) * |f (ρ 0 ω) - g (ρ 0 ω)| ∂μ) /
        ∫ ω, (f (ρ 0 ω) + g (ρ 0 ω)) ^ 2 ∂μ)) := by
  sorry

end Odesky
