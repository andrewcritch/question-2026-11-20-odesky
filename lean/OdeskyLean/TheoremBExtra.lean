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
  intro i j
  rcases le_total (x i) (x j) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr (hg h))
  · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr (hg h))

theorem limit_a_eq_b {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y) (x : Fin n → ℝ)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc (f ∘ x) σ) (hτ : SortsDesc (g ∘ x) τ) :
    profA (f ∘ x) (g ∘ x) = profB (f ∘ x) (g ∘ x) σ τ := by
  exact (profA_eq_profB_iff _ _ (fun i => hfpos _) (fun i => hgpos _) hσ hτ).mpr
    (similarlyOrdered_of_monotone f g hf hg x)

theorem limit_mem_Theta {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y)
    (hsign : (∀ y, g y ≤ f y) ∨ (∀ y, f y ≤ g y)) (x : Fin n → ℝ)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc (f ∘ x) σ) (hτ : SortsDesc (g ∘ x) τ) :
    profA (f ∘ x) (g ∘ x) = profB (f ∘ x) (g ∘ x) σ τ ∧
      profC (f ∘ x) (g ∘ x) σ τ * profD (f ∘ x) (g ∘ x) σ τ = 0 := by
  refine (mem_Theta_iff _ _ (fun i => hfpos _) (fun i => hgpos _) hσ hτ).mpr
    ⟨similarlyOrdered_of_monotone f g hf hg x, ?_⟩
  rcases hsign with h | h
  · exact Or.inl (fun i => h _)
  · exact Or.inr (fun i => h _)

/-- `c - d` of the limit form `L_∞`, using a decreasing sort of each list. -/
noncomputable def cdOf (f g : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  profC (f ∘ x) (g ∘ x) (exists_sortsDesc (f ∘ x)).choose (exists_sortsDesc (g ∘ x)).choose -
    profD (f ∘ x) (g ∘ x) (exists_sortsDesc (f ∘ x)).choose (exists_sortsDesc (g ∘ x)).choose

theorem cd_eq_ratio {n : ℕ} [NeZero n] (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfpos : ∀ y, 0 < f y) (hgpos : ∀ y, 0 < g y) (x : Fin n → ℝ) :
    cdOf f g x = (∑ i, (f (x i) - g (x i)) * |f (x i) - g (x i)|) /
      ∑ i, (f (x i) + g (x i)) ^ 2 := by
  unfold cdOf profC profD
  rw [← sub_div, c_sub_d_num _ _ (similarlyOrdered_of_monotone f g hf hg x)
    (exists_sortsDesc (f ∘ x)).choose_spec (exists_sortsDesc (g ∘ x)).choose_spec]
  rfl

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
  have hint1 : Integrable (fun ω => (f (ρ 0 ω) - g (ρ 0 ω)) * |f (ρ 0 ω) - g (ρ 0 ω)|) μ := by
    refine hint.mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact ((((hfm.comp (hmeas 0)).sub (hgm.comp (hmeas 0)))).mul
        ((hfm.comp (hmeas 0)).sub (hgm.comp (hmeas 0))).abs).aestronglyMeasurable
    · have h1 := hfpos (ρ 0 ω)
      have h2 := hgpos (ρ 0 ω)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, ← sq, sq_abs]
      nlinarith
  have hpos : 0 < ∫ ω, (f (ρ 0 ω) + g (ρ 0 ω)) ^ 2 ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg _) hint]
    have : Function.support (fun ω => (f (ρ 0 ω) + g (ρ 0 ω)) ^ 2) = Set.univ := by
      ext ω
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (sq_pos_of_pos (add_pos (hfpos _) (hgpos _)))
    rw [this, measure_univ]
    exact one_pos
  have h := ratio_slln ρ hmeas hindep hident (fun y => (f y - g y) * |f y - g y|)
    (fun y => (f y + g y) ^ 2) ((hfm.sub hgm).mul (hfm.sub hgm).abs)
    ((hfm.add hgm).pow_const 2) hint1 hint hpos
  filter_upwards [h] with ω hω
  have h2 := hω.comp (tendsto_add_atTop_nat 1)
  refine h2.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [cd_eq_ratio f g hf hg hfpos hgpos, Fin.sum_univ_eq_sum_range
    (fun i => (f (ρ i ω) - g (ρ i ω)) * |f (ρ i ω) - g (ρ i ω)|),
    Fin.sum_univ_eq_sum_range (fun i => (f (ρ i ω) + g (ρ i ω)) ^ 2)]

end Odesky
