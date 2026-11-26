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
  sum of rank-one forms on orthogonal planes `L = Kᵀ Q` with `α_i = fv_i`, `β_i = gv_i`.
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

private lemma linear_gram_limit {m : ℕ} (z : ℕ → Fin m → ℝ)
    (h : ∀ a b, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N, z j a * z j b)
      atTop (𝓝 (if a = b then (1 : ℝ) else 0)))
    (a b c d : Fin m) (A B C D : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ range N,
      (A * z j a + B * z j b) * (C * z j c + D * z j d)) atTop
      (𝓝 (A * C * (if a = c then 1 else 0) +
        A * D * (if a = d then 1 else 0) +
        B * C * (if b = c then 1 else 0) +
        B * D * (if b = d then 1 else 0))) := by
  have hh := (((h a c).const_mul (A * C)).add
    ((h a d).const_mul (A * D))).add
    ((h b c).const_mul (B * C))
  have hh := hh.add ((h b d).const_mul (B * D))
  convert hh using 1
  ext N
  have he : ∀ j, (A * z j a + B * z j b) * (C * z j c + D * z j d) =
      A * C * (z j a * z j c) + A * D * (z j a * z j d) +
      B * C * (z j b * z j c) + B * D * (z j b * z j d) := by
    intro j
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

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
  classical
  have h := gram_slln Z hmeas hindep hident
    (gaussian_prod_integrable (Z 0) (hmeas 0) hcoord hgauss)
    (gaussian_second_moment (Z 0) (hmeas 0) hcoord hgauss)
  filter_upwards [h] with ω hω
  intro i l
  have hlin := linear_gram_limit (fun j => Z j ω) hω
    (Fin.castAdd n i) (Fin.natAdd n i) (Fin.castAdd n l) (Fin.natAdd n l)
  have heq : Fin.castAdd n i ≠ Fin.natAdd n l := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  have heq' : Fin.natAdd n i ≠ Fin.castAdd n l := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := l.isLt
    omega
  have hsfi := Real.sq_sqrt (le_of_lt (hf i))
  have hsgi := Real.sq_sqrt (le_of_lt (hg i))
  simp only [Fin.natAdd_eq_addNat] at heq heq'
  have hqq := hlin (Real.sqrt (fv i)) (-Real.sqrt (gv i))
    (Real.sqrt (fv l)) (-Real.sqrt (gv l))
  have hkk := hlin (Real.sqrt (fv i)) (Real.sqrt (gv i))
    (Real.sqrt (fv l)) (Real.sqrt (gv l))
  have hqk := hlin (Real.sqrt (fv i)) (-Real.sqrt (gv i))
    (Real.sqrt (fv l)) (Real.sqrt (gv l))
  by_cases hil : i = l
  · subst l
    simpa [qcol, kcol, sub_eq_add_neg, heq, heq', ← pow_two, hsfi, hsgi]
      using And.intro hqq (And.intro hkk hqk)
  · simpa [qcol, kcol, sub_eq_add_neg, heq, heq', hil]
      using And.intro hqq (And.intro hkk hqk)

/-- Theorem B, limit configuration: rows `q_i, k_i ∈ ℝᴺ` with
`⟪q_i, q_l⟫ = ⟪k_i, k_l⟫ = δ_il (fv_i + gv_i)` and `⟪q_i, k_l⟫ = δ_il (fv_i - gv_i)`
give a sum of rank-one forms on orthogonal planes with `L x = ∑ ⟪q_i, x⟫ k_i`,
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
  classical
  let r : Fin n → ℝ := fun i => Real.sqrt (fv i + gv i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (add_pos (hf i) (hg i))
  have hr0 : ∀ i, r i ≠ 0 := fun i => ne_of_gt (hr i)
  have hr2 : ∀ i, r i * r i = fv i + gv i := by
    intro i
    exact Real.mul_self_sqrt (le_of_lt (add_pos (hf i) (hg i)))
  have hnq : ∀ i, ‖q i‖ = r i := by
    intro i
    have hh := hqq i i
    simp only [ite_true, real_inner_self_eq_norm_sq] at hh
    have hh' := hr2 i
    nlinarith [norm_nonneg (q i), hr i]
  have hnk : ∀ i, ‖k i‖ = r i := by
    intro i
    have hh := hkk i i
    simp only [ite_true, real_inner_self_eq_norm_sq] at hh
    have hh' := hr2 i
    nlinarith [norm_nonneg (k i), hr i]
  let B : OrthoBlocks n N := {
    s := fun i => fv i + gv i
    u := fun i => (r i)⁻¹ • k i
    v := fun i => (r i)⁻¹ • q i
    s_pos := fun i => add_pos (hf i) (hg i)
    u_unit := by
      intro i
      simp [norm_smul, abs_of_pos (hr i), hnk, hr0]
    v_unit := by
      intro i
      simp [norm_smul, abs_of_pos (hr i), hnq, hr0]
    uu := by
      intro i j hij
      simp [real_inner_smul_left, real_inner_smul_right, hkk, hij]
    uv := by
      intro i j hij
      rw [real_inner_smul_left, real_inner_smul_right, ← real_inner_comm (k i) (q j)]
      simp [hqk, Ne.symm hij]
    vv := by
      intro i j hij
      simp [real_inner_smul_left, real_inner_smul_right, hqq, hij] }
  have ht : ∀ i, B.t i = (fv i - gv i) / (fv i + gv i) := by
    intro i
    change ⟪(r i)⁻¹ • k i, (r i)⁻¹ • q i⟫ = _
    rw [real_inner_smul_left, real_inner_smul_right, ← real_inner_comm (k i) (q i)]
    simp only [hqk, ite_true]
    rw [← hr2 i]
    field_simp [hr0 i]
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Finset.sum_congr rfl
    intro i _
    change ((fv i + gv i) * ⟪(r i)⁻¹ • q i, x⟫) • ((r i)⁻¹ • k i) = _
    rw [real_inner_smul_left, smul_smul, ← hr2 i]
    congr 1
    field_simp [hr0 i]
  · intro i
    rw [ht, abs_lt]
    constructor
    · apply (lt_div_iff₀ (add_pos (hf i) (hg i))).2
      linarith [hf i]
    · apply (div_lt_iff₀ (add_pos (hf i) (hg i))).2
      linarith [hg i]
  · intro i
    change (fv i + gv i) * (1 + B.t i) / 2 = fv i
    rw [ht]
    field_simp [ne_of_gt (add_pos (hf i) (hg i))]
    ring
  · intro i
    change (fv i + gv i) * (1 - B.t i) / 2 = gv i
    rw [ht]
    field_simp [ne_of_gt (add_pos (hf i) (hg i))]
    ring

end Odesky
