import OdeskyLean.Rearrangement

/-!
# Layer 2: Theorem A in terms of the profile `(a, b, c, d)`

For an orthogonal sum of rank-one forms with block eigenvalues `α, β > 0`,
Layer 3 shows: `λ₊` is `α` sorted decreasingly, `λ₋` is `β` sorted decreasingly,
`‖L‖² = ∑ (α_i + β_i)²`, and `‖T‖² = 2 ∑ α_i β_i`. This file takes those
values as the definition of the profile and proves Theorem A for it.
-/

open Finset

namespace Odesky

variable {n : ℕ}

/-- `‖L‖² = ∑ σ_i² = ∑ (α_i + β_i)²`. -/
noncomputable def normSq (α β : Fin n → ℝ) : ℝ := ∑ i, (α i + β i) ^ 2

/-- `a = ‖T‖² / ‖L‖²`, with `‖T‖² = 2 ∑ α_i β_i`. -/
noncomputable def profA (α β : Fin n → ℝ) : ℝ := 2 * (∑ i, α i * β i) / normSq α β

/-- `b = 2 ⟨λ₊, λ₋⟩ / ‖L‖²`, with `λ₊ = α ∘ σ`, `λ₋ = β ∘ τ`. -/
noncomputable def profB (α β : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  2 * (∑ k, α (σ k) * β (τ k)) / normSq α β

/-- `c = ‖(λ₊ - λ₋)₊‖² / ‖L‖²`. -/
noncomputable def profC (α β : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  (∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2) / normSq α β

/-- `d = ‖(λ₊ - λ₋)₋‖² / ‖L‖²`. -/
noncomputable def profD (α β : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  (∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2) / normSq α β

private theorem normSq_pos [NeZero n] (α β : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) : 0 < normSq α β := by
  unfold normSq
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (add_pos (hα i) (hβ i)))
    Finset.univ_nonempty

private theorem parts_sq (x y : ℝ) :
    (max (x - y) 0) ^ 2 + (max (y - x) 0) ^ 2 = (x - y) ^ 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring

/-- Consistency check: the four coordinates sum to one. -/
theorem prof_sum_eq_one [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β + profB α β σ τ + profC α β σ τ + profD α β σ τ = 1 := by
  have hn := ne_of_gt (normSq_pos α β hα hβ)
  have hs : (∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2) +
      (∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2) =
      (∑ i, α i ^ 2) + (∑ i, β i ^ 2) -
        2 * (∑ k, α (σ k) * β (τ k)) := by
    rw [← sum_add_distrib]
    simp_rw [parts_sq, sub_sq]
    simp only [sum_add_distrib, sum_sub_distrib, mul_sum,
      Equiv.sum_comp σ (fun i => α i ^ 2),
      Equiv.sum_comp τ (fun i => β i ^ 2)]
    simp_rw [mul_assoc]
    ring
  have hnexp : normSq α β = (∑ i, α i ^ 2) + (∑ i, β i ^ 2) +
      2 * (∑ i, α i * β i) := by
    unfold normSq
    simp_rw [add_sq]
    simp only [sum_add_distrib, mul_sum]
    ring
  unfold profA profB profC profD
  rw [← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hn]
  linarith

/-- Theorem A(i): `a ≤ b`. -/
theorem profA_le_profB [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β ≤ profB α β σ τ := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (blockwise_le_sorted α β hσ hτ) (by norm_num))
    (le_of_lt (normSq_pos α β hα hβ))

/-- Theorem A(i): `a = b` iff `(α, β)` is similarly ordered. -/
theorem profA_eq_profB_iff [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ i, 0 < β i) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β = profB α β σ τ ↔ SimilarlyOrdered α β := by
  unfold profA profB
  rw [div_left_inj' (ne_of_gt (normSq_pos α β hα hβ)),
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0)]
  exact blockwise_eq_sorted_iff α β hσ hτ

/-- Theorem A: `c - d = ∑ w_i t_i |t_i|`, with `σ_i = α_i + β_i`,
`t_i = (α_i - β_i)/(α_i + β_i)`, `w_i = σ_i² / ∑ σ_j²`. -/
theorem profC_sub_profD [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ i, 0 < β i) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profC α β σ τ - profD α β σ τ
      = ∑ i, ((α i + β i) ^ 2 / normSq α β)
          * ((α i - β i) / (α i + β i)) * |(α i - β i) / (α i + β i)| := by
  unfold profC profD
  rw [← sub_div, c_sub_d_num α β h hσ hτ, sum_div]
  apply sum_congr rfl
  intro i _
  have hp := add_pos (hα i) (hβ i)
  rw [abs_div, abs_of_pos hp]
  field_simp

/-- Theorem A (main statement): the profile lies on `Θ = {a = b, c d = 0}` iff
`(α, β)` is similarly ordered and the tilts all have one sign. -/
theorem mem_Theta_iff [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    (profA α β = profB α β σ τ ∧ profC α β σ τ * profD α β σ τ = 0) ↔
      (SimilarlyOrdered α β ∧ ((∀ i, β i ≤ α i) ∨ (∀ i, α i ≤ β i))) := by
  have hn := ne_of_gt (normSq_pos α β hα hβ)
  rw [profA_eq_profB_iff α β hα hβ hσ hτ]
  constructor
  · rintro ⟨h, hm⟩
    refine ⟨h, ?_⟩
    rcases mul_eq_zero.mp hm with hc | hd
    · exact Or.inr ((c_num_eq_zero_iff α β h hσ hτ).mp
        ((div_eq_zero_iff.mp hc).resolve_right hn))
    · exact Or.inl ((d_num_eq_zero_iff α β h hσ hτ).mp
        ((div_eq_zero_iff.mp hd).resolve_right hn))
  · rintro ⟨h, hs⟩
    refine ⟨h, ?_⟩
    rcases hs with hd | hc
    · have hz := (d_num_eq_zero_iff α β h hσ hτ).mpr hd
      simp [profD, hz]
    · have hz := (c_num_eq_zero_iff α β h hσ hτ).mpr hc
      simp [profC, hz]

end Odesky
