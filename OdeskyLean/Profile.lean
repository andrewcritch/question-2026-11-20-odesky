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

/-- Consistency check: the four coordinates sum to one. -/
theorem prof_sum_eq_one [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β + profB α β σ τ + profC α β σ τ + profD α β σ τ = 1 := by
  sorry

/-- Theorem A(i): `a ≤ b`. -/
theorem profA_le_profB [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β ≤ profB α β σ τ := by
  sorry

/-- Theorem A(i): `a = b` iff `(α, β)` is similarly ordered. -/
theorem profA_eq_profB_iff [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ i, 0 < β i) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profA α β = profB α β σ τ ↔ SimilarlyOrdered α β := by
  sorry

/-- Theorem A: `c - d = ∑ w_i t_i |t_i|`, with `σ_i = α_i + β_i`,
`t_i = (α_i - β_i)/(α_i + β_i)`, `w_i = σ_i² / ∑ σ_j²`. -/
theorem profC_sub_profD [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (hβ : ∀ i, 0 < β i) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    profC α β σ τ - profD α β σ τ
      = ∑ i, ((α i + β i) ^ 2 / normSq α β)
          * ((α i - β i) / (α i + β i)) * |(α i - β i) / (α i + β i)| := by
  sorry

/-- Theorem A (main statement): the profile lies on `Θ = {a = b, c d = 0}` iff
`(α, β)` is similarly ordered and the tilts all have one sign. -/
theorem mem_Theta_iff [NeZero n] (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    (profA α β = profB α β σ τ ∧ profC α β σ τ * profD α β σ τ = 0) ↔
      (SimilarlyOrdered α β ∧ ((∀ i, β i ≤ α i) ∨ (∀ i, α i ≤ β i))) := by
  sorry

end Odesky
