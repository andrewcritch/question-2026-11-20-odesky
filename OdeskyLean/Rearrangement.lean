import Mathlib

/-!
# Layer 1: the rearrangement core of Theorem A

Finite lists `α β : Fin n → ℝ` are the block eigenvalues `α_i = σ_i(1+t_i)/2`,
`β_i = σ_i(1-t_i)/2` of an orthogonal sum of rank-one forms. Sorting is
expressed by a permutation that makes the list antitone, so no sorting function
is needed.
-/

open Finset

namespace Odesky

/-- `α, β` are similarly ordered: `(α i - α j) (β i - β j) ≥ 0` for all `i, j`. -/
def SimilarlyOrdered {n : ℕ} (α β : Fin n → ℝ) : Prop :=
  ∀ i j, 0 ≤ (α i - α j) * (β i - β j)

/-- The permutation `σ` sorts `f` in decreasing order. -/
def SortsDesc {n : ℕ} (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  Antitone (f ∘ σ)

/-- Every list has a decreasing sort. -/
theorem exists_sortsDesc {n : ℕ} (f : Fin n → ℝ) : ∃ σ, SortsDesc f σ := by
  sorry

/-- The sorted values do not depend on which sorting permutation is used. -/
theorem sortsDesc_unique {n : ℕ} (f : Fin n → ℝ) {σ σ' : Equiv.Perm (Fin n)}
    (h : SortsDesc f σ) (h' : SortsDesc f σ') : f ∘ σ = f ∘ σ' := by
  sorry

/-- Similarly ordered iff one permutation sorts both lists. -/
theorem similarlyOrdered_iff_common_sort {n : ℕ} (α β : Fin n → ℝ) :
    SimilarlyOrdered α β ↔ ∃ π, SortsDesc α π ∧ SortsDesc β π := by
  sorry

/-- Theorem A(i), inequality (`a ≤ b`): the blockwise pairing is at most the
sorted pairing. -/
theorem blockwise_le_sorted {n : ℕ} (α β : Fin n → ℝ) {σ τ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ i, α i * β i ≤ ∑ k, α (σ k) * β (τ k) := by
  sorry

/-- Theorem A(i), equality case (`a = b` iff similarly ordered). -/
theorem blockwise_eq_sorted_iff {n : ℕ} (α β : Fin n → ℝ) {σ τ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ i, α i * β i = ∑ k, α (σ k) * β (τ k) ↔ SimilarlyOrdered α β := by
  sorry

/-- Theorem A(ii), relation (1): for similarly ordered nonnegative lists, the
sorted list of blockwise geometric means `√(α_i β_i)` equals the list of
geometric means of the separately sorted lists. -/
theorem relation_one {n : ℕ} (α β : Fin n → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h : SimilarlyOrdered α β) {σ τ ρ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ)
    (hρ : SortsDesc (fun i => Real.sqrt (α i * β i)) ρ) :
    ∀ k, Real.sqrt (α (ρ k) * β (ρ k)) = Real.sqrt (α (σ k) * β (τ k)) := by
  sorry

/-- Theorem A(ii), `c - d` (numerators): for similarly ordered lists, the sum of
squared positive parts minus the sum of squared negative parts of the sorted
differences equals `∑ (α_i - β_i) |α_i - β_i|`. -/
theorem c_sub_d_num {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2 - ∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2
      = ∑ i, (α i - β i) * |α i - β i| := by
  sorry

/-- Theorem A(ii): for similarly ordered lists, `d = 0` iff every `β_i ≤ α_i`
(every tilt `t_i ≥ 0`). -/
theorem d_num_eq_zero_iff {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2 = 0 ↔ ∀ i, β i ≤ α i := by
  sorry

/-- Theorem A(ii): for similarly ordered lists, `c = 0` iff every `α_i ≤ β_i`
(every tilt `t_i ≤ 0`). -/
theorem c_num_eq_zero_iff {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2 = 0 ↔ ∀ i, α i ≤ β i := by
  sorry

end Odesky
