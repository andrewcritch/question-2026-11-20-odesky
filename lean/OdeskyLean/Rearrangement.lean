import Mathlib

/-!
# Layer 1: the rearrangement core of Theorem A

Finite lists `α β : Fin n → ℝ` are the block eigenvalues `α_i = σ_i(1+t_i)/2`,
`β_i = σ_i(1-t_i)/2` of a sum of rank-one forms on orthogonal planes. Sorting is
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
  exact ⟨Tuple.sort (fun i => OrderDual.toDual (f i)), Tuple.monotone_sort (fun i => OrderDual.toDual (f i))⟩

/-- The sorted values do not depend on which sorting permutation is used. -/
theorem sortsDesc_unique {n : ℕ} (f : Fin n → ℝ) {σ σ' : Equiv.Perm (Fin n)}
    (h : SortsDesc f σ) (h' : SortsDesc f σ') : f ∘ σ = f ∘ σ' := by
  exact Tuple.unique_antitone h h'

/-- Similarly ordered iff one permutation sorts both lists. -/
theorem similarlyOrdered_iff_common_sort {n : ℕ} (α β : Fin n → ℝ) :
    SimilarlyOrdered α β ↔ ∃ π, SortsDesc α π ∧ SortsDesc β π := by
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := exists_sortsDesc (fun i => α i + β i)
    refine ⟨π, ?_, ?_⟩
    · intro i j hij
      have hs := hπ hij
      have hp := h (π i) (π j)
      change α (π j) + β (π j) ≤ α (π i) + β (π i) at hs
      change α (π j) ≤ α (π i)
      nlinarith
    · intro i j hij
      have hs := hπ hij
      have hp := h (π i) (π j)
      change α (π j) + β (π j) ≤ α (π i) + β (π i) at hs
      change β (π j) ≤ β (π i)
      nlinarith
  · rintro ⟨π, ha, hb⟩ i j
    obtain hij | hij := le_total (π.symm i) (π.symm j)
    · have ha1 := ha hij
      have hb1 := hb hij
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at ha1 hb1
      exact mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
    · have ha1 := ha hij
      have hb1 := hb hij
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at ha1 hb1
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ha1) (sub_nonpos.mpr hb1)

/-- Theorem A(i), inequality (`a ≤ b`): the blockwise pairing is at most the
sorted pairing. -/
theorem blockwise_le_sorted {n : ℕ} (α β : Fin n → ℝ) {σ τ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ i, α i * β i ≤ ∑ k, α (σ k) * β (τ k) := by
  have hm := hσ.monovary hτ
  have hh := hm.sum_mul_comp_perm_le_sum_mul (σ := σ.trans τ.symm)
  simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sum_comp σ (fun i => α i * β i)] using hh

/-- Theorem A(i), equality case (`a = b` iff similarly ordered). -/
theorem blockwise_eq_sorted_iff {n : ℕ} (α β : Fin n → ℝ) {σ τ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ i, α i * β i = ∑ k, α (σ k) * β (τ k) ↔ SimilarlyOrdered α β := by
  have hm := hσ.monovary hτ
  have hh := hm.sum_mul_comp_perm_eq_sum_mul_iff (σ := σ.trans τ.symm)
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sum_comp σ (fun i => α i * β i)] at hh
  constructor
  · intro he
    have hv := hh.mp he
    have hv1 : Monovary α β := by
      intro i j hij
      simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hv (i := σ.symm i) (j := σ.symm j) (by simpa using hij)
    intro i j
    obtain hb | hb := le_total (β i) (β j)
    · obtain he | hl := hb.eq_or_lt
      · simp [he]
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hv1 hl)) (sub_nonpos.mpr hb)
    · obtain he | hl := hb.eq_or_lt
      · simp [he]
      · exact mul_nonneg (sub_nonneg.mpr (hv1 hl)) (sub_nonneg.mpr hb)
  · intro h
    apply hh.mpr
    intro i j hij
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at hij
    change α (σ i) ≤ α (σ j)
    have hp := h (σ i) (σ j)
    nlinarith

/-- Theorem A(ii), relation (1): for similarly ordered nonnegative lists, the
sorted list of blockwise geometric means `√(α_i β_i)` equals the list of
geometric means of the separately sorted lists. -/
theorem relation_one {n : ℕ} (α β : Fin n → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h : SimilarlyOrdered α β) {σ τ ρ : Equiv.Perm (Fin n)}
    (hσ : SortsDesc α σ) (hτ : SortsDesc β τ)
    (hρ : SortsDesc (fun i => Real.sqrt (α i * β i)) ρ) :
    ∀ k, Real.sqrt (α (ρ k) * β (ρ k)) = Real.sqrt (α (σ k) * β (τ k)) := by
  obtain ⟨π, ha, hb⟩ := (similarlyOrdered_iff_common_sort α β).mp h
  have ea := sortsDesc_unique α ha hσ
  have eb := sortsDesc_unique β hb hτ
  have hp : SortsDesc (fun i => Real.sqrt (α i * β i)) π := by
    intro i j hij
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (ha hij) (hb hij) (hβ _) (hα _)
  have ep := sortsDesc_unique _ hρ hp
  intro k
  have eak := congrFun ea k
  have ebk := congrFun eb k
  have epk := congrFun ep k
  simp only [Function.comp_apply] at eak ebk epk
  simpa only [eak, ebk] using epk

/-- Theorem A(ii), `c - d` (numerators): for similarly ordered lists, the sum of
squared positive parts minus the sum of squared negative parts of the sorted
differences equals `∑ (α_i - β_i) |α_i - β_i|`. -/
theorem c_sub_d_num {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2 - ∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2
      = ∑ i, (α i - β i) * |α i - β i| := by
  obtain ⟨π, ha, hb⟩ := (similarlyOrdered_iff_common_sort α β).mp h
  have ea := sortsDesc_unique α hσ ha
  have eb := sortsDesc_unique β hτ hb
  have e : ∀ k, α (σ k) = α (π k) ∧ β (τ k) = β (π k) :=
    fun k => ⟨congrFun ea k, congrFun eb k⟩
  simp_rw [(e _).1, (e _).2]
  rw [← Finset.sum_sub_distrib, ← Equiv.sum_comp π (fun i => (α i - β i) * |α i - β i|)]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hi1 : β (π i) ≤ α (π i)
  · rw [max_eq_left (sub_nonneg.mpr hi1), max_eq_right (sub_nonpos.mpr hi1),
      abs_of_nonneg (sub_nonneg.mpr hi1)]
    ring
  · have hi2 := le_of_not_ge hi1
    rw [max_eq_right (sub_nonpos.mpr hi2), max_eq_left (sub_nonneg.mpr hi2),
      abs_of_nonpos (sub_nonpos.mpr hi2)]
    ring

/-- Theorem A(ii): for similarly ordered lists, `d = 0` iff every `β_i ≤ α_i`
(every tilt `t_i ≥ 0`). -/
theorem d_num_eq_zero_iff {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (β (τ k) - α (σ k)) 0) ^ 2 = 0 ↔ ∀ i, β i ≤ α i := by
  obtain ⟨π, ha, hb⟩ := (similarlyOrdered_iff_common_sort α β).mp h
  have ea := sortsDesc_unique α hσ ha
  have eb := sortsDesc_unique β hτ hb
  have e : ∀ k, α (σ k) = α (π k) ∧ β (τ k) = β (π k) :=
    fun k => ⟨congrFun ea k, congrFun eb k⟩
  simp_rw [(e _).1, (e _).2]
  rw [Equiv.sum_comp π (fun i => (max (β i - α i) 0) ^ 2)]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (max (β i - α i) 0))]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, max_eq_right_iff, sub_nonpos]

/-- Theorem A(ii): for similarly ordered lists, `c = 0` iff every `α_i ≤ β_i`
(every tilt `t_i ≤ 0`). -/
theorem c_num_eq_zero_iff {n : ℕ} (α β : Fin n → ℝ) (h : SimilarlyOrdered α β)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc α σ) (hτ : SortsDesc β τ) :
    ∑ k, (max (α (σ k) - β (τ k)) 0) ^ 2 = 0 ↔ ∀ i, α i ≤ β i := by
  have hs : SimilarlyOrdered β α := by
    intro i j
    simpa only [mul_comm] using h i j
  exact d_num_eq_zero_iff β α hs hτ hσ

end Odesky
