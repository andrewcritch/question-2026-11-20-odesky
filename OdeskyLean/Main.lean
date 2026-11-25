import OdeskyLean.Profile
import OdeskyLean.Spectral

/-!
# Theorem A for the operator itself

Let `L` be an orthogonal sum of rank-one forms on `ℝᴺ`, with `2n ≤ N`, `n ≥ 1`,
and every tilt `|t_i| < 1`. Its spectral lists are given here as any decreasing
lists with the right multisets of values:

* `lp` (`λ₊`): the positive eigenvalues of `S`, with multiplicity;
* `lm` (`λ₋`): the absolute values of the negative eigenvalues of `S`;
* `sv` (`σ(T)`): the singular values of `T`, each pair counted once, i.e., the
  positive eigenvalues of `TᵀT = -T²`, with multiplicity, are the `sv_k²`, each
  twice.

The profile uses Frobenius norms computed in an orthonormal basis `b`.
-/

open Finset Polynomial

namespace Odesky

namespace OrthoBlocks

variable {n N : ℕ} (B : OrthoBlocks n N)

/-- The hypotheses that make `lp`, `lm`, `sv` the spectral lists of `L`. -/
structure SpectralLists (lp lm sv : Fin n → ℝ) : Prop where
  lp_anti : Antitone lp
  lm_anti : Antitone lm
  sv_anti : Antitone sv
  sv_nonneg : ∀ k, 0 ≤ sv k
  lp_roots : Multiset.map lp univ.val = B.Slin.charpoly.roots.filter (fun x => 0 < x)
  lm_roots : Multiset.map (fun k => -lm k) univ.val =
    B.Slin.charpoly.roots.filter (fun x => x < 0)
  sv_roots : 2 • Multiset.map (fun k => sv k ^ 2) univ.val =
    (-(B.Tlin ∘ₗ B.Tlin)).charpoly.roots.filter (fun x => 0 < x)

private lemma map_perm (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Multiset.map (f ∘ σ) univ.val = Multiset.map f univ.val := by
  simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using
    (Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm f))

private lemma lists_sorted (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc B.α σ) (hτ : SortsDesc B.β τ) :
    lp = B.α ∘ σ ∧ lm = B.β ∘ τ := by
  refine ⟨sorted_eq_of_multiset _ _ h.lp_anti
    (h.lp_roots.trans (B.roots_S_pos hT hN)) hσ, ?_⟩
  apply sorted_eq_of_multiset _ _ h.lm_anti _ hτ
  have hm := congrArg (Multiset.map (fun x : ℝ => -x))
    (h.lm_roots.trans (B.roots_S_neg hT hN))
  simpa only [Multiset.map_map, Function.comp_def, neg_neg] using hm

private lemma sv_sorted (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    {ρ : Equiv.Perm (Fin n)}
    (hρ : SortsDesc (fun i => Real.sqrt (B.α i * B.β i)) ρ) :
    sv = (fun i => Real.sqrt (B.α i * B.β i)) ∘ ρ := by
  apply sorted_eq_of_multiset _ _ h.sv_anti _ hρ
  have hm : Multiset.map (fun k => sv k ^ 2) univ.val =
      Multiset.map (fun i => B.α i * B.β i) univ.val := by
    have hh := h.sv_roots.trans (B.roots_neg_T_sq_pos hT hN)
    exact (nsmul_right_injective (by norm_num : (2 : ℕ) ≠ 0)) hh
  have hh := congrArg (Multiset.map Real.sqrt) hm
  simpa only [Multiset.map_map, Function.comp_def, Real.sqrt_sq (h.sv_nonneg _)] using hh

/-- The hypotheses `SpectralLists` are not vacuous: the spectral lists exist. -/
theorem spectralLists_exists (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    ∃ lp lm sv, B.SpectralLists lp lm sv := by
  classical
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨ρ, hρ⟩ := exists_sortsDesc (fun i => Real.sqrt (B.α i * B.β i))
  refine ⟨B.α ∘ σ, B.β ∘ τ, (fun i => Real.sqrt (B.α i * B.β i)) ∘ ρ,
    hσ, hτ, hρ, (fun _ => Real.sqrt_nonneg _), ?_, ?_, ?_⟩
  · rw [map_perm, B.roots_S_pos hT hN]
  · change Multiset.map ((fun i => -B.β i) ∘ τ) _ = _
    rw [map_perm, B.roots_S_neg hT hN]
  · simp only [Function.comp_apply, Real.sq_sqrt
      (le_of_lt (mul_pos (B.α_pos hT _) (B.β_pos hT _)))]
    change 2 • Multiset.map ((fun i => B.α i * B.β i) ∘ ρ) _ = _
    rw [map_perm, B.roots_neg_T_sq_pos hT hN]

variable (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))

/-- `‖L‖²`. -/
noncomputable def nL : ℝ := ∑ k, ‖B.L (b k)‖ ^ 2

/-- `a = ‖T‖² / ‖L‖²`. -/
noncomputable def pa : ℝ := (∑ k, ‖B.T (b k)‖ ^ 2) / B.nL b

/-- `b = 2 ⟨λ₊, λ₋⟩ / ‖L‖²`. -/
noncomputable def pb (lp lm : Fin n → ℝ) : ℝ := 2 * (∑ k, lp k * lm k) / B.nL b

/-- `c = ‖(λ₊ - λ₋)₊‖² / ‖L‖²`. -/
noncomputable def pc (lp lm : Fin n → ℝ) : ℝ := (∑ k, (max (lp k - lm k) 0) ^ 2) / B.nL b

/-- `d = ‖(λ₊ - λ₋)₋‖² / ‖L‖²`. -/
noncomputable def pd (lp lm : Fin n → ℝ) : ℝ := (∑ k, (max (lm k - lp k) 0) ^ 2) / B.nL b

private lemma nL_eq : B.nL b = normSq B.α B.β := by
  rw [nL, B.frob_L]
  simp only [normSq, B.α_add_β]

private lemma pa_eq : B.pa b = profA B.α B.β := by
  rw [pa, B.frob_T, B.nL_eq b]
  rfl

/-- Theorem A, inequality: `a ≤ b`. -/
theorem main_a_le_b [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv) :
    B.pa b ≤ B.pb b lp lm := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨rfl, rfl⟩ := B.lists_sorted hT hN h hσ hτ
  simpa only [B.pa_eq b, pb, B.nL_eq b, profB, Function.comp_apply] using
    profA_le_profB B.α B.β (B.α_pos hT) (B.β_pos hT) hσ hτ

/-- Theorem A, relation (1): if `(α, β)` is similarly ordered, then
`σ(T)_k = √(λ₊,k λ₋,k)` for every `k`. -/
theorem main_relation_one [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    ∀ k, sv k = Real.sqrt (lp k * lm k) := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨ρ, hρ⟩ := exists_sortsDesc (fun i => Real.sqrt (B.α i * B.β i))
  obtain ⟨rfl, rfl⟩ := B.lists_sorted hT hN h hσ hτ
  rw [B.sv_sorted hT hN h hρ]
  exact relation_one B.α B.β (fun i => (B.α_pos hT i).le)
    (fun i => (B.β_pos hT i).le) hso hσ hτ hρ

/-- Theorem A, `c - d`: if `(α, β)` is similarly ordered, then
`c - d = ∑ w_i t_i |t_i|` with `w_i = s_i² / ‖L‖²`. -/
theorem main_c_sub_d [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pc b lp lm - B.pd b lp lm = ∑ i, (B.s i ^ 2 / B.nL b) * B.t i * |B.t i| := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨rfl, rfl⟩ := B.lists_sorted hT hN h hσ hτ
  simp only [pc, pd, B.nL_eq b, Function.comp_apply]
  change profC B.α B.β σ τ - profD B.α B.β σ τ = _
  rw [profC_sub_profD B.α B.β (B.α_pos hT) (B.β_pos hT) hso hσ hτ]
  apply sum_congr rfl
  intro i _
  rw [B.α_add_β, B.α_sub_β, mul_div_cancel_left₀ _ (ne_of_gt (B.s_pos i))]

/-- **Theorem A.** The profile of `L` lies on `Θ = {a = b, c d = 0}` if and only
if `(α, β)` is similarly ordered and the tilts are all `≥ 0` or all `≤ 0`. -/
theorem main_mem_Theta_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv) :
    (B.pa b = B.pb b lp lm ∧ B.pc b lp lm * B.pd b lp lm = 0) ↔
      (SimilarlyOrdered B.α B.β ∧ ((∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0))) := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨rfl, rfl⟩ := B.lists_sorted hT hN h hσ hτ
  simp only [B.pa_eq b, pb, pc, pd, B.nL_eq b, Function.comp_apply]
  change (profA B.α B.β = profB B.α B.β σ τ ∧
    profC B.α B.β σ τ * profD B.α B.β σ τ = 0) ↔ _
  rw [mem_Theta_iff B.α B.β (B.α_pos hT) (B.β_pos hT) hσ hτ]
  have hp (i) : B.β i ≤ B.α i ↔ 0 ≤ B.t i := by
    rw [← sub_nonneg, B.α_sub_β, mul_nonneg_iff_of_pos_left (B.s_pos i)]
  have hn (i) : B.α i ≤ B.β i ↔ B.t i ≤ 0 := by
    rw [← sub_nonpos, B.α_sub_β]
    constructor
    · intro hi
      nlinarith [B.s_pos i]
    · exact mul_nonpos_of_nonneg_of_nonpos (B.s_pos i).le
  simp only [hp, hn]

end OrthoBlocks

end Odesky
