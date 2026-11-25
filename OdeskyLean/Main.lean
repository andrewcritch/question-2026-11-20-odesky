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

/-- The hypotheses `SpectralLists` are not vacuous: the spectral lists exist. -/
theorem spectralLists_exists (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N) :
    ∃ lp lm sv, B.SpectralLists lp lm sv := by
  sorry

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

/-- Theorem A, inequality: `a ≤ b`. -/
theorem main_a_le_b [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv) :
    B.pa b ≤ B.pb b lp lm := by
  sorry

/-- Theorem A, relation (1): if `(α, β)` is similarly ordered, then
`σ(T)_k = √(λ₊,k λ₋,k)` for every `k`. -/
theorem main_relation_one [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    ∀ k, sv k = Real.sqrt (lp k * lm k) := by
  sorry

/-- Theorem A, `c - d`: if `(α, β)` is similarly ordered, then
`c - d = ∑ w_i t_i |t_i|` with `w_i = s_i² / ‖L‖²`. -/
theorem main_c_sub_d [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pc b lp lm - B.pd b lp lm = ∑ i, (B.s i ^ 2 / B.nL b) * B.t i * |B.t i| := by
  sorry

/-- **Theorem A.** The profile of `L` lies on `Θ = {a = b, c d = 0}` if and only
if `(α, β)` is similarly ordered and the tilts are all `≥ 0` or all `≤ 0`. -/
theorem main_mem_Theta_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv) :
    (B.pa b = B.pb b lp lm ∧ B.pc b lp lm * B.pd b lp lm = 0) ↔
      (SimilarlyOrdered B.α B.β ∧ ((∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0))) := by
  sorry

end OrthoBlocks

end Odesky
