import OdeskyLean.GenProfile
import OdeskyLean.Main
import OdeskyLean.TheoremB
import OdeskyLean.Weyl

/-!
# Layer 11 (gap G2): the general profile at the exact limit configuration

Rows `q_i, k_i ∈ ℝᴺ` with `⟪q_i, q_l⟫ = ⟪k_i, k_l⟫ = δ_il (f_i + g_i)` and
`⟪q_i, k_l⟫ = δ_il (f_i - g_i)` (the limit configuration of Theorem B). With
`2n ≤ N`, the spectral lists of the general profile are the sorted `f`, the sorted
`g`, and (when `(f, g)` is similarly ordered) `√(f g)` of the sorted lists; so the
general profile equals the profile of Theorem A.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

theorem lists_at_limit [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (q k : Fin n → V)
    (hqq : ∀ i l, ⟪q i, q l⟫ = if i = l then fv i + gv i else 0)
    (hkk : ∀ i l, ⟪k i, k l⟫ = if i = l then fv i + gv i else 0)
    (hqk : ∀ i l, ⟪q i, k l⟫ = if i = l then fv i - gv i else 0)
    (hN : 2 * n ≤ N) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    lamP q k = fv ∘ σ ∧ lamM q k = gv ∘ τ ∧ frobL q k = normSq fv gv ∧
      frobT q k = 2 * ∑ i, fv i * gv i ∧
      (SimilarlyOrdered fv gv → ∀ j, sigT q k j = Real.sqrt (fv (σ j) * gv (τ j))) := by
  sorry

theorem gprof_at_limit [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i)
    (hg : ∀ i, 0 < gv i) (q k : Fin n → V)
    (hqq : ∀ i l, ⟪q i, q l⟫ = if i = l then fv i + gv i else 0)
    (hkk : ∀ i l, ⟪k i, k l⟫ = if i = l then fv i + gv i else 0)
    (hqk : ∀ i l, ⟪q i, k l⟫ = if i = l then fv i - gv i else 0)
    (hN : 2 * n ≤ N) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    gA q k = profA fv gv ∧ gB q k = profB fv gv σ τ ∧ gC q k = profC fv gv σ τ ∧
      gD q k = profD fv gv σ τ ∧ (SimilarlyOrdered fv gv → gErr q k = 0) := by
  sorry

end Odesky
