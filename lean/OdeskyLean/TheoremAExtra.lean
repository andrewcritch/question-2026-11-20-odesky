import OdeskyLean.Main

/-!
# Theorem 1, remaining items, for the operator

* `main_d_eq_zero_iff`, `main_c_eq_zero_iff`: Theorem 1(3), second part, as a
  statement about the operator `L`: if the blocks are similarly ordered, then
  `d = 0` iff every tilt is `≥ 0`, and `c = 0` iff every tilt is `≤ 0`.
* `theta_attained`: Theorem 1(5): every point `(a, a, c, d)` of `Θ` with `a > 0`
  (i.e., every point of `Θ` other than `(0,0,1,0)` and `(0,0,0,1)`) is the profile
  of a form in normal form, here with one block in `ℝ²`.
-/

open Finset RealInnerProductSpace

namespace Odesky

namespace OrthoBlocks

variable {n N : ℕ} (B : OrthoBlocks n N)
variable (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))

private lemma lists_sorted' (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc B.α σ) (hτ : SortsDesc B.β τ) :
    lp = B.α ∘ σ ∧ lm = B.β ∘ τ := by
  refine ⟨sorted_eq_of_multiset _ _ h.lp_anti
    (h.lp_roots.trans (B.roots_S_pos hT hN)) hσ, ?_⟩
  apply sorted_eq_of_multiset _ _ h.lm_anti _ hτ
  have hm := congrArg (Multiset.map (fun x : ℝ => -x))
    (h.lm_roots.trans (B.roots_S_neg hT hN))
  simpa only [Multiset.map_map, Function.comp_def, neg_neg] using hm

private lemma nL_eq' : B.nL b = normSq B.α B.β := by
  rw [nL, B.frob_L]
  simp only [normSq, B.α_add_β]

private lemma nL_pos [NeZero n] : 0 < B.nL b := by
  rw [nL, B.frob_L]
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (B.s_pos i)) Finset.univ_nonempty

/-- Theorem 1(3): `d = 0` iff every tilt is `≥ 0`. -/
theorem main_d_eq_zero_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pd b lp lm = 0 ↔ ∀ i, 0 ≤ B.t i := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨rfl, rfl⟩ := B.lists_sorted' hT hN h hσ hτ
  have hn := ne_of_gt (B.nL_pos b)
  have hp (i) : B.β i ≤ B.α i ↔ 0 ≤ B.t i := by
    rw [← sub_nonneg, B.α_sub_β, mul_nonneg_iff_of_pos_left (B.s_pos i)]
  rw [pd, div_eq_zero_iff, or_iff_left hn]
  simp only [Function.comp_apply]
  rw [d_num_eq_zero_iff B.α B.β hso hσ hτ]
  simp only [hp]

/-- Theorem 1(3): `c = 0` iff every tilt is `≤ 0`. -/
theorem main_c_eq_zero_iff [NeZero n] (hT : ∀ i, |B.t i| < 1) (hN : 2 * n ≤ N)
    {lp lm sv : Fin n → ℝ} (h : B.SpectralLists lp lm sv)
    (hso : SimilarlyOrdered B.α B.β) :
    B.pc b lp lm = 0 ↔ ∀ i, B.t i ≤ 0 := by
  obtain ⟨σ, hσ⟩ := exists_sortsDesc B.α
  obtain ⟨τ, hτ⟩ := exists_sortsDesc B.β
  obtain ⟨rfl, rfl⟩ := B.lists_sorted' hT hN h hσ hτ
  have hn := ne_of_gt (B.nL_pos b)
  have hn' (i) : B.α i ≤ B.β i ↔ B.t i ≤ 0 := by
    rw [← sub_nonpos, B.α_sub_β]
    constructor
    · intro hi
      nlinarith [B.s_pos i]
    · exact mul_nonpos_of_nonneg_of_nonpos (B.s_pos i).le
  rw [pc, div_eq_zero_iff, or_iff_left hn]
  simp only [Function.comp_apply]
  rw [c_num_eq_zero_iff B.α B.β hso hσ hτ]
  simp only [hn']

end OrthoBlocks

/-- Theorem 1(5): every point of `Θ` other than its two endpoints is the profile
of a form in normal form. The point is `(a, a, c, d)` with `a > 0`,
`c, d ≥ 0`, `c d = 0` and `2a + c + d = 1`. -/
theorem theta_attained (a c d : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c * d = 0) (hsum : 2 * a + c + d = 1) :
    ∃ B : OrthoBlocks 1 2, (∀ i, |B.t i| < 1) ∧
      SimilarlyOrdered B.α B.β ∧ ((∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0)) ∧
      ∃ lp lm sv : Fin 1 → ℝ, B.SpectralLists lp lm sv ∧
        ∀ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
          B.pa b = a ∧ B.pb b lp lm = a ∧ B.pc b lp lm = c ∧ B.pd b lp lm = d := by
  set t : ℝ := Real.sqrt c - Real.sqrt d with ht_def
  have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have hds : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  have hsd : Real.sqrt c * Real.sqrt d = 0 := by
    rw [← Real.sqrt_mul hc, hcd, Real.sqrt_zero]
  have ht2 : t ^ 2 = c + d := by
    rw [ht_def, sub_sq, hcs, hds, mul_assoc, hsd]; ring
  have ht1 : t ^ 2 < 1 := by rw [ht2]; linarith
  have hr : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  let u : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
  let v : EuclideanSpace ℝ (Fin 2) := !₂[t, Real.sqrt (1 - t ^ 2)]
  have hu : ‖u‖ = 1 := by
    simp [u, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [v, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp [hr]
  have huv : ⟪u, v⟫ = t := by
    simp [u, v, PiLp.inner_apply, Fin.sum_univ_two]
  let B : OrthoBlocks 1 2 :=
    { s := fun _ => 1
      u := fun _ => u
      v := fun _ => v
      s_pos := fun _ => one_pos
      u_unit := fun _ => hu
      v_unit := fun _ => hv
      uu := fun i j h => absurd (Subsingleton.elim i j) h
      uv := fun i j h => absurd (Subsingleton.elim i j) h
      vv := fun i j h => absurd (Subsingleton.elim i j) h }
  have hBt (i) : B.t i = t := huv
  have hT : ∀ i, |B.t i| < 1 := by
    intro i
    rw [hBt, abs_lt]
    constructor <;> nlinarith
  have hα (i) : B.α i = (1 + t) / 2 := by simp [OrthoBlocks.α, hBt, B]
  have hβ (i) : B.β i = (1 - t) / 2 := by simp [OrthoBlocks.β, hBt, B]
  have hso : SimilarlyOrdered B.α B.β := by
    intro i j
    rw [Subsingleton.elim i j]; simp
  have hsign : (∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0) := by
    rcases le_total 0 t with h0 | h0
    · exact Or.inl fun i => by rw [hBt]; exact h0
    · exact Or.inr fun i => by rw [hBt]; exact h0
  have hsl : B.SpectralLists B.α B.β (fun i => Real.sqrt (B.α i * B.β i)) := by
    refine ⟨Subsingleton.antitone _, Subsingleton.antitone _, Subsingleton.antitone _,
      fun _ => Real.sqrt_nonneg _, ?_, ?_, ?_⟩
    · rw [B.roots_S_pos hT le_rfl]
    · rw [B.roots_S_neg hT le_rfl]
    · simp only [Real.sq_sqrt (le_of_lt (mul_pos (B.α_pos hT _) (B.β_pos hT _)))]
      rw [B.roots_neg_T_sq_pos hT le_rfl]
  refine ⟨B, hT, hso, hsign, B.α, B.β, _, hsl, fun b => ?_⟩
  have hnL : B.nL b = 1 := by
    rw [OrthoBlocks.nL, B.frob_L]; simp [B]
  have hpa : B.pa b = 2 * (B.α 0 * B.β 0) := by
    rw [OrthoBlocks.pa, B.frob_T, hnL, div_one, Fin.sum_univ_one]
  have hpb : B.pb b B.α B.β = 2 * (B.α 0 * B.β 0) := by
    rw [OrthoBlocks.pb, hnL, div_one, Fin.sum_univ_one]
  have hab : 2 * (B.α 0 * B.β 0) = a := by
    rw [hα, hβ]; nlinarith
  have hαβ : B.α 0 - B.β 0 = t := by rw [hα, hβ]; ring
  refine ⟨hpa.trans hab, hpb.trans hab, ?_, ?_⟩
  · rw [OrthoBlocks.pc, hnL, div_one, Fin.sum_univ_one, hαβ]
    rcases mul_eq_zero.mp hcd with h0 | h0
    · have : t = -Real.sqrt d := by rw [ht_def, h0, Real.sqrt_zero, zero_sub]
      rw [this, max_eq_right (by simp [Real.sqrt_nonneg]), h0]; ring
    · have : t = Real.sqrt c := by rw [ht_def, h0, Real.sqrt_zero, sub_zero]
      rw [this, max_eq_left (Real.sqrt_nonneg _), hcs]
  · rw [OrthoBlocks.pd, hnL, div_one, Fin.sum_univ_one,
      show B.β 0 - B.α 0 = -t by rw [← hαβ]; ring]
    rcases mul_eq_zero.mp hcd with h0 | h0
    · have : t = -Real.sqrt d := by rw [ht_def, h0, Real.sqrt_zero, zero_sub]
      rw [this, neg_neg, max_eq_left (Real.sqrt_nonneg _), hds]
    · have : t = Real.sqrt c := by rw [ht_def, h0, Real.sqrt_zero, sub_zero]
      rw [this, max_eq_right (by simp [Real.sqrt_nonneg]), h0]; ring

end Odesky
