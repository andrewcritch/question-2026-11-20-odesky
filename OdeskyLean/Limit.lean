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

private lemma card_filter_univ {m : ℕ} (f : Fin m → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (univ.filter (fun i => P (f i))).card = Multiset.card ((Multiset.map f univ.val).filter P) := by
  rw [Multiset.filter_map, Multiset.card_map]; rfl

private lemma map_perm' {m : ℕ} (f : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    Multiset.map (f ∘ σ) univ.val = Multiset.map f univ.val := by
  simpa only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn] using
    (Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm f))

/-- For an antitone list, an upward-closed predicate holds exactly on a prefix. -/
private lemma prefix_iff {m : ℕ} (f : Fin m → ℝ) (hf : Antitone f) (P : ℝ → Prop)
    [DecidablePred P] (hP : ∀ a b, a ≤ b → P a → P b) (k : Fin m) :
    P (f k) ↔ k.val < (univ.filter (fun i => P (f i))).card := by
  constructor
  · intro hk
    have hsub : Iic k ⊆ univ.filter (fun i => P (f i)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and]
      exact hP _ _ (hf (mem_Iic.mp hi)) hk
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hk
    by_contra hn
    have hsub : univ.filter (fun i => P (f i)) ⊆ Iio k := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_Iio]
      by_contra hik
      exact hn (hP _ _ (hf (not_lt.mp hik)) hi)
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- Two antitone lists whose upper-level counts differ by the factor `c` agree at
matching indices. -/
private lemma eq_of_counts {m k : ℕ} (v : Fin m → ℝ) (hv : Antitone v) (p : Fin k → ℝ)
    (hp : Antitone p) (hpos : ∀ j, 0 < p j) (c : ℕ) (hc0 : 0 < c)
    (hc : ∀ y : ℝ, 0 < y → Multiset.card ((Multiset.map v univ.val).filter (fun x => y ≤ x)) =
      c * Multiset.card ((Multiset.map p univ.val).filter (fun x => y ≤ x)))
    (j : Fin k) (i : Fin m) (hij : i.val = c * j.val) : v i = p j := by
  have key : ∀ y : ℝ, 0 < y → (y ≤ v i ↔ y ≤ p j) := by
    intro y hy
    have e1 := card_filter_univ v (fun x => y ≤ x)
    have e2 := card_filter_univ p (fun x => y ≤ x)
    rw [prefix_iff v hv (fun x => y ≤ x) (fun a b hab h => h.trans hab) i,
      prefix_iff p hp (fun x => y ≤ x) (fun a b hab h => h.trans hab) j, e1, e2, hc y hy, hij]
    exact Nat.mul_lt_mul_left hc0
  have h1 : p j ≤ v i := (key _ (hpos j)).mpr le_rfl
  have h2 : v i ≤ p j := (key _ (lt_of_lt_of_le (hpos j) h1)).mp le_rfl
  exact le_antisymm h2 h1

/-- Counting the entries `≥ y > 0` through the positive part of a multiset. -/
private lemma count_pos_part (M : Multiset ℝ) {y : ℝ} (hy : 0 < y) :
    M.filter (fun x => y ≤ x) = (M.filter (fun x => 0 < x)).filter (fun x => y ≤ x) := by
  rw [Multiset.filter_filter]
  apply Multiset.filter_congr
  intro x _
  constructor
  · intro h; exact ⟨h, lt_of_lt_of_le hy h⟩
  · intro h; exact h.1

private lemma count_neg_part (M : Multiset ℝ) {y : ℝ} (hy : 0 < y) :
    M.filter (fun x => y ≤ -x) = (M.filter (fun x => x < 0)).filter (fun x => y ≤ -x) := by
  rw [Multiset.filter_filter]
  apply Multiset.filter_congr
  intro x _
  constructor
  · intro h; exact ⟨h, by linarith⟩
  · intro h; exact h.1

theorem lists_at_limit [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i) (hg : ∀ i, 0 < gv i)
    (q k : Fin n → V)
    (hqq : ∀ i l, ⟪q i, q l⟫ = if i = l then fv i + gv i else 0)
    (hkk : ∀ i l, ⟪k i, k l⟫ = if i = l then fv i + gv i else 0)
    (hqk : ∀ i l, ⟪q i, k l⟫ = if i = l then fv i - gv i else 0)
    (hN : 2 * n ≤ N) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    lamP q k = fv ∘ σ ∧ lamM q k = gv ∘ τ ∧ frobL q k = normSq fv gv ∧
      frobT q k = 2 * ∑ i, fv i * gv i ∧
      (SimilarlyOrdered fv gv → ∀ j, sigT q k j = Real.sqrt (fv (σ j) * gv (τ j))) := by
  classical
  obtain ⟨B, hL, hT, hα, hβ⟩ := blocks_of_limit_gram fv gv hf hg q k hqq hkk hqk
  have hαf : B.α = fv := funext hα
  have hβg : B.β = gv := funext hβ
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hLx : ∀ x, formL q k x = B.L x := by
    intro x; rw [hL]; simp [formL, LinearMap.sum_apply]
  have hLtx : ∀ x, formLt q k x = B.Lt x := by
    intro x; apply ext_inner_left ℝ; intro y
    rw [← formLt_adjoint, ← B.inner_L_eq, hLx]
  have hS : formS q k = B.Slin := by
    apply LinearMap.ext; intro x
    rw [B.Slin_apply]; simp [formS, OrthoBlocks.S, hLx, hLtx]
  have hTT : formT q k = B.Tlin := by
    apply LinearMap.ext; intro x
    rw [B.Tlin_apply]; simp [formT, OrthoBlocks.T, hLx, hLtx]
  have hSroots : Multiset.map (eigS q k) univ.val = B.Slin.charpoly.roots := by
    rw [← hS]
    exact (roots_charpoly_eq_eigenvalues finrank_euclideanSpace_fin
      (formS_isSymmetric q k)).symm
  have hT2roots : Multiset.map (eigT2 q k) univ.val =
      (-(B.Tlin ∘ₗ B.Tlin)).charpoly.roots := by
    rw [← hTT]
    exact (roots_charpoly_eq_eigenvalues finrank_euclideanSpace_fin
      (negTsq_isSymmetric q k)).symm
  have hpos := B.roots_S_pos hT hN
  have hneg := B.roots_S_neg hT hN
  have htpos := B.roots_neg_T_sq_pos hT hN
  rw [hαf] at hpos
  rw [hβg] at hneg
  rw [hαf, hβg] at htpos
  have hvA : Antitone (eigS q k) :=
    (formS_isSymmetric q k).eigenvalues_antitone finrank_euclideanSpace_fin
  have hvT : Antitone (eigT2 q k) :=
    (negTsq_isSymmetric q k).eigenvalues_antitone finrank_euclideanSpace_fin
  -- the positive eigenvalues of `S`
  have hP : ∀ (j : Fin n) (h : (j : ℕ) < N), eigS q k ⟨j, h⟩ = fv (σ j) := by
    intro j h
    refine eq_of_counts (eigS q k) hvA (fv ∘ σ) hσ (fun j => hf _) 1 one_pos ?_ j ⟨j, h⟩
      (by simp)
    intro y hy
    rw [count_pos_part _ hy, hSroots, hpos, map_perm', one_mul]
  -- the negative eigenvalues of `S`
  let w : Fin N → ℝ := fun i => -eigS q k (Fin.revPerm i)
  have hw : Antitone w := by
    intro a b hab
    simp only [w, Fin.revPerm_apply, neg_le_neg_iff]
    exact hvA (Fin.rev_le_rev.mpr hab)
  have hwmap : Multiset.map w univ.val =
      Multiset.map (fun x => -x) (Multiset.map (eigS q k) univ.val) := by
    have : w = (fun x => -x) ∘ (eigS q k ∘ Fin.revPerm) := rfl
    rw [this, ← Multiset.map_map, map_perm']
  have hM : ∀ (j : Fin n) (h : (j : ℕ) < N), w ⟨j, h⟩ = gv (τ j) := by
    intro j h
    refine eq_of_counts w hw (gv ∘ τ) hτ (fun j => hg _) 1 one_pos ?_ j ⟨j, h⟩ (by simp)
    intro y hy
    rw [hwmap, Multiset.filter_map, Multiset.card_map, map_perm', one_mul]
    change Multiset.card ((Multiset.map (eigS q k) univ.val).filter (fun x => y ≤ -x)) = _
    rw [count_neg_part _ hy, hSroots, hneg, Multiset.filter_map, Multiset.filter_map,
      Multiset.card_map, Multiset.card_map]
    congr 1
    apply Multiset.filter_congr
    intro x _
    simp
  have hnN : n ≤ N := by omega
  have hkq : ∀ i l, ⟪k i, q l⟫ = if l = i then fv l - gv l else 0 := by
    intro i l; rw [real_inner_comm]; exact hqk l i
  have hfrobL : frobL q k = normSq fv gv := by
    simp only [frobL, hkk, hqq, normSq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [sq]
    · intro j _ hji; simp [Ne.symm hji]
    · simp
  refine ⟨?_, ?_, hfrobL, ?_, ?_⟩
  · funext j
    have h : (j : ℕ) < N := by omega
    simp only [lamP, eigAt, dif_pos h, hP j h, Function.comp_apply]
    exact max_eq_left (hf _).le
  · funext j
    have h : N - 1 - (j : ℕ) < N := by omega
    have hj : (j : ℕ) < N := by omega
    have he : eigS q k ⟨N - 1 - (j : ℕ), h⟩ = -w ⟨j, hj⟩ := by
      simp only [w, neg_neg, Fin.revPerm_apply]
      congr 1
      ext
      simp only [Fin.val_rev]
      omega
    simp only [lamM, eigAt, dif_pos h, he, neg_neg, hM j hj, Function.comp_apply]
    exact max_eq_left (hg _).le
  · rw [frobT, hfrobL]
    simp only [hkq, hqk, normSq]
    have hs : ∀ i, (∑ j, (if j = i then fv j - gv j else 0) *
        (if i = j then fv i - gv i else 0)) = (fv i - gv i) ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · simp [sq]
      · intro j _ hji; simp [hji]
      · simp
    simp only [hs, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro hso j
    obtain ⟨π, hπa, hπb⟩ := (similarlyOrdered_iff_common_sort fv gv).mp hso
    let p : Fin n → ℝ := fun i => fv (π i) * gv (π i)
    have hp : Antitone p := by
      intro a b hab
      exact mul_le_mul (hπa hab) (hπb hab) (hg _).le (hf _).le
    have h2 : 2 * (j : ℕ) < N := by omega
    have hval : eigT2 q k ⟨2 * j, h2⟩ = p j := by
      refine eq_of_counts (eigT2 q k) hvT p hp (fun i => mul_pos (hf _) (hg _)) 2
        two_pos ?_ j ⟨2 * j, h2⟩ rfl
      intro y hy
      have : p = (fun i => fv i * gv i) ∘ π := rfl
      rw [count_pos_part _ hy, hT2roots, htpos, Multiset.filter_nsmul, Multiset.card_nsmul,
        this, map_perm']
    have ea := congrFun (sortsDesc_unique fv hπa hσ) j
    have eb := congrFun (sortsDesc_unique gv hπb hτ) j
    simp only [Function.comp_apply] at ea eb
    simp only [sigT, eigAt, dif_pos h2, hval, p, ea, eb]
    rw [max_eq_left (mul_pos (hf _) (hg _)).le]

theorem gprof_at_limit [NeZero n] (fv gv : Fin n → ℝ) (hf : ∀ i, 0 < fv i)
    (hg : ∀ i, 0 < gv i) (q k : Fin n → V)
    (hqq : ∀ i l, ⟪q i, q l⟫ = if i = l then fv i + gv i else 0)
    (hkk : ∀ i l, ⟪k i, k l⟫ = if i = l then fv i + gv i else 0)
    (hqk : ∀ i l, ⟪q i, k l⟫ = if i = l then fv i - gv i else 0)
    (hN : 2 * n ≤ N) {σ τ : Equiv.Perm (Fin n)} (hσ : SortsDesc fv σ) (hτ : SortsDesc gv τ) :
    gA q k = profA fv gv ∧ gB q k = profB fv gv σ τ ∧ gC q k = profC fv gv σ τ ∧
      gD q k = profD fv gv σ τ ∧ (SimilarlyOrdered fv gv → gErr q k = 0) := by
  obtain ⟨hP, hM, hL, hT, hrel⟩ := lists_at_limit fv gv hf hg q k hqq hkk hqk hN hσ hτ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gA, hL, hT]; rfl
  · rw [gB, hP, hM, hL]; rfl
  · rw [gC, hP, hM, hL]; rfl
  · rw [gD, hP, hM, hL]; rfl
  · intro hso
    have h0 : ∑ j, (sigT q k j - Real.sqrt (lamP q k j * lamM q k j)) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hrel hso j, hP, hM]
      simp
    rw [gErr, h0, Real.sqrt_zero, zero_div]

end Odesky
