import OdeskyLean.GenProfile

/-!
# The log-determinant identity of §1

Rows `q_i, k_i ∈ ℝᴺ` (`L x = ∑ ⟪q_i, x⟫ k_i`, i.e., `L = Kᵀ Q`), with the `2n` rows
linearly independent and `2n ≤ N`. Let `G` be their `2n × 2n` Gram matrix.

* `lists_pos`: every `λ₊,j`, `λ₋,j` and `σ(T)_j` is positive.
* `prod_lam_eq_det`: `∏ λ₊,j λ₋,j = det G / 4ⁿ`.
* `prod_sig_eq_det`: `∏ σ(T)_j² = det G / 4ⁿ`.
* `logdet_identity`: hence `∑ log σ(T)_j = ½ ∑ log(λ₊,j λ₋,j)`.

Proof idea: `2S = Fᵀ J F` and `2T = Fᵀ Ω F` with `F` the stacked rows,
`J = [[0, I], [I, 0]]`, `Ω = [[0, -I], [I, 0]]`; the nonzero spectra of `2S` and `2T`
are those of `J G` and `Ω G` (`Matrix.charpoly_mul_comm_of_le`-type facts), and
`|det J| = det Ω = 1`.
-/

open RealInnerProductSpace Finset

namespace Odesky

variable {n N : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The rows of `Q` followed by the rows of `K`. -/
def stackRows (q k : Fin n → V) : Fin n ⊕ Fin n → V := Sum.elim q k

/-- Gram matrix of the stacked rows. -/
noncomputable def gramRows (q k : Fin n → V) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => ⟪stackRows q k a, stackRows q k b⟫

theorem lists_pos (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) (j : Fin n) :
    0 < lamP q k j ∧ 0 < lamM q k j ∧ 0 < sigT q k j := by
  sorry

theorem prod_lam_eq_det (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∏ j, (lamP q k j * lamM q k j) = (gramRows q k).det / 4 ^ n := by
  sorry

theorem prod_sig_eq_det (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∏ j, sigT q k j ^ 2 = (gramRows q k).det / 4 ^ n := by
  sorry

theorem logdet_identity (hN : 2 * n ≤ N) (q k : Fin n → V)
    (hli : LinearIndependent ℝ (stackRows q k)) :
    ∑ j, Real.log (sigT q k j) = (1 / 2) * ∑ j, Real.log (lamP q k j * lamM q k j) := by
  sorry

end Odesky
