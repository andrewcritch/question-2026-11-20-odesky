INTERRUPTED PARTIAL

**Verdict:** Every mathematical claim in §1, §2, §3, and §7 is mathematically sound and no Lean definition has a junk-value or indexing bug, **but** two claims in §3 have unformalized probabilistic/scaling steps (`the claim is unchecked as stated`), several theorems carry explicit Lean hypotheses (`2 * n ≤ N`, `|t_i| < 1`, `Measurable f, g`, `1 ≤ κ`) or small unglued links that are mathematically redundant/harmless (`a harmless difference`), and `#print axioms` / `lake build` could not be machine-run before timeout.

---

## Status at Interruption

- **What was established before timeout:** `question.md`, `answer_draft.md`, `OdeskyLean.lean`, `lakefile.toml`, `lean-toolchain`, and **all 23 `.lean` files** in `lean/OdeskyLean/` were read in full. By direct source inspection, zero `sorry`, `admit`, `axiom`, or `opaque` declarations appear anywhere in `OdeskyLean`. All core definitions, quantifiers, and theorem statements in §1, §2, §3, §6, and §7 were compared against the Lean source.
- **What we were in the middle of:** Running a read-only `lake env lean --stdin` command to verify `#print axioms` on the headline theorems (§6, line 77); `lake` was not on the default `zsh` `PATH` (`command not found: lake`), and the 30-minute timer expired immediately after that turn.
- **What we would do next:** Locate `lake` (e.g., `/Users/andrew/.elan/bin/lake`) to machine-verify `#print axioms` on every theorem in the §6 table, confirm `lake build` against the current `.olean` cache, and do a second pass for any subtler cross-file type coercions.

---

## 1. Core Definitions Audit (`question.md` & `answer_draft.md` vs. Lean)

- **Bilinear form and symmetric/antisymmetric parts (`GenProfile.lean`, `Geometry.lean`):**
  - `formL q k x = ∑ i, ⟪q i, x⟫ • k i` (`GenProfile.lean:28`) matches $L = K^\top Q$ when $q_i, k_i \in \mathbb{R}^N$ are the rows of $Q, K \in \mathbb{R}^{n \times N}$.
  - `OrthoBlocks.L x = ∑ i, (B.s i * ⟪B.v i, x⟫) • B.u i` (`Geometry.lean:55`) and `formL (fun i => σ i • v i) u` (`Bridge.lean:141`, `Identities.lean:229`) both match $\sum_i \sigma_i u_i v_i^\top = U\Sigma V^\top$.
  - `formS`, `formT` and `OrthoBlocks.S`, `OrthoBlocks.T` match $S = (L+L^\top)/2$ and $T = (L-L^\top)/2$.
- **Spectral lists $\lambda_+$, $\lambda_-$, $\sigma(T)$ (`GenProfile.lean`, `Main.lean`, `LogDet.lean`):**
  - Lean uses two representations (accurately noted in §6, line 77):
    1. In `GenProfile.lean:95-112`, `lamP`, `lamM`, `sigT` extract the top $n$ positive eigenvalues of $S$, top $n$ negated bottom eigenvalues of $S$, and square roots of even-indexed eigenvalues `2 * j` of $-T^2 = T^\top T$ from Mathlib's decreasing `IsSymmetric.eigenvalues`, clamped with `max · 0` and `eigAt` (`0` out of range). Note: if $1 \le N < n$, natural subtraction in `N - 1 - (j : ℕ)` (`GenProfile.lean:108`) saturates at `0` rather than going out of range, so the docstring at `GenProfile.lean:14` is slightly loose for $N < n$; however, every theorem where `lamM` matters either has $n \le N$ (from `Orthonormal ℝ u`) or $2n \le N$, where `eigS_pos_part`, `eigS_neg_part` (`Identities.lean:104-129`), `pair_eq`, and `lists_pos` (`LogDet.lean:214, 563`) prove exact agreement with `question.md`'s spectral lists (zero-padded when degenerate, and strictly positive when $\operatorname{rank} F = 2n$).
    2. In `Main.lean:29-38`, `OrthoBlocks.SpectralLists lp lm sv` characterizes the three decreasing lists via filtered root multisets of `charpoly` of `S` and `-T²`. `B.spectralLists_exists` (`Main.lean:70`) proves non-vacuity under `|t_i| < 1` and `2n ≤ N`; `Weyl.roots_charpoly_eq_eigenvalues` (`Weyl.lean:134`) and `Limit.lists_at_limit` / `gprof_at_limit` (`Limit.lean:95, 228`) bridge this to `GenProfile`.
- **Frobenius norms, profile $(a,b,c,d)$, $\Theta$, tilts, similar ordering, normal form:**
  - `frobL_eq`, `frobT_eq` (`GenProfile.lean:120-126`) verify `frobL` and `frobT` against $\sum_t \|A(b_t)\|^2$ in any orthonormal basis $b$, matching `OrthoBlocks.nL` and `pa`.
  - `gA, gB, gC, gD` (`GenProfile.lean:145-153`), `pa, pb, pc, pd` (`Main.lean:92-101`), and `profA, profB, profC, profD` (`Profile.lean:22-34`) match `question.md` line 45; `gErr` (`GenProfile.lean:156`) matches §4 line 54.
  - `SimilarlyOrdered` (`Rearrangement.lean:17`) matches $(\alpha_i - \alpha_j)(\beta_i - \beta_j) \ge 0$ for all $i, j$.
  - Lean does not define standalone names `Theta` or `IsNormalForm`, unfolding them inline as `a = b ∧ c * d = 0` and `SimilarlyOrdered α β ∧ ((∀ i, 0 ≤ t i) ∨ (∀ i, t i ≤ 0))`, which match `question.md` line 46 (given $a,b,c,d \ge 0$ summing to $1$) and §2 line 22.

**Claim checked hardest:** **Theorem 2 and the operator-to-limit bridge** (`theoremB_ae` in `TheoremBFull.lean`, together with `GenProfile.lean`, `Orthonormalize.lean`, `Perturb.lean`, `Weyl.lean`, `Limit.lean`, and `TheoremBExtra.lean`) — verifying that `lamP`, `lamM`, `sigT` (especially even-index sampling `2 * j` of `-T²` and `ℕ`-subtraction `N - 1 - j` as $N \to \infty$), the Gram-matrix perturbation to a nearby orthonormal family (`exists_orthonormal_near`), Weyl bounds (`eig_perturb`), and `lists_at_limit` / `gprof_at_limit` align with no hidden hypothesis or junk-value division/logarithm/square-root loophole.

---

## 2. Findings Where Lean Differs or Leaves Steps Unformalized

### Finding 1 — Unformalized scaling, entry-to-matrix law, and variance-matching steps in §3 special cases
- **Claim:** §3, lines 49–50: *"For $f=(1+r)/2$ and $g=(1-r)/2$, this is the law of the corresponding entry of $(2\sqrt f\,P,\;2\sqrt g\,M)$, i.e., of $\sqrt N\,(Q+K,\;K-Q)$ in the ensemble."* and *"for $r=0$, the question's model has $Q$ and $K$ with independent standard Gaussian entries, and the previous item matches it with $f=g=\tfrac12$. This case is the Gaussian baseline. By Theorem 2, its limit profile is the midpoint $(\tfrac12,\tfrac12,0,0)$ of $\Theta$."*
- **Lean theorems:** `SpecialCases.lean`: `correlated_gaussian_law`, `const_profile` (and `TheoremBFull.lean`: `theoremB_ae`).
- **What differs:**
  1. `correlated_gaussian_law` proves only that for a single pair $(X, Y) \sim \mathcal{N}(0,1) \otimes \mathcal{N}(0,1)$ and $|r| < 1$, $(X + (rX + \sqrt{1-r^2}Y),\; (rX + \sqrt{1-r^2}Y) - X) \sim \mathcal{N}(0, v_1) \otimes \mathcal{N}(0, v_2)$ with $v_1 = 2(1+r)$, $v_2 = 2(1-r)$. It does not prove that $(2\sqrt{f}\,Z_1, 2\sqrt{g}\,Z_2)$ with $f=(1+r)/2, g=(1-r)/2$ has law $\mathcal{N}(0, v_1) \otimes \mathcal{N}(0, v_2)$, nor lift single-entry equality in distribution to the joint $n \times N$ matrices.
  2. In `question.md` line 59 and §3 line 50, $Q$ and $K$ have unscaled $\mathcal{N}(0,1)$ entries, whereas §3's ensemble divides $Q$ and $K$ by $\sqrt{N}$, so $L_{\text{question}} \stackrel{d}{=} N \cdot L_{\text{ensemble}}$. Deducing the limit profile of the question's unscaled model from `theoremB_ae` + `const_profile` requires scale invariance $\pi(c Q, c K) = \pi(Q, K)$ ($c = \sqrt{N} > 0$), which is not proved in Lean. (Note: §6 row 11 describes `const_profile` and `correlated_gaussian_law` more narrowly and accurately than §3 lines 49–50.)
- **How serious:** **the claim is unchecked as stated** (all three omitted steps are elementary and mathematically true, so the claim itself is correct, but Lean stops short of linking `question.md`'s unscaled Gaussian models to `theoremB_ae`).

### Finding 2 — "Condition on $\rho$", joint probability space, and measure existence in §3 / Theorem 2
- **Claim:** §3, lines 39–42: *"Draw an i.i.d. sequence $\rho_1,\rho_2,\dots$ from $\mu$ ... let $P,M\in\mathbb R^{n\times N}$ be the first $N$ columns of two infinite arrays of i.i.d. standard Gaussian entries, independent of each other and of the $\rho_i$ ... **Theorem 2.** Condition on $\rho$. As $N\to\infty$ with $n$ fixed, almost surely $\pi(L)$ converges to $\pi(L_\infty)$..."*
- **Lean theorems:** `TheoremBFull.lean`: `theoremB_ae`; `TheoremBExtra.lean`: `cd_limit_ae`.
- **What differs:**
  1. Lean never places $\rho$ and $(P, M)$ on a common probability space, never states independence of $(P, M)$ from $\rho$, and does not formalize regular conditional probability / disintegration. Instead, `theoremB_ae` replaces "Condition on $\rho$" by taking fixed deterministic vectors `fv gv : Fin n → ℝ` (`0 < fv i`, `0 < gv i`), and `cd_limit_ae` takes a separate probability space carrying `ρ : ℕ → Ω → ℝ`.
  2. Neither file constructs a probability space $(\Omega, \mathcal{F}, \mathbb{P})$ witnessing that infinite i.i.d. Gaussian arrays `Z` or i.i.d. sequences `ρ` from an arbitrary law $\mu$ exist (`Z` and `ρ` are universally quantified hypotheses; if no such space existed, the theorems would be vacuous, though existence is standard by Kolmogorov/infinite product measures).
  3. On the other hand, both `theoremB_ae` and `cd_limit_ae` assume only `Pairwise IndepFun` across columns / indices $i \ne j$, which is weaker than full mutual independence (making that part of the Lean statement slightly stronger than claimed).
- **How serious:** **the claim is unchecked as stated** with respect to the conditional-probability / joint-space step (mathematically valid and standard because $(P, M) \perp \rho$, so conditioning on $\rho = r$ reduces to deterministic $fv_i = f(r_i), gv_i = g(r_i)$).

### Finding 3 — Existence of an actual operator $L_\infty$ and gluing of Theorem 2's limit consequences (§3 line 42 & §6 lines 88–89)
- **Claim:** §3, line 42: *"almost surely $\pi(L)$ converges to $\pi(L_\infty)$, where $L_\infty$ is a sum of rank-one forms on orthogonal planes with $\alpha_i=f(\rho_i)$ and $\beta_i=g(\rho_i)$ ... Hence $a-b\to0$, and relation (1) holds with equality in the limit."* and §6, line 88: *"convergence of the profile and of the relation-(1) error, to the profile of an actual sum $L_\infty$ of rank-one forms on orthogonal planes | `theoremB_ae`, `blocks_of_limit_gram`, `gprof_at_limit`"*.
- **Lean theorems:** `TheoremBFull.lean`: `theoremB_ae` (and `private lemma limit_config`); `TheoremB.lean`: `blocks_of_limit_gram`; `Limit.lean`: `gprof_at_limit`; `TheoremBExtra.lean`: `similarlyOrdered_of_monotone`, `limit_a_eq_b`, `limit_mem_Theta`.
- **What differs:**
  1. `theoremB_ae` proves convergence of `(gA, gB, gC, gD)` to the algebraic formulas `(profA fv gv, profB fv gv σ τ, profC fv gv σ τ, profD fv gv σ τ)`. Both `blocks_of_limit_gram` and `gprof_at_limit` are implications *assuming* rows `q, k : Fin n → EuclideanSpace ℝ (Fin N)` (with `2 * n ≤ N`) satisfy the limit Gram equations `hqq`, `hkk`, `hqk`. The lemma showing such rows exist from any orthonormal family `e : Fin (n + n) → EuclideanSpace ℝ (Fin N)` is `private lemma limit_config` (`TheoremBFull.lean:192`), so no public theorem combines `EuclideanSpace.basisFun` (at $N = 2n$), `limit_config`, `blocks_of_limit_gram`, `gprof_at_limit`, and `theoremB_ae` into a single theorem quantified over an actual operator $L_\infty$.
  2. In `theoremB_ae`, `Tendsto gErr ... (𝓝 0)` is guarded by `SimilarlyOrdered fv gv → ...`; plugging `similarlyOrdered_of_monotone` into that implication, and subtracting `gB → profB` from `gA → profA` using `limit_a_eq_b` to get `gA - gB → 0` (which §6 line 89 explicitly notes), are left as unbundled 1-line consequences.
- **How serious:** **a harmless difference** (every mathematical step — including `private lemma limit_config` — is already proved in `TheoremBFull.lean`, `Limit.lean`, and `TheoremBExtra.lean`).

### Finding 4 — Extra `Measurable f` and `Measurable g` hypotheses in `cd_limit_ae`
- **Claim:** §3, lines 39 & 42–43: *"Fix $n\ge1$, a law $\mu$ on $\mathbb R$, and functions $f,g:\mathbb R\to(0,\infty)$ that are both nondecreasing ... If also $\mathbb E[(f+g)(\rho)^2]<\infty$ for $\rho\sim\mu$, then, as $n\to\infty$, almost surely $c(L_\infty)-d(L_\infty)\to\dots$"*
- **Lean theorem:** `TheoremBExtra.lean`: `cd_limit_ae` (lines 65–74).
- **What differs:** `cd_limit_ae` adds explicit hypotheses `(hfm : Measurable f) (hgm : Measurable g)` alongside `(hf : Monotone f) (hg : Monotone g)`.
- **How serious:** **a harmless difference** (over $\mathbb{R}$ with its Borel $\sigma$-algebra, every `Monotone` function is Borel-measurable via Mathlib's `Monotone.measurable`, so `hfm` and `hgm` do not mathematically restrict $f, g$).

### Finding 5 — Unstated `2 * n ≤ N` and `|t_i| < 1` (vs. $u_i \ne \pm v_i$) hypotheses in §1 bullet 2 and §2 Theorem 1
- **Claim:** §1, lines 14–15 ($a - b = c + d - m_2 - q$) and §2, lines 22 & 26–30 (definition of sum of rank-one forms on orthogonal planes with $u_i \ne \pm v_i$, and Theorem 1(1)–(4)).
- **Lean theorems:** `Identities.lean`: `gprof_sum_eq_one`, `gA_sub_gB_identity`; `Spectral.lean`: `charpoly_S`, etc.; `Main.lean`: `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff`; `TheoremAExtra.lean`: `main_d_eq_zero_iff`, `main_c_eq_zero_iff`.
- **What differs:**
  1. All of these Lean theorems take an explicit hypothesis `(hN : 2 * n ≤ N)`. In §1, $N \ge 2n$ is stated in bullet 1 (line 13) and globally in `question.md` line 23 ($n \le N/2$), though not repeated in bullet 2 (and internally `Identities.gsum_general` only needs `n ≤ N`, which already follows from `Orthonormal ℝ u`). In §2 Theorem 1, $N \ge 2n$ is not stated in the theorem text because $n$ mutually orthogonal 2-dimensional planes $\mathrm{span}(u_i, v_i)$ ($u_i \ne \pm v_i$) in $\mathbb{R}^N$ mathematically force $2n \le N$; Lean simply assumes `2 * n ≤ N` rather than deriving it from `OrthoBlocks` + `hT`.
  2. §2 line 22 defines blocks via unit vectors with $u_i \ne \pm v_i$ and remarks that $t_i = u_i^\top v_i \in (-1, 1)$; Lean's `OrthoBlocks` theorems take `(hT : ∀ i, |B.t i| < 1)` directly rather than deriving it from $u_i \ne \pm v_i$ by Cauchy–Schwarz.
- **How serious:** **a harmless difference** (mathematically equivalent hypotheses).

### Finding 6 — Lemma 1 stated for a single block vs. Lean's $n$-block characteristic polynomials on $-T^2$
- **Claim:** §2, line 24 (Lemma 1) and §6, line 85: *"The symmetric part of block $i$ has eigenvalues $\alpha_i>0$ and $-\beta_i<0$, and the antisymmetric part of block $i$ has singular value $\sqrt{\alpha_i\beta_i}$ with multiplicity 2."*
- **Lean theorems:** `Spectral.lean`: `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg`, `roots_neg_T_sq_pos`; `Geometry.lean`: `α_pos`, `β_pos` (plus `S_add`, `S_sub`, `neg_T_sq_add`, `neg_T_sq_sub`).
- **What differs:** `Spectral.lean` proves the characteristic polynomials and positive/negative root multisets for the full $n$-block sum $B$ on $\mathbb{R}^N$ (including the $X^{N-2n}$ zero-eigenvalue factor), and states that `-(B.Tlin ∘ₗ B.Tlin)` has positive roots $\alpha_i \beta_i$ with multiplicity 2 (taking square roots to get singular values $\sqrt{\alpha_i \beta_i}$ happens in `Main.lean:sv_sorted` and `Limit.lean:lists_at_limit`). Specializing `n = 1` recovers a single block.
- **How serious:** **a harmless difference**.

### Finding 7 — Theorem 1(5) witness fixes $(n, N) = (1, 2)$
- **Claim:** §2, lines 26, 31, 33: *"Let $L$ be a sum of $n\ge1$ rank-one forms on orthogonal planes. Then: ... 5. Every point of $\Theta$ other than the two endpoints of $\Theta$ is $\pi(L')$ for some $L'$ in normal form."* (Proof sketch, line 33: *"Equal tilts $t_i=t$ give the rank-one profiles, which gives item 5."*)
- **Lean theorem:** `TheoremAExtra.lean`: `theta_attained` (line 83).
- **What differs:** `theta_attained` constructs $L'$ specifically in `OrthoBlocks 1 2` ($n = 1, N = 2$), rather than for an arbitrary $n \ge 1, N \ge 2n$ with equal tilts $t_i = t$ as sketched in line 33. However, item 5 only asserts "for some $L'$ in normal form", line 35 explicitly notes that items 1–4 (not 5) hold for every $n \ge 1$, and §6 line 87 explicitly discloses *"with a witness of one block in $\mathbb R^2$"*. Also, `theta_attained` encodes "other than the two endpoints of $\Theta$" as `0 < a` with `0 ≤ c, 0 ≤ d, c * d = 0, 2 * a + c + d = 1`, which is exact since $a = 0$ on $\Theta$ yields precisely $(0,0,1,0)$ and $(0,0,0,1)$.
- **How serious:** **a harmless difference**.

### Finding 8 — Unstated `1 ≤ κ` (and $f, g > 0$) in §7 fixed-ratio bound prose
- **Claim:** §7, line 99: *"Writing $x$ for the iterated-limit value and $y$ for the fixed-ratio value, $x\le y\le x(1+1/\kappa)$ ... and for $f=g$, $x=y=0$; Lean checks this bound as `fixed_ratio_bound` in `Ratio.lean`"*
- **Lean theorem:** `Ratio.lean`: `fixed_ratio_bound` (line 14).
- **What differs:** `fixed_ratio_bound` requires `(hκ : 1 ≤ κ) (hf : 0 < f) (hg : 0 < g)`. In context, $f, g > 0$ comes from §3 and heads satisfy $N \ge 2n$ so $\kappa = N/n \ge 2 \ge 1$ (and mathematically the inequality holds for all $\kappa > 0$, failing only for $\kappa \le 0$). The remark $f = g \implies x = y = 0$ is an immediate specialization of $0 \le y \le 0$ rather than a separate lemma.
- **How serious:** **a harmless difference**.

### Finding 9 — Minor unformalized prose glosses and unbundled wrappers (§1 lines 13, 16; §3 lines 44, 48)
- **Claims & Lean theorems:**
  - §1, line 13 & §6, line 82 (`Congruence.lean`, `Bridge.lean`, `Extras.lean`): `exists_isometry_of_same_W` does not even need §1's $N \ge 2n$ hypothesis (Lean proves a stronger statement valid for all $N$). `gprof_eq_of_same_W` bundles `exists_isometry_of_same_W` + `gprof_isometry` for the profile and `gErr`, whereas for spectral lists (`lists_isometry`) and operator conjugation (`formL_isometry`) the two-line `map_smul` glue is not wrapped into a separate `_of_same_W` lemma.
  - §1, line 16 & §6, line 92 (`Extras.lean`: `logratio_sum_zero`, `eq_zero_of_sum_zero_of_const`): Lean proves $\sum r_i = 0$ and $(\forall i, r_i = c) \implies \forall i, r_i = 0$ (assuming `[NeZero n]`); the final Equivalence $r_i = 0 \iff \sigma(T)_i = \sqrt{\lambda_{+,i}\lambda_{-,i}}$ via strict positivity (`lists_pos`) and `Real.log` injectivity is left implicit in prose (*"relation (1) can fail only through the spread of the $r_i$ over $i$"*).
  - §3, line 44 & §6, line 92 (`Extras.lean`: `weighted_tilt`): proves the pointwise algebraic identity $(f+g)^2 t|t| = (f-g)|f-g|$ for $f + g > 0$; taking expectations and forming the weighted mean ratio is left to prose. Also $t_i = (f(\rho_i)-g(\rho_i))/(f(\rho_i)+g(\rho_i))$ is proved internally (`have ht`, `TheoremB.lean:172`) rather than exported in `blocks_of_limit_gram`'s statement.
  - §3, line 48 (*"In words: row $i$ of $Q+K$ has squared norm close to $4f(\rho_i)$..."*): informal heuristic summary of the ensemble, not a separate Lean theorem (though immediate from `gram_slln`).
- **How serious:** **a harmless difference** in all four cases.

---

## 3. Claims Where Answer and Lean Match

- **§1 SVD-form existence and operator-only dependence** (line 11; §6 line 81): matches `Bridge.exists_svd_rows` and `Bridge.gprof_of_formL_eq` (with row count $n = \operatorname{rank} L$ fixed).
- **§1 $(\Sigma, W)$ orthogonal congruence and invariance** (line 13; §6 line 82): matches `Congruence.exists_isometry_of_same_W`, `Congruence.gprof_isometry`, `Congruence.gprof_eq_of_same_W`, `Bridge.lists_isometry`, and `Extras.formL_isometry` (modulo the trivial wrapper note in Finding 9).
- **§1 Exact identities $a = \frac{1}{2}(1 - m_2 - q)$ and $a - b = c + d - m_2 - q$** (lines 14–15; §6 line 83): match `Identities.gA_identity`, `Identities.gprof_sum_eq_one`, and `Identities.gA_sub_gB_identity` (modulo Finding 5 on $2n \le N$).
- **§1 Log-determinant identity $\prod \sigma(T)_i^2 = \prod \lambda_{+,i}\lambda_{-,i} = \det G / 4^n$ and $\sum \log \sigma(T)_i = \frac{1}{2}\sum \log(\lambda_{+,i}\lambda_{-,i})$** (line 16; §6 line 84): matches `LogDet.prod_sig_eq_det`, `LogDet.prod_lam_eq_det`, and `LogDet.logdet_identity` (`LinearIndependent ℝ (stackRows q k)` + `2 * n ≤ N` is exact for $\operatorname{rank} F = 2n$, and `lists_pos` rules out `Real.log` junk values).
- **§2 Theorem 1(1)–(4)** (lines 26–30; §6 line 86) & **§4 application of Theorem 1(1)** (line 68): match `Main.main_a_le_b`, `Main.main_a_eq_b_iff`, `Main.main_relation_one`, `Main.main_c_sub_d`, `Main.main_mem_Theta_iff`, `TheoremAExtra.main_d_eq_zero_iff`, and `TheoremAExtra.main_c_eq_zero_iff` (modulo Finding 5). Even if a nonzero $n$-row head had $m < n$ orthogonal blocks, zero-padding of $\lambda_+, \lambda_-$ leaves $a$ and $b$ unchanged, so §4 line 68's deduction from $a > b$ is also sound.
- **§3 SLLN for ratios and $c(L_\infty) - d(L_\infty)$ formula** (lines 43, 46; §6 line 90): match `Probability.ratio_slln`, `TheoremBExtra.cd_eq_ratio`, and `TheoremBExtra.cd_limit_ae` (modulo Finding 4).
- **§7 Iterated-limit formula $1 - 2a = (f-g)^2/(f+g)^2$ for constant $f, g > 0$** (line 99): matches `Extras.const_one_sub_two_a`.
- **§6 Table & Axiom Statement** (lines 77–92): Every theorem name and file attribution in the §6 table is accurate (subject to the nuances noted in Findings 1, 3, 5, 6), and visual inspection of all 23 files confirms zero `sorry`/`axiom` declarations, though `#print axioms` was not machine-executed before interruption.
