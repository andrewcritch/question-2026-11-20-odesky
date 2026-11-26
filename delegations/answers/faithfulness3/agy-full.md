**Verdict:** Every mathematical claim in §1–§3 and §7 is mathematically true and its core content is proved in Lean (with only standard axioms `propext`, `Classical.choice`, `Quot.sound`), but several bridging steps and scope claims are **unchecked as stated**, and one statement in §6 about what Lean assumes for the relation-(1) error **is wrong**.

---

## 1. Overview of Definitions Checked

Across the 23 files in `OdeskyLean/`, all core mathematical objects match the question (`question.md`) and draft answer (`answer_draft.md`) on the head regime $n \ge 1$, $N \ge 2n$:

- **Bilinear form and parts (`GenProfile.lean`, `Geometry.lean`):** For rows $q_i, k_i \in \mathbb{R}^N$ of $Q, K \in \mathbb{R}^{n \times N}$, `formL q k x = ∑ i, ⟪q i, x⟫ • k i` agrees with $(K^\top Q)x = \sum_i k_i q_i^\top x$; for SVD rows `q i = σ i • v i`, `k i = u i`, `formL (fun i => σ i • v i) u` agrees with $U\Sigma V^\top = \sum_i \sigma_i u_i v_i^\top$, as does `OrthoBlocks.L`. Symmetric and antisymmetric parts `formS` and `formT` are $\tfrac12(L \pm L^\top)$, with $-(T \circ T) = T^\top T$.
- **Spectral lists (`GenProfile.lean`, `LogDet.lean`, `Main.lean`):** Mathlib's `IsSymmetric.eigenvalues` is decreasing (`Antitone`). For $2n \le N$, `lamP` takes the $n$ largest positive eigenvalues of $S$, `lamM` takes the $n$ largest absolute negative eigenvalues of $S$, and `sigT` takes every even-indexed square root of `eigT2` (justified for general skew $T$ by `pair_eq` in `LogDet.lean`, which proves positive eigenvalues of $-T^2$ occur in equal pairs). `Main.lean` instead axiomatizes decreasing root multisets via `SpectralLists`, bridged by `spectralLists_exists` (`Main.lean`), `roots_charpoly_eq_eigenvalues` (`Weyl.lean`), and `lists_at_limit` / `gprof_at_limit` (`Limit.lean`).
- **Frobenius norms, profile, $\Theta$, tilts, similar ordering, normal form:** `frobL_eq` and `frobT_eq` (`GenProfile.lean`) and `frob_L`, `frob_S`, `frob_T` (`Spectral.lean`) verify that the Gram-matrix formulas equal $\sum_t \|L b_t\|^2$ and $\sum_t \|T b_t\|^2$ in any orthonormal basis. `gA, gB, gC, gD`, `pa, pb, pc, pd`, and `profA, profB, profC, profD` match $(a,b,c,d)$; `gErr` matches $\|\sigma(T) - \sqrt{\lambda_+\lambda_-}\|_2 / \|\sigma(T)\|_2$; `SimilarlyOrdered` matches $(\alpha_i - \alpha_j)(\beta_i - \beta_j) \ge 0$ for all $i,j$; normal form in `main_mem_Theta_iff` matches similar ordering plus tilts all $\ge 0$ or all $\le 0$.
- **Ensemble and signs (`TheoremBFull.lean`, `Gaussian.lean`, `Probability.lean`):** `qOf` and `kOf` define rows $q_i = \sqrt{f_i}\,x_i - \sqrt{g_i}\,x_{n+i}$ and $k_i = \sqrt{f_i}\,x_i + \sqrt{g_i}\,x_{n+i}$ where `colVec` divides standard Gaussian (`gaussianReal 0 1`, mean $0$, variance $1$) entries by $\sqrt N$, giving $Q+K = 2\,\mathrm{diag}(\sqrt{f})P/\sqrt N$ and $K-Q = 2\,\mathrm{diag}(\sqrt{g})M/\sqrt N$, with limit block tilt $t_i = (f_i - g_i)/(f_i + g_i)$ and eigenvalues $\alpha_i = f_i$, $\beta_i = g_i$.
- **Axioms:** Running `#print axioms` on all 38 cited Lean theorems confirms every one depends only on `[propext, Classical.choice, Quot.sound]`.

---

## 2. Detailed Findings (Discrepancies, Unchecked Steps, and §6 Inaccuracies)

### Finding 1 — §6 statement on what Lean assumes for `gErr`
- **Claim (`answer_draft.md`, §6, line 77):** *"For degenerate heads, Lean pads missing entries of the spectral lists with zeros and takes $x/0=0$; the statements about the relation-(1) error assume $T\ne0$, where its denominator is positive."*
- **Lean theorems:** `Bridge.lean`: `gprof_of_formL_eq`; `Congruence.lean`: `gprof_isometry`, `gprof_eq_of_same_W`; `Limit.lean`: `gprof_at_limit`; `TheoremBFull.lean`: `profile_tendsto`, `theoremB_ae` (and `GenProfile.lean`: `lamM`, `gErr`).
- **What differs:**
  1. **No theorem in Lean assumes $T \ne 0$.** Three of the theorems about `gErr` (`gprof_of_formL_eq`, `gprof_isometry`, `gprof_eq_of_same_W`) put **no** nonvanishing hypothesis on $T$ at all (when $T = 0$, `gErr` evaluates to `0 / 0 = 0` by Lean's division-by-zero convention). The other three (`gprof_at_limit`, `profile_tendsto`, `theoremB_ae`) assume `[NeZero n]` and `∀ i, 0 < fv i`, `∀ i, 0 < gv i` on the limit blocks — which forces all $n$ singular values of $T_\infty$ to be strictly positive (stronger than $T_\infty \ne 0$ when $n > 1$), while making no assumption $T_N \ne 0$ at finite $N$.
  2. In addition, the first clause (*"Lean pads missing entries of the spectral lists with zeros"*) holds when $n \le N$ (and in particular for all heads $2n \le N$), but fails for $1 \le N < n$ despite `GenProfile.lean`'s docstring claiming *"no hypothesis `2n ≤ N` is needed to define them"*: `lamM` (`GenProfile.lean`, line 108) indexes `eigAt (eigS q k) (N - 1 - (j : ℕ))` using truncating natural-number subtraction, so for $j \ge N \ge 1$ we get `N - 1 - j = 0 < N`, repeating `max (-eigS q k 0) 0` rather than padding with `0`.
- **Severity:** **The claim is wrong** (as a meta-statement in §6 describing the Lean formalization; the `lamM` truncation when $N < n$ is a harmless difference for the theorems in §1–§3 because heads satisfy $2n \le N$ or $N \to \infty$).

---

### Finding 2 — §3 special cases: law of the ensemble entries, scale invariance, and the Gaussian baseline limit
- **Claim (`answer_draft.md`, §3, lines 49–50, and §6, line 77):**
  - Line 49: *"For $f=(1+r)/2$ and $g=(1-r)/2$, this is the law of the corresponding entry of $(2\sqrt f\,P,\;2\sqrt g\,M)$, i.e., of $\sqrt N\,(Q+K,\;K-Q)$ in the ensemble."*
  - Line 50: *"for $r=0$, the question's model has $Q$ and $K$ with independent standard Gaussian entries, and the previous item matches it entry by entry, up to the factor $\sqrt N$, with $f=g=\tfrac12$. This case is the Gaussian baseline. By Theorem 2, its limit profile is the midpoint $(\tfrac12,\tfrac12,0,0)$ of $\Theta$."*
  - Line 77: *"Every theorem and identity in §1–§3 is checked in Lean..."*
- **Lean theorems:** `SpecialCases.lean`: `correlated_gaussian_law`, `const_profile`.
- **What differs:** `correlated_gaussian_law` proves that if $(p_1, p_2) \sim \mathcal{N}(0,1) \otimes \mathcal{N}(0,1)$ and $|r|<1$, then $(p_1 + (rp_1 + \sqrt{1-r^2}p_2),\; (rp_1 + \sqrt{1-r^2}p_2) - p_1)$ has law $\mathcal{N}(0, v_1) \otimes \mathcal{N}(0, v_2)$ with $v_1 = 2(1+r)$, $v_2 = 2(1-r)$. `const_profile` proves algebraically that `profA = profB = 1/2` and `profC = profD = 0` when $\alpha_i = \beta_i = c > 0$. Lean does **not** prove:
  1. that $(2\sqrt{f}\,P_{ij}, 2\sqrt{g}\,M_{ij})$ with $f=(1+r)/2$, $g=(1-r)/2$ has law $\mathcal{N}(0, v_1) \otimes \mathcal{N}(0, v_2)$ (or equality of joint matrix laws across entries);
  2. scale invariance of the profile (`gprof (c • q) (c • k) = gprof q k` for $c = \sqrt N > 0$), which is needed to pass from the ensemble's $1/\sqrt N$-normalized $(Q, K)$ to the question's unscaled Gaussian $(Q, K)$;
  3. the chained theorem that the question's i.i.d. Gaussian baseline $(Q, K)$ has limit profile $(\tfrac12, \tfrac12, 0, 0)$ a.s. as $N \to \infty$.
  (Note: §6 row 11 accurately states the narrower facts proved in `SpecialCases.lean`, whereas §3 lines 49–50 and §6 line 77 claim more.) Also, §3 line 48's informal statement that row $i$ of $Q+K$ (resp. $K-Q$) has squared norm close to $4f(\rho_i)$ (resp. $4g(\rho_i)$) has no dedicated Lean lemma.
- **Severity:** **The claim is unchecked as stated** (all unformalized steps are mathematically valid).

---

### Finding 3 — Theorem 2: joint probability space and conditioning on $\rho$
- **Claim (`answer_draft.md`, §3, lines 39–43):** §3 defines a single ensemble with $\rho_1, \rho_2, \dots \stackrel{\text{i.i.d.}}{\sim} \mu$ and Gaussian arrays $P, M$ independent of each other and of $\rho$. Theorem 2 states: *"Fix the values of $\rho_1,\dots,\rho_n$ (since $P,M$ are independent of $\rho$, this is conditioning on $\rho$). As $N\to\infty$ with $n$ fixed, almost surely $\pi(L)$ converges to $\pi(L_\infty)$..."* and then takes $n \to \infty$ almost surely over random $\rho_1, \rho_2, \dots \sim \mu$.
- **Lean theorems:** `TheoremBFull.lean`: `theoremB_ae`; `TheoremBExtra.lean`: `cd_limit_ae`.
- **What differs:**
  1. `theoremB_ae` takes deterministic positive vectors `fv gv : Fin n → ℝ` and a sequence of random column vectors `Z : ℕ → Ω → (Fin (n + n) → ℝ)` on an abstract probability space `(Ω, μ)`. Separately, `cd_limit_ae` takes a sequence `ρ : ℕ → Ω → ℝ` on an abstract probability space `(Ω, μ)`.
  2. Lean never constructs a joint probability space carrying $(\rho, P, M)$ (nor proves existence of `(Ω, μ)` carrying infinite i.i.d. sequences via product measures), and does **not** formalize the parenthetical claim that fixing $\rho_1, \dots, \rho_n$ equals conditioning on $\rho$ under independence of $(P, M)$ and $\rho$ (nor deduce unconditional a.s. convergence on the joint space).
- **Severity:** **The claim is unchecked as stated** for the parenthetical conditioning claim and joint-space existence (fixing $\rho_1,\dots,\rho_n$ deterministically in the $N \to \infty$ limit and randomizing $\rho$ in the $n \to \infty$ limit match `theoremB_ae` and `cd_limit_ae` individually).

---

### Finding 4 — Theorem 2 and §6 row 8: unconditional existence of the operator $L_\infty$ and chaining of limit consequences
- **Claim (`answer_draft.md`, §3, line 42, and §6, lines 77 & 88–89):**
  - Line 42: *"almost surely $\pi(L)$ converges to $\pi(L_\infty)$, where $L_\infty$ is a sum of rank-one forms on orthogonal planes with $\alpha_i=f(\rho_i)$ and $\beta_i=g(\rho_i)$... Hence $a-b\to0$, and relation (1) holds with equality in the limit."*
  - Line 88: *"Theorem 2: convergence of the profile and of the relation-(1) error, to the profile of an actual sum $L_\infty$ of rank-one forms on orthogonal planes | `theoremB_ae`, `blocks_of_limit_gram`, `gprof_at_limit`"*
- **Lean theorems:** `TheoremBFull.lean`: `theoremB_ae` (and `private lemma limit_config`); `TheoremB.lean`: `blocks_of_limit_gram`; `Limit.lean`: `gprof_at_limit`; `TheoremBExtra.lean`: `similarlyOrdered_of_monotone`, `limit_a_eq_b`, `limit_mem_Theta`.
- **What differs:**
  1. `theoremB_ae` proves convergence of `(gA, gB, gC, gD)` to the algebraic formulas `(profA fv gv, profB fv gv σ τ, profC fv gv σ τ, profD fv gv σ τ)` (and `SimilarlyOrdered fv gv → gErr → 0`). Meanwhile, `blocks_of_limit_gram` and `gprof_at_limit` are **conditional**: they take as inputs vectors `q, k : Fin n → ℝ^N` (with `2 * n ≤ N` in `gprof_at_limit`) assumed to satisfy the limit Gram equations `hqq`, `hkk`, `hqk`. Although `private lemma limit_config` (`TheoremBFull.lean`, line 192) builds such `q, k` from any `e : Fin (n + n) → ℝ^N` with `Orthonormal ℝ e`, no public theorem instantiates `e` (e.g., with `EuclideanSpace.basisFun (Fin (n + n)) ℝ`) to prove unconditionally that an actual operator $L_\infty$ exists for every `fv, gv > 0`.
  2. Similarly, Lean does not export a combined theorem chaining `similarlyOrdered_of_monotone`, `limit_a_eq_b`, and `theoremB_ae` to state `gA - gB → 0` and `gErr → 0` directly under `Monotone f` and `Monotone g` (as §6 row 9 partially notes with *"so, with the previous row, $a - b \to 0$"*).
  3. In §6 line 77 (*"which `Main.lean` and `Limit.lean` identify with the profile of the operator"*), `Main.lean`'s identification lemmas `nL_eq` and `pa_eq` are `private` (and `pb, pc, pd` are identified inline inside proofs), whereas `Limit.lean` exports `gprof_at_limit` publicly.
- **Severity:** **The claim is unchecked as stated** with respect to unconditional existence of $L_\infty$ in §6 row 8 and the unchained 2-line corollaries (all substantive ingredients, including `private lemma limit_config`, are proved in Lean, so mathematically there is no gap).

---

### Finding 5 — §1 bullet 2: omitted $N \ge 2n$ hypothesis on $a - b = c + d - m_2 - q$
- **Claim (`answer_draft.md`, §1, lines 11 & 14–15):** With $L = U\Sigma V^\top$ of rank $n \ge 1$ and $U, V \in \mathbb{R}^{N \times n}$ having orthonormal columns (which itself only forces $N \ge n$), bullet 1 explicitly writes *"For $N \ge 2n$, ..."*, whereas bullet 2 omits $N \ge 2n$ and states: *"Then exactly $a=\tfrac12(1-m_2-q),\; a-b=c+d-m_2-q$."*
- **Lean theorems:** `Identities.lean`: `gA_identity`, `gprof_sum_eq_one`, `gA_sub_gB_identity`.
- **What differs:** `gA_identity` needs no bound on $N$, but `gprof_sum_eq_one` and `gA_sub_gB_identity` add `(hN : 2 * n ≤ N)`. (Interestingly, the private helper `gsum_general` on line 183 of `Identities.lean` already proved `a + b + c + d = 1` under `n ≤ N`, which follows automatically from `Orthonormal ℝ u`, so the identity is mathematically true even for $n \le N < 2n$, and `question.md` line 23 assumes $n \le N/2$ for heads.) Also, `Identities.lean` states these for SVD rows `(fun i => σ i • v i) u`, which connect to general rank-$n$ heads `(q, k)` via `exists_svd_rows` and `gprof_of_formL_eq` in `Bridge.lean`.
- **Severity:** **A harmless difference** if $n \le N/2$ ($N \ge 2n$) is read as standing head notation from `question.md`; **unchecked as stated** on the range $n \le N < 2n$ if §1 bullet 2 is read standalone in contrast to bullet 1's explicit *"For $N \ge 2n$"*.

---

### Finding 6 — §7 bullet 4: omitted $\kappa \ge 1$ hypothesis on `fixed_ratio_bound` and elementary corollaries
- **Claim (`answer_draft.md`, §7, line 99):** *"Writing $x$ for the iterated-limit value and $y$ for the fixed-ratio value, $x\le y\le x(1+1/\kappa)$: for $f\ne g$, a relative difference of at most $1/\kappa$, which is 5–8% for the measured models ($\kappa=12$–$20$), and for $f=g$, $x=y=0$; Lean checks this bound as `fixed_ratio_bound` in `Ratio.lean`, and the value of $x$ as `const_one_sub_two_a` in `Extras.lean`."*
- **Lean theorems:** `Ratio.lean`: `fixed_ratio_bound`; `Extras.lean`: `const_one_sub_two_a`.
- **What differs:** `fixed_ratio_bound` assumes `(hκ : 1 ≤ κ)` alongside `(hf : 0 < f)` and `(hg : 0 < g)`. Line 99 does not state $\kappa \ge 1$ (though for heads with $N \ge 2n$, $\kappa = N/n \ge 2 \ge 1$, and for the measured models $\kappa \in [12, 20]$; algebraically the bound actually holds for all $\kappa > 0$ because $0 \le x < 1$). The immediate consequences $(y - x)/x \le 1/\kappa$ for $f \ne g$, the arithmetic $1/20 = 5\%$ to $1/12 \approx 8.3\%$, and $f = g \implies x = y = 0$ are not separately formalized in `Ratio.lean`.
- **Severity:** **A harmless difference** in the head regime $N \ge 2n$ ($\kappa \ge 2$); **unchecked as stated** as a pure real inequality for $0 < \kappa < 1$.

---

### Finding 7 — §2 definitions and Theorem 1: `u_i ≠ ±v_i` vs `|t_i| < 1`, explicit `2 * n ≤ N`, single-block vs $n$-block Lemma 1, and $n=1, N=2$ witness in Theorem 1(5)
- **Claim (`answer_draft.md`, §2, lines 22–33, and §6, lines 85–87):** Definition of sum of rank-one forms on orthogonal planes ($u_i \ne \pm v_i \implies t_i \in (-1,1)$), Lemma 1, and Theorem 1(1)–(5).
- **Lean theorems:** `Geometry.lean`: `OrthoBlocks`, `α_pos`, `β_pos`; `Spectral.lean`: `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg`, `roots_neg_T_sq_pos`; `Main.lean`: `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff`; `TheoremAExtra.lean`: `main_d_eq_zero_iff`, `main_c_eq_zero_iff`, `theta_attained`.
- **What differs:**
  1. `OrthoBlocks` omits $u_i \ne \pm v_i$; `Spectral.lean`, `Main.lean`, and `TheoremAExtra.lean` instead take `(hT : ∀ i, |B.t i| < 1)` directly (equivalent for unit vectors by Cauchy–Schwarz, which is not separately proved).
  2. Every theorem in `Spectral.lean`, `Main.lean`, and `TheoremAExtra.lean` takes an explicit hypothesis `(hN : 2 * n ≤ N)` not written in Theorem 1. Because $n$ orthogonal blocks with $|t_i| < 1$ produce $2n$ nonzero orthogonal vectors $\{u_i \pm v_i\}$ in $\mathbb{R}^N$, $2n \le N$ is mathematically forced whenever such an `OrthoBlocks` exists, so `hN` does not narrow Theorem 1 mathematically.
  3. Lemma 1 is stated for a single block $i$, while `Spectral.lean` proves the characteristic polynomials and nonzero root multisets for the full $n$-block sum (specializing at $n = 1$ to Lemma 1 and directly supplying the $n$-block step used in Theorem 1).
  4. Theorem 1(5) is proved by `theta_attained` using a 1-block witness in $\mathbb{R}^2$ (`OrthoBlocks 1 2`), as explicitly noted in §6 row 7; this matches *"for some $L'$ in normal form"* in Theorem 1(5), though the proof sketch's *"Equal tilts $t_i = t$ give the rank-one profiles"* for arbitrary $n \ge 1, N \ge 2n$ is only instantiated at $n=1, N=2$.
  5. Theorem 1(4) (and Theorem 2) writes *"$\pi(L)\in\Theta$, i.e., relation (2) holds"*: in `question.md` line 49, observation (2) is *"lie close to $\Theta$ and spread along it"*, so for a single form Lean checks $\pi(L) \in \Theta$ (`a = b ∧ c * d = 0`), while spreading across $\Theta$ is addressed separately by `theta_attained` and `cd_limit_ae`.
- **Severity:** **A harmless difference.**

---

### Finding 8 — Theorem 2 (`cd_limit_ae`) measurability hypotheses and minor §1 unchained steps
- **Claim (`answer_draft.md`, §3, lines 39 & 42–43; §1, lines 13 & 16):** Nondecreasing $f, g : \mathbb{R} \to (0,\infty)$ in `cd_limit_ae`; congruence determination in §1 bullet 1; log-ratio zero-spread conclusion in §1 bullet 3.
- **Lean theorems:** `TheoremBExtra.lean`: `cd_limit_ae`; `Congruence.lean`: `exists_isometry_of_same_W`, `gprof_eq_of_same_W`; `Bridge.lean`: `lists_isometry`; `Extras.lean`: `formL_isometry`, `eq_zero_of_sum_zero_of_const`.
- **What differs:**
  1. `cd_limit_ae` includes explicit hypotheses `(hfm : Measurable f) (hgm : Measurable g)` alongside `(hf : Monotone f) (hg : Monotone g)`, and indexes block count as `Fin (n + 1)` as $n \to \infty$. On $\mathbb{R}$ with Mathlib's Borel measurable space, every `Monotone` function is automatically measurable (`Monotone.measurable`), so `hfm` and `hgm` do not narrow the mathematical theorem. Conversely, `theoremB_ae` and `cd_limit_ae` assume only *pairwise* independence across columns / draws rather than full mutual independence, and `cd_limit_ae` drops the sign-constancy hypothesis on $f - g$ suggested by *"If also..."* in Theorem 2 — making Lean strictly *more general* on those points.
  2. In §1 bullet 1, `exists_isometry_of_same_W` does not even need $N \ge 2n$ (more general than the prose); `gprof_eq_of_same_W` packages the congruence invariance for the profile and `gErr`, whereas combining `exists_isometry_of_same_W` with `formL_isometry` and `lists_isometry` for `formL (σ • v) u` is left as a 2-line `map_smul` step. In §1 bullet 3, `eq_zero_of_sum_zero_of_const` proves constant zero-sum lists vanish ($r_i = 0$), leaving $r_i = 0 \iff \sigma(T)_i = \sqrt{\lambda_{+,i}\lambda_{-,i}}$ (for positive entries, proved by `lists_pos`) implicit.
- **Severity:** **A harmless difference.**

---

## 3. Concise Summary of Matching Claims

Where a claim and its cited Lean theorems match (modulo the harmless differences noted above):

- **§1 SVD existence and representation independence (line 11; §6 row 1):** Matches `exists_svd_rows` and `gprof_of_formL_eq` (`Bridge.lean`).
- **§1 $(\Sigma, W)$ congruence determination and invariance (line 13; §6 row 2):** Matches `exists_isometry_of_same_W`, `gprof_isometry`, `gprof_eq_of_same_W` (`Congruence.lean`), `lists_isometry` (`Bridge.lean`), and `formL_isometry` (`Extras.lean`).
- **§1 exact formula $a = \tfrac12(1 - m_2 - q)$ and (for $N \ge 2n$) $a - b = c + d - m_2 - q$ (lines 14–15; §6 row 3):** Matches `gA_identity`, `gprof_sum_eq_one`, `gA_sub_gB_identity` (`Identities.lean`).
- **§1 log-determinant and Gram determinant identities (line 16; §6 rows 4 & 12):** Matches `lists_pos`, `prod_lam_eq_det`, `prod_sig_eq_det`, `logdet_identity` (`LogDet.lean`) and `logratio_sum_zero`, `eq_zero_of_sum_zero_of_const` (`Extras.lean`), with positivity of all $\log$ arguments proved in `lists_pos`.
- **§2 Lemma 1 and Theorem 1(1)–(5) (lines 24–31; §6 rows 5–7):** Match `α_pos`, `β_pos` (`Geometry.lean`), `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg`, `roots_neg_T_sq_pos` (`Spectral.lean`), `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff` (`Main.lean`), and `main_d_eq_zero_iff`, `main_c_eq_zero_iff`, `theta_attained` (`TheoremAExtra.lean`).
- **§3 Theorem 2 fixed-$\rho$ $N \to \infty$ convergence, monotonicity consequences, $n \to \infty$ SLLN for $c(L_\infty) - d(L_\infty)$, and weighted-tilt identity (lines 42–44; §6 rows 8–10 & 12):** Match `theoremB_ae` (`TheoremBFull.lean`), `similarlyOrdered_of_monotone`, `limit_a_eq_b`, `limit_mem_Theta`, `cd_eq_ratio`, `cd_limit_ae` (`TheoremBExtra.lean`), `ratio_slln` (`Probability.lean`), and `weighted_tilt` (`Extras.lean`), subject to Findings 3 and 4.
- **§7 iterated-limit formula $x = (f-g)^2/(f+g)^2$ and fixed-ratio bound $x \le y \le x(1+1/\kappa)$ for $\kappa \ge 1$ (line 99):** Match `const_one_sub_two_a` (`Extras.lean`) and `fixed_ratio_bound` (`Ratio.lean`), subject to Finding 6.

---

## 4. Claim Checked Hardest

The claim checked hardest was **Theorem 2 (§3, lines 39–44)** across `GenProfile.lean`, `Orthonormalize.lean`, `Perturb.lean`, `Weyl.lean`, `Limit.lean`, `TheoremB.lean`, `TheoremBFull.lean`, `TheoremBExtra.lean`, `Probability.lean`, and `Gaussian.lean`. Specifically, I checked:
1. **End-to-end sign conventions:** Solving $Q+K = 2\,\mathrm{diag}(\sqrt f)P/\sqrt N$ and $K-Q = 2\,\mathrm{diag}(\sqrt g)M/\sqrt N$ gives $Q = (\mathrm{diag}(\sqrt f)P - \mathrm{diag}(\sqrt g)M)/\sqrt N$ (`qOf`) and $K = (\mathrm{diag}(\sqrt f)P + \mathrm{diag}(\sqrt g)M)/\sqrt N$ (`kOf`). In `formL q k` ($= K^\top Q$), the limit unit vectors are $u_i \propto k_i$ and $v_i \propto q_i$, giving tilt $t_i = u_i^\top v_i = (f_i - g_i)/(f_i + g_i)$ (not flipped), $\alpha_i = f_i$, $\beta_i = g_i$, and positive $c - d$ when $f > g$ — consistent with $c - d \approx r|r|$ for $f = (1+r)/2$, $g = (1-r)/2$.
2. **Quantifier order for almost-sure convergence:** In `theoremB_ae` (`TheoremBFull.lean`, line 569) and `gram_slln` (`Probability.lean`, line 32), `∀ᵐ ω ∂μ` sits outside `Tendsto (fun N => ...) atTop`, proving genuine almost-sure convergence as $N \to \infty$ (via finite intersection `ae_all_iff` over `Fin (n + n)`), and `gaussianReal 0 1` in Mathlib is verified to take variance `1`.
3. **Perturbation and multiplicity counting at the limit:** Once $N \ge 2n$ (`eventually_ge_atTop (2 * n)` in `profile_tendsto`), `lamM`'s natural subtraction `N - 1 - j` cannot underflow, `eq_of_counts` with multiplicity factor `c = 2` in `Limit.lean` correctly extracts the paired eigenvalues of $-T^2$, and `cd_limit_ae` properly handles integrability of the numerator $|(f-g)|f-g|| \le (f+g)^2$ and strict positivity of the denominator $\mathbb{E}[(f+g)(\rho)^2] > 0$ from $f, g > 0$ on a probability space.
4. **Where the formalization stops:** This check also surfaced Findings 3 and 4 (separate probability spaces for `Z` and `ρ` without formalizing conditioning, and `limit_config` being left `private` rather than exporting unconditional existence of $L_\infty$).
