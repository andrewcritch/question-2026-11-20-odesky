**Verdict: Mostly faithful on the core theorems, but overstated in §6—none of the main mathematical claims are false under their intended reading, yet six claims/hypotheses in §1–§3 are unchecked as stated (most notably Theorem 2's sign condition on $\operatorname{supp}(\mu)$, the SVD bridge from $L=K^\top Q$, the `gErr` $0/0$ degeneracy vs. relation (1), explicit $|t_i|<1$ in §2, the correlated-Gaussian reduction up to scale, and §3's non-determination by the law of $t$ alone), and §6 misdescribes how several files compute the profile.**

---

## 1. Overview & Claim Checked Hardest

All 21 modules in `lean/OdeskyLean/*.lean` were read in full alongside `question.md` and `answer_draft.md`, and `#print axioms` was verified on all 29 theorems listed in §6 and §7 (confirming only `[propext, Classical.choice, Quot.sound]` and zero `sorry`).

**Claim checked hardest:** **Theorem 2 (§3, lines 39–45)** across the 9-file chain `GenProfile.lean` $\to$ `Weyl.lean` $\to$ `Orthonormalize.lean` $\to$ `Perturb.lean` $\to$ `TheoremB.lean` $\to$ `Limit.lean` $\to$ `Gaussian.lean` $\to$ `Probability.lean` $\to$ `TheoremBFull.lean` + `TheoremBExtra.lean`. Specifically, I traced:
1. the exact sign and factor-of-$2/\sqrt{N}$ correspondence between $Q+K, K-Q$ (line 40) and `qOf`, `kOf`, `colVec` (`TheoremBFull.lean:41–49, 541–545`);
2. whether `GenProfile.lean`'s zero-padded eigenvalue definitions (`lamP`, `lamM`, `sigT`) and relative-error ratio `gErr` suffer from Lean's `x / 0 = 0` convention along the $N \to \infty$ limit (in `TheoremBFull.lean:532`, strict positivity $f(\rho_i), g(\rho_i) > 0$ and `[NeZero n]` guarantee the limit denominator of `gErr` is strictly positive, preventing spurious `0 / 0 = 0` convergence—unlike in §1's general rank-$n$ setting, see Finding F3);
3. the quantifier and conditioning structure on $\rho$ vs. $(P, M)$, which exposed the gap between "on the support of $\mu$" in prose and global sign constancy on $\mathbb{R}$ in `limit_mem_Theta` (Finding F1), as well as the split between deterministic `(fv, gv)` in `theoremB_ae` and random `ρ : ℕ → Ω → ℝ` in `cd_limit_ae` (Finding F7).

---

## 2. Audit of Definitions (Answer vs. Lean)

- **Bilinear form $L = K^\top Q$, $S$, $T$**: `GenProfile.lean` (`formL`, `formS`, `formT`) defines $L x = \sum_{i<n} \langle q_i, x \rangle k_i$ for rows $q_i, k_i \in \mathbb{R}^N$, matching $L = K^\top Q = \sum_i k_i q_i^\top$, $S = (L+L^\top)/2$, $T = (L-L^\top)/2$. `Geometry.lean` (`OrthoBlocks.L`, `S`, `T`) defines $L x = \sum_i s_i \langle v_i, x \rangle u_i$, matching $\sum_i \sigma_i u_i v_i^\top$.
- **Spectral lists ($\lambda_+$, $\lambda_-$, $\sigma(T)$)**: Lean has **two** operator-level definitions:
  1. `GenProfile.lean` (`lamP`, `lamM`, `sigT`) takes Mathlib's decreasingly sorted `IsSymmetric.eigenvalues` of $S$ and $-T^2 = T^\top T$, reading top $n$ (`max (eigS j) 0`), bottom $n$ negated (`max (-eigS (N-1-j)) 0`), and even indices `2*j` (`√(max (eigT2 (2*j)) 0)`), returning `0` out of range. On the generic signature-$(n,n,N-2n)$ / rank-$2n$ locus of `question.md` (and whenever $\operatorname{rank} F = 2n$, by `LogDet.lists_pos` and `LogDet.pair_eq`), these match $\lambda_+, \lambda_-, \sigma(T)$ exactly; on degenerate forms they zero-pad.
  2. `Main.lean` (`OrthoBlocks.SpectralLists`) defines `lp, lm, sv : Fin n → ℝ` as antitone lists matching the filtered positive/negative `charpoly.roots` multisets of `Slin` and `-(Tlin ∘ₗ Tlin)` (with factor $2$ for `sv^2`). By `Weyl.roots_charpoly_eq_eigenvalues` and `Limit.lists_at_limit`, the two agree on `OrthoBlocks` when $|t_i| < 1$ and $2n \le N$.
- **Frobenius norms**: `GenProfile.frobL` and `frobT` are Gram-matrix formulas proved equal in `frobL_eq` and `frobT_eq` to $\sum_t \|L(b_t)\|^2$ and $\sum_t \|T(b_t)\|^2$ in any orthonormal basis $b$, matching `Main.nL` and `Main.pa`.
- **Profile $\pi(L) = (a,b,c,d)$**: Lean uses **three** separate definitions across files (contrary to §6 line 79; see Finding F11): `GenProfile` (`gA, gB, gC, gD`), `Main` (`pa, pb, pc, pd`), and the purely list-algebraic `Profile` (`profA, profB, profC, profD` on `α β : Fin n → ℝ`). They agree wherever their domains overlap (`Limit.gprof_at_limit`, `Main.lean:103–109, 118, 160`).
- **Tilts, $\alpha_i, \beta_i$, similar ordering, normal form**: `OrthoBlocks.t i = ⟪u i, v i⟫`, `α i = s i * (1 + t i) / 2`, `β i = s i * (1 - t i) / 2`, `SimilarlyOrdered α β := ∀ i j, 0 ≤ (α i - α j) * (β i - β j)`, and normal form `SimilarlyOrdered B.α B.β ∧ ((∀ i, 0 ≤ B.t i) ∨ (∀ i, B.t i ≤ 0))` match §2 word-for-word—**except** that `OrthoBlocks` does not build $|t_i| < 1$ into the structure (Finding F4). Note also that even if singular values $\sigma_i$ repeat, any two decompositions of $L$ on orthogonal planes yield the same multiset of pairs $\{(\sigma_i, t_i)\}$, so normal form is genuinely an invariant of the operator $L$.
- **Relation-(1) relative error (`gErr`)**: `GenProfile.gErr` is $\|\sigma(T) - \sqrt{\lambda_+\lambda_-}\|_2 / \|\sigma(T)\|_2$, matching §4 line 56 when $T \ne 0$, but silently evaluating to `0` via `x / 0 = 0` when $T = 0$ (Finding F3).
- **The ensemble and limits**: `qOf`, `kOf`, and `colVec` in `TheoremBFull.lean` match $Q+K = 2\mathrm{diag}(\sqrt{f(\rho)})P/\sqrt{N}$ and $K-Q = 2\mathrm{diag}(\sqrt{g(\rho)})M/\sqrt{N}$ exactly; limits use `Filter.Tendsto ... atTop (𝓝 ...)` almost surely (`∀ᵐ ω ∂μ`).

---

## 3. Findings: Claims Wrong or Unchecked as Stated

### F1. Theorem 2 sign condition on $\operatorname{supp}(\mu)$ vs. all of $\mathbb{R}$
- **Claim (§3, line 42):** *"Condition on $\rho$. ... If $f-g$ does not change sign on the support of $\mu$, then $L_\infty$ is in normal form, so relation (2) holds in the limit."*
- **Lean theorem:** `TheoremBExtra.lean`: `Odesky.limit_mem_Theta` (also cited in §6 line 90).
- **What differs:**
  1. `limit_mem_Theta` assumes `(hsign : (∀ y : ℝ, g y ≤ f y) ∨ (∀ y : ℝ, f y ≤ g y))`—that $f - g$ does not change sign **everywhere on $\mathbb{R}$**, with no mention of $\mu$ or `Measure.support`. For example, if $\mu = \mathrm{Uniform}([1,2])$, $f(y) = e^{2y}$, and $g(y) = e^y$, then $f, g : \mathbb{R} \to (0, \infty)$ are nondecreasing and $f - g > 0$ on $\operatorname{supp}(\mu) = [1,2]$, yet $f(-1) < g(-1)$ so `limit_mem_Theta` does not apply.
  2. In the prose quantifier order ("Condition on $\rho$ ..."), if $\rho \in \mathbb{R}^n$ is an arbitrary conditioned vector outside $\operatorname{supp}(\mu)^n$, $L_\infty$ need not be in normal form; the statement holds for $\mu^{\otimes n}$-almost every $\rho$ (since $\mathbb{P}(\rho_i \in \operatorname{supp}(\mu)) = 1$ on $\mathbb{R}$), a measure-theoretic step also absent from Lean.
- **Severity:** **the claim is unchecked as stated** (mathematically true for $\mu^{\otimes n}$-a.e. $\rho$, but Lean proves only the strictly narrower hypothesis of global sign constancy on $\mathbb{R}$; §6 line 90 also silently drops "on the support of $\mu$").

### F2. SVD bridge from $L = K^\top Q$ of rank $n$ to $L = U\Sigma V^\top$ in §1
- **Claim (§1, lines 11–15):** *"Let $L=K^\top Q$ have rank $n$. Write $L=U\Sigma V^\top$, where $\Sigma=\mathrm{diag}(\sigma_1,\dots,\sigma_n)$ holds the $n$ nonzero singular values $\sigma_1\ge\dots\ge\sigma_n>0$, and $U,V\in\mathbb R^{N\times n}$ have orthonormal columns $u_i$, $v_i$. ... For $N\ge2n$, the pair $(\Sigma,W)$ determines $L$ up to the congruence $L\mapsto OLO^\top$ ... Then exactly $a=\tfrac12(1-m_2-q),\ a-b=c+d-m_2-q$."*
- **Lean theorems:** `Congruence.lean`: `exists_isometry_of_same_W`, `gprof_eq_of_same_W`; `Identities.lean`: `gA_identity`, `gprof_sum_eq_one`, `gA_sub_gB_identity`.
- **What differs:** Lean never proves that a rank-$n$ operator `formL q k` admits an SVD `(σ, u, v)` with $\sigma_i > 0$ and orthonormal `u, v`, nor does it state a lemma that `formL q k = formL q' k'` implies `gA q k = gA q' k'` (etc.). Instead, `Congruence.lean` and `Identities.lean` take `(σ : Fin n → ℝ)` and orthonormal `(u v : Fin n → V)` directly as inputs and evaluate `gA, gB, gC, gD, gErr` only at the specific SVD row representation `q' = fun i => σ i • v i`, `k' = u`.
- **Severity:** **the claim is unchecked as stated** (the SVD existence and factorization-independence steps between a rank-$n$ head $L=K^\top Q$ and `gA (fun i => σ i • v i) u` are standard linear algebra, but unformalized in Lean).

### F3. Invariance/determination of "relation (1)" vs. `gErr` (and `0 / 0 = 0` when $T = 0$)
- **Claim (§1, line 13):** *"The profile and relations (1) and (2) are invariant under this congruence, so $(\Sigma,W)$ determines them."*
- **Lean theorems:** `Congruence.lean`: `gprof_isometry`, `gprof_eq_of_same_W` (§6 line 83).
- **What differs:** `gprof_isometry` and `gprof_eq_of_same_W` do not export equality of the spectral lists `lamP`, `lamM`, `sigT` or equivalence of indexwise relation (1) ($\forall j, \sigma(T)_j = \sqrt{\lambda_{+,j}\lambda_{-,j}}$); they export equality of `gA, gB, gC, gD` and the scalar `gErr`. In §1's general rank-$n$ setting, $T = 0$ is allowed: for $n=2, N=4$ and $L = e_1 e_1^\top - e_2 e_2^\top$ ($\sigma=(1,1)$, $u=(e_1,e_2)$, $v=(e_1,-e_2)$), `sigT = (0,0)` while `lamP = (1,0)` and `lamM = (1,0)`, so relation (1) **fails** ($\sigma(T)_1 = 0 \ne 1$), yet Lean computes `gErr = 1 / 0 = 0`. (Inside the proof of `gprof_isometry` at lines 192–197, local `have` steps `hP`, `hM`, `hT` *do* show `lamP`, `lamM`, `sigT` are invariant under `O`, so invariance of relation (1) is nearly proved, just not stated in the theorem signature; §6 line 83 accurately says `Congruence.lean` checks "the relation-(1) error" rather than relation (1) itself.)
- **Severity:** **the claim is unchecked as stated** for relation (1) in exported theorem statements (though the underlying `lamP`/`lamM`/`sigT` invariance is proved locally inside `Congruence.lean`).

### F4. Non-collinearity $|t_i| < 1$ in the definition of "sum of rank-one forms on orthogonal planes"
- **Claim (§2, line 22, Lemma 1 line 24, Theorem 1 lines 26–31):** *"A sum of rank-one forms on orthogonal planes is $L=\sum_i\sigma_iu_iv_i^\top$ with $\sigma_i>0$, unit vectors $u_i,v_i$, and the planes $\mathrm{span}(u_i,v_i)$ mutually orthogonal (so $W$ is diagonal). The summand $\sigma_iu_iv_i^\top$ is block $i$; its tilt $t_i=u_i^\top v_i$ (defined in §1) lies in $(-1,1)$."*
- **Lean theorems:** `Geometry.lean`: `OrthoBlocks`, `α_pos`, `β_pos`; `Spectral.lean`: `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg`; `Main.lean`: `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff`; `TheoremAExtra.lean`: `main_d_eq_zero_iff`, `main_c_eq_zero_iff`.
- **What differs:** Unit vectors $u_i, v_i$ satisfy $t_i \in [-1, 1]$; $t_i \in (-1, 1)$ holds only if "the planes $\mathrm{span}(u_i, v_i)$" is read as requiring each span to be 2-dimensional ($u_i \ne \pm v_i$). Lean's `structure OrthoBlocks` (`Geometry.lean:30`) does **not** include $|t_i| < 1$, so **every** theorem in `Spectral.lean`, `Main.lean`, and `TheoremAExtra.lean` adds `(hT : ∀ i, |B.t i| < 1)` (plus `[NeZero n]` and `(hN : 2 * n ≤ N)`) as explicit hypotheses. If $u_i = \pm v_i$ were permitted, "$t_i \in (-1,1)$" and Lemma 1 ($\alpha_i > 0, -\beta_i < 0$) would be false, and $L' = e_1 e_1^\top$ would have zero-padded profile $(0,0,1,0)$ (an endpoint of $\Theta$). (Note: once `∀ i, |B.t i| < 1` holds, `2 * n ≤ N` is mathematically automatic because `u_i + v_i` and `u_i - v_i` form $2n$ nonzero orthogonal vectors in $\mathbb{R}^N$.)
- **Severity:** **the claim is unchecked as stated** unless "planes" in line 22 is read as enforcing $\dim \mathrm{span}(u_i, v_i) = 2$ (and `[NeZero n]`, i.e. $n \ge 1$, is also unstated in Theorem 1, though standard for nonzero heads). If $u_i = \pm v_i$ is considered allowed by line 22's first sentence, then "$t_i \in (-1,1)$" and Lemma 1 are **wrong** at $|t_i| = 1$.

### F5. Correlated Gaussian special case in §3
- **Claim (§3, line 50 & §6, line 92):** *"$f,g$ constant, $f\ne g$: up to scale, the question's correlated Gaussian ensemble $K=rQ+\sqrt{1-r^2}\,G$, with $f/g=(1+r)/(1-r)$."* (§6: *"the question's correlated Gaussian ensemble is the case $f/g=(1+r)/(1-r)$ | `correlated_gaussian_law`"*.)
- **Lean theorem:** `SpecialCases.lean`: `Odesky.correlated_gaussian_law`.
- **What differs:**
  1. `correlated_gaussian_law` adds the hypothesis `(hr : |r| < 1)` (unstated in line 50, though forced by $f, g \in (0, \infty)$ since $f/g = (1+r)/(1-r) > 0 \iff |r| < 1$; line 50's $f \ne g$ also corresponds to $r \ne 0$).
  2. `correlated_gaussian_law` proves **only** a 1D scalar-pair measure identity: for $(X, Y) \sim \mathcal{N}(0,1) \otimes \mathcal{N}(0,1)$, the pushforward $(X + (rX + \sqrt{1-r^2}Y),\ (rX + \sqrt{1-r^2}Y) - X)$ is $\mathcal{N}(0, 2(1+r)) \otimes \mathcal{N}(0, 2(1-r))$. Lean does **not** prove the inverse bijection back to $(Q, K)$, the $n \times N$ i.i.d. matrix law, scale invariance $\pi(c L) = \pi(L)$ for $c > 0$ (needed to bridge the $1/\sqrt{N}$ scaling in §3 to unscaled $Q, G$), or $f/g = (1+r)/(1-r)$ and $c - d \to r|r|$.
- **Severity:** **the claim is unchecked as stated** (valid for $|r| < 1$, with several straightforward steps left unformalized; §6 line 92 overstates what `correlated_gaussian_law` proves).

### F6. Unformalized claim in §3 on determination by $(t, f+g)$ vs. $t$ alone
- **Claim (§3, line 52):** *"By the formula in Theorem 2, the position of $\pi(L_\infty)$ along $\Theta$ is determined by the joint law of $(t,f+g)$, but not by the law of $t$ alone."*
- **Lean theorem:** None.
- **What differs:** No Lean theorem covers either half of this statement—neither expressing the $n \to \infty$ limit in terms of the joint distribution of $(t(\rho), (f+g)(\rho))$, nor constructing two valid monotone pairs $(f_1, g_1), (f_2, g_2) : \mathbb{R} \to (0,\infty)$ with identical law of $t(\rho)$ and distinct limits along $\Theta$. (Also, in wording, it is the *$n \to \infty$ limit*—or the law—of $\pi(L_\infty)$, not the finite-$n$ random vector $\pi(L_\infty)$, that is determined by the joint law of $(t, f+g)$. The mathematical claim itself is true: e.g., for $\mu = \frac{1}{2}\delta_0 + \frac{1}{2}\delta_1$, setting $t(0)=0, t(1)=1/2$, $s(0)=1, s(1)=M \ge 2$ gives nondecreasing $f, g > 0$ with $c-d \to \frac{M^2/4}{1+M^2}$, which varies with $M$ while the law of $t$ stays fixed.)
- **Severity:** **the claim is unchecked as stated** (contradicting §6 line 79's *"Every theorem and identity in §1–§3 is checked in Lean"* and §7 line 100's claim that only §4's measurements and §7's fixed-ratio formula are unchecked).

---

## 4. Harmless Differences & §6 Inaccuracies

### F7. Quantifiers, conditioning on $\rho$, and split probability spaces in Theorem 2
- **Claim (§3, lines 39–44):** *"Fix $n$, a law $\mu$ on $\mathbb R$ ... Draw $\rho_1,\dots,\rho_n$ i.i.d. from $\mu$. ... **Theorem 2.** Condition on $\rho$. As $N\to\infty$ with $n$ fixed, almost surely $\pi(L)$ converges to $\pi(L_\infty)$ ... Hence $a-b\to0$, and relation (1) holds with equality in the limit. ... If also $\mathbb E[(f+g)(\rho)^2]<\infty$ for $\rho\sim\mu$, then, as $n\to\infty$, almost surely $c(L_\infty)-d(L_\infty)\to\dots$"*
- **Lean theorems:** `TheoremBFull.lean`: `theoremB_ae`; `TheoremBExtra.lean`: `similarlyOrdered_of_monotone`, `limit_a_eq_b`, `cd_eq_ratio`, `cd_limit_ae`; `Probability.lean`: `ratio_slln`.
- **What differs:**
  1. **Split probability spaces & conditioning:** Lean does not build a single joint probability space carrying both $\rho$ and $(P,M)$ or use conditional kernels. Instead, `theoremB_ae` takes fixed deterministic vectors `fv gv : Fin n → ℝ` (`0 < fv i`, `0 < gv i`, `[NeZero n]`) and an axiomatized sequence of pairwise-independent standard-Gaussian column vectors `Z : ℕ → Ω → Fin (n+n) → ℝ`, while `cd_limit_ae` works on a separate space with an infinite sequence `ρ : ℕ → Ω → ℝ` (indexing sample sizes as `Fin (n + 1)` so $n+1 \ge 1$; note prose line 39 initially fixed $n$ and conditioned on $\rho$ in line 42, leaving implicit the unconditioning and promotion of $\rho$ to an infinite i.i.d. sequence as $n \to \infty$).
  2. **Unchained easy steps:** `theoremB_ae` proves `gA → profA`, `gB → profB`, `gC → profC`, `gD → profD`, and `SimilarlyOrdered fv gv → (gErr → 0)`, while `TheoremBExtra` separately proves `similarlyOrdered_of_monotone` and `limit_a_eq_b` (`profA = profB`) without a wrapper explicitly stating `gA - gB → 0`. Also, relation (1) in the limit is stated via `gErr → 0` (individual limits `lamP j → fv (σ j)`, `lamM j → gv (τ j)`, `sigT j → √(fv (σ j) * gv (τ j))` are proved inside `profile_tendsto` at `TheoremBFull.lean:506–528`, with strictly positive denominator on line 532).
  3. **Extra redundant/weaker hypotheses in `cd_limit_ae`:** `cd_limit_ae` assumes `(hfm : Measurable f) (hgm : Measurable g)`, which is redundant since `Monotone` functions $\mathbb{R} \to \mathbb{R}$ are Borel measurable (`Monotone.measurable`); conversely, `cd_limit_ae` drops the sign condition on $f-g$, proving a more general result than *"If also..."*.
- **Severity:** **a harmless difference** (mathematically equivalent to conditioning on $\rho$ by independence $(P,M) \perp \rho$, aside from Finding F1).

### F8. Theorem 1(5) (`theta_attained`) proved for $(n, N) = (1, 2)$ only, and rank remark
- **Claim (§2, lines 31, 35):** *"5. Every point of $\Theta$ other than the two endpoints of $\Theta$ is $\pi(L')$ for some $L'$ in normal form."* Line 35: *"Even so, a form in normal form can have any rank $n\ge1$."*
- **Lean theorem:** `TheoremAExtra.lean`: `Odesky.theta_attained` (§6 line 88).
- **What differs:** `theta_attained` constructs `∃ B : OrthoBlocks 1 2, ...` ($n = 1, N = 2$). This literally satisfies existential *"for some $L'$ in normal form"* when $(n, N)$ is free to vary, as the proof sketch indicates (*"Equal tilts $t_i = t$ give the rank-one profiles"*), though it does not prove attainment at fixed arbitrary $(n, N)$ with $1 \le n \le N/2$. Also, no standalone Lean theorem checks line 35 (`LinearMap.rank B.Llin = n` and existence of normal-form `OrthoBlocks n (2*n)` for all $n \ge 1$).
- **Severity:** **a harmless difference** for Theorem 1(5) as phrased; line 35's rank remark is immediate from orthonormality of $u, v$ and $s_i > 0$ but unformalized as a theorem.

### F9. Log-determinant intermediate expression and mean over $i$
- **Claim (§1, line 16):** *"For every head with $\operatorname{rank}F=2n$, $\sum_i\log\sigma(T)_i=\tfrac12\sum_i\log(\lambda_{+,i}\lambda_{-,i})$, because both sides equal $\tfrac12\log\det G-n\log2$ ... So relation (1) holds exactly for the mean over $i$ of the log-ratios $r_i$."*
- **Lean theorems:** `LogDet.lean`: `logdet_identity`, `prod_sig_eq_det`, `prod_lam_eq_det` (plus `lists_pos`).
- **What differs:** Lean represents $\operatorname{rank} F = 2n$ as `LinearIndependent ℝ (stackRows q k)` with `2 * n ≤ N` (equivalent), proves the multiplicative identities $\prod_j \sigma(T)_j^2 = \det G / 4^n$ and $\prod_j \lambda_{+,j}\lambda_{-,j} = \det G / 4^n$, and deduces `logdet_identity` without writing a separate equality to $\frac{1}{2}\log\det G - n\log 2$ or dividing by $n$ for the mean (`[NeZero n]`). §6 line 85 accurately discloses the multiplicative intermediate form.
- **Severity:** **a harmless difference**.

### F10. Fixed-ratio bound in §7 (`Ratio.lean`)
- **Claim (§7, line 99):** *"for constant $f,g$, simulations agree with $1-2a\to(1+1/\kappa)(f-g)^2/\bigl((f+g)^2+(f-g)^2/\kappa\bigr)$, against $(f-g)^2/(f+g)^2$ for the iterated limit ... The two expressions differ by a relative amount of at most $1/\kappa$ ... Lean checks this bound as `fixed_ratio_bound` in `Ratio.lean`."*
- **Lean theorem:** `Ratio.lean`: `Odesky.fixed_ratio_bound`.
- **What differs:** `fixed_ratio_bound` assumes `(hκ : 1 ≤ κ) (hf : 0 < f) (hg : 0 < g)` and proves `x ≤ y ∧ y ≤ x * (1 + 1 / κ)` where `x := (f - g)^2 / (f + g)^2` is defined via `let` (not linked to `1 - 2 * profA`). Under the question's standing assumption $N \ge 2n$, $\kappa = N/n \ge 2 \ge 1$ (and $\kappa \in [12, 20]$ for the measured models; the numerical values $0.1579$ and $0.1111$ at $f=2, g=1, \kappa=2$ are also accurate).
- **Severity:** **a harmless difference**.

### F11. Inaccuracies in §6 (and lines 3, 100) about what Lean checks
1. **§6 line 79 (*"In these checks, Lean computes the profile from Mathlib's decreasingly sorted eigenvalues of $S$ and $T^\top T$ and from Frobenius norms"*):** **Inaccurate** for half the §6 table. Only `GenProfile.lean`-based files (`Congruence.lean`, `Identities.lean`, `LogDet.lean`, `Limit.lean`, and the finite-$N$ side of `TheoremBFull.lean`) use Mathlib's `IsSymmetric.eigenvalues`. All of Theorem 1 (`Main.lean`, `TheoremAExtra.lean`) instead uses characteristic-polynomial root multisets (`SpectralLists`) and `pa/pb/pc/pd`; and `TheoremBExtra.lean` (`limit_a_eq_b`, `limit_mem_Theta`, `cd_eq_ratio`, `cd_limit_ae`) plus `SpecialCases.lean` (`const_profile`) compute no eigenvalues or operator norms at all, operating directly on the algebraic formulas `profA/profB/profC/profD` (`Profile.lean`).
2. **Line 3, §6 line 79, and §7 line 100 (completeness of Lean coverage):** Overstated because Findings F1, F2, F5, and F6 are mathematical claims/steps in §1–§3 not checked in full by Lean (and §7 lines 96–98 also contain empirical claims beyond the two items listed in line 100).
3. **§6 line 83 (`exists_isometry_of_same_W`):** Proves `∃ O : V ≃ₗᵢ[ℝ] V, ∀ i, O (u i) = u' i ∧ O (v i) = v' i`; the operator-congruence equation $L'(Ox) = O(Lx)$ is `private lemma formL_map`, not exported. (Harmless.)
4. **§6 line 86 (Lemma 1):** Lists `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg` in `Spectral.lean`, omitting `roots_neg_T_sq_pos` (which actually filters the positive eigenvalues of $-T^2$ with multiplicity 2) and `Geometry.lean`'s `α_pos`, `β_pos` (which §2 line 33 cites). (Harmless.)
5. **§6 line 90 & line 92:** Line 90 omits *"on the support of $\mu$"* (masking Finding F1) and attributes $a - b \to 0$ to `limit_a_eq_b` (which proves $a(L_\infty) = b(L_\infty)$); line 92 overstates `correlated_gaussian_law` (Finding F5).

---

## 5. Summary of Claims That Match

Subject to the shared domain conventions noted above (`[NeZero n]` in §1–§3, `(hT : ∀ i, |B.t i| < 1)` and `(hN : 2 * n ≤ N)` in §2, and the SVD parameterization in §1):
- **§1 bullet 2 (`Identities.lean`: `gA_identity`, `gprof_sum_eq_one`, `gA_sub_gB_identity`):** Exact match for $a = \frac{1}{2}(1 - m_2 - q)$ and $a - b = c + d - m_2 - q$ (with implicit $n \ge 1, N \ge 2n$ from `question.md`).
- **§1 bullet 3 (`LogDet.lean`: `prod_lam_eq_det`, `prod_sig_eq_det`, `logdet_identity`):** Matches $\sum_j \log \sigma(T)_j = \frac{1}{2}\sum_j \log(\lambda_{+,j}\lambda_{-,j})$ for linearly independent stacked rows of $Q, K$ (up to F9).
- **§2 Lemma 1 (`Geometry.lean`, `Spectral.lean`):** Matches (generalized from 1 block to $n$ blocks under $|t_i| < 1$, $2n \le N$).
- **§2 Theorem 1(1)–(4) (`Main.lean`: `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff`; `TheoremAExtra.lean`: `main_d_eq_zero_iff`, `main_c_eq_zero_iff`):** Exact match on `OrthoBlocks` under `[NeZero n]`, `∀ i, |B.t i| < 1`, `2 * n ≤ N`, and `SpectralLists`.
- **§2 Theorem 1(5) (`TheoremAExtra.lean`: `theta_attained`):** Matches every non-endpoint of $\Theta$ via a rank-1 normal-form witness on $\mathbb{R}^2$ (F8).
- **§3 Theorem 2 ($N \to \infty$ profile & `gErr` convergence, similar ordering, and $n \to \infty$ limit of $c - d$):** Matches `theoremB_ae` (`TheoremBFull.lean`), `similarlyOrdered_of_monotone`, `limit_a_eq_b`, `cd_eq_ratio`, `cd_limit_ae` (`TheoremBExtra.lean`), and `ratio_slln` (`Probability.lean`) up to F7—with **only** the $\operatorname{supp}(\mu)$ sign clause (F1) unchecked as stated.
- **§3 Gaussian baseline midpoint (`SpecialCases.lean`: `const_profile`):** Matches $\pi(L_\infty) = (\frac{1}{2}, \frac{1}{2}, 0, 0)$ for constant $f = g = c > 0$ (`[NeZero n]`), with entrywise independence of $Q, K$ corresponding to $r = 0$ of `correlated_gaussian_law`.
- **§7 fixed-ratio bound (`Ratio.lean`: `fixed_ratio_bound`):** Matches relative bound $1/\kappa$ for $\kappa \ge 1, f > 0, g > 0$ (F10).
