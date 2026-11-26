Theorem 1 and the \(N\to\infty\) profile convergence match the cited Lean statements; the support-only sign hypothesis for relation (2), the matrix reading of the correlated Gaussian, and §5’s unconditional convergence to a normal form do not.

I compared the claims in §1, §2, §3 and §7 of `answer_draft.md`, and the §6 table, with the Lean statements and the definitions they use. I did not recompile the project.

## What matches

The three §1 calculations match the theorems named in §6.

- Orthogonal congruence: `exists_isometry_of_same_W`, `gprof_isometry` and `gprof_eq_of_same_W` in `Congruence.lean`. Same singular values and the same cosine matrix \(W_{ij}=\langle u_i,v_j\rangle\), for orthonormal frames, give a linear isometry \(O\) with \(L'=OLO^\top\), and the same \((a,b,c,d)\) and the same relation-(1) error `gErr`. The prose adds \(N\ge 2n\); the theorems do not need it.
- The identities \(a=\tfrac12(1-m_2-q)\) and \(a-b=c+d-m_2-q\): `gA_identity` and `gA_sub_gB_identity` in `Identities.lean`. `m2` and `qrec` are the sums in the answer. The second identity uses \(2n\le N\), which is the question’s \(n\le N/2\).
- The log-determinant identity: `logdet_identity`, `prod_lam_eq_det` and `prod_sig_eq_det` in `LogDet.lean`. Under \(2n\le N\) and linear independence of the \(2n\) stacked rows (the answer’s \(\operatorname{rank} F=2n\)), \(\prod_j\sigma(T)_j^2=\prod_j\lambda_{+,j}\lambda_{-,j}=\det G/4^n\), and therefore \(\sum_j\log\sigma(T)_j=\tfrac12\sum_j\log(\lambda_{+,j}\lambda_{-,j})\). The prose form “both sides equal \(\tfrac12\log\det G-n\log 2\)” is that product identity plus \(\log(4^n)=2n\log 2\). `sigT` takes the even indices of the decreasing eigenvalues of \(T^\top T\); `pair_eq` shows those eigenvalues come in equal pairs, so this is the singular-value list counted once. The mean of the log-ratios \(r_i\) is then zero because the sum of the \(r_i\) is zero.

Lemma 1 and Theorem 1 match.

- Lemma 1: `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos` and `roots_S_neg` in `Spectral.lean`, together with the block eigenvector equations in `Geometry.lean`. For an `OrthoBlocks` with \(|t_i|<1\) and \(2n\le N\), the eigenvalues of \(S\) are the \(\alpha_i>0\), the \(-\beta_i<0\), and zeros, and the nonzero eigenvalues of \(T^\top T\) are the \(\alpha_i\beta_i\), each twice.
- Theorem 1(1)–(4): `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_d_eq_zero_iff`, `main_c_eq_zero_iff`, `main_mem_Theta_iff`. The profile \((p_a,p_b,p_c,p_d)\) is \(\|T\|^2/\|L\|^2\), \(2\langle\lambda_+,\lambda_-\rangle/\|L\|^2\), and the two squared positive-part norms, with \(\lambda_\pm\) the decreasing charpoly roots. `SimilarlyOrdered` is \((\alpha_i-\alpha_j)(\beta_i-\beta_j)\ge 0\). Normal form is that condition plus all tilts \(\ge 0\) or all tilts \(\le 0\). The right-hand side of (3) is \(\sum_i(s_i^2/\|L\|^2)\,t_i|t_i|\), and \(\|L\|^2=\sum_i s_i^2\).
- Theorem 1(5): `theta_attained` in `TheoremAExtra.lean`. Every \((a,a,c,d)\) with \(a>0\), \(c,d\ge 0\), \(cd=0\) and \(2a+c+d=1\) is the profile of a one-block normal form in \(\mathbb R^2\). Those numerical hypotheses are exactly the points of \(\Theta\) other than \((0,0,1,0)\) and \((0,0,0,1)\).

Theorem 2’s \(N\to\infty\) statement matches, including the part I checked hardest (below). `theoremB_ae` in `TheoremBFull.lean` fixes \(f(\rho_i)\) and \(g(\rho_i)\) as positive constants and lets the Gaussian matrix vary. That is the answer’s “condition on \(\rho\)”. The rows
\[
q_i=\sqrt{f_i}\,x_i-\sqrt{g_i}\,x_{n+i},\qquad
k_i=\sqrt{f_i}\,x_i+\sqrt{g_i}\,x_{n+i}
\]
are the answer’s \(Q+K=2\operatorname{diag}(\sqrt f)\,P/\sqrt N\) and \(K-Q=2\operatorname{diag}(\sqrt g)\,M/\sqrt N\). Almost surely, \((a,b,c,d)\) tends to the block profile of \((\alpha,\beta)=(f(\rho),g(\rho))\), and if those lists are similarly ordered then `gErr` tends to \(0\). `blocks_of_limit_gram` realises that profile as an orthogonal-plane sum with those \(\alpha_i,\beta_i\) and with tilt \((f_i-g_i)/(f_i+g_i)\). `similarlyOrdered_of_monotone` is the monotonicity claim. The \(n\to\infty\) limit of \(c-d\) is `cd_eq_ratio` plus `cd_limit_ae`: the ratio of expectations in the display, for an i.i.d. sequence, under \(\mathbb E[(f+g)(\rho)^2]<\infty\). Lean derives integrability of the numerator from that hypothesis. The same limit does not need the sign hypothesis that the answer places in the preceding sentence.

The constant case \(f=g=c>0\) has abstract profile \((\tfrac12,\tfrac12,0,0)\) by `const_profile`. With `theoremB_ae`, that is the Gaussian baseline’s limit profile.

The §7 bound matches `fixed_ratio_bound` in `Ratio.lean`: for \(\kappa\ge 1\) and \(f,g>0\), if \(x=(f-g)^2/(f+g)^2\) and \(y\) is the displayed fixed-ratio expression, then \(x\le y\le x(1+1/\kappa)\), so \((y-x)/x\le 1/\kappa\) whenever \(x>0\). The answer is right that Lean checks this comparison and does not check the fixed-ratio formula, the simulation numbers, or the measurements in §4. The one use of a theorem in §4, the contrapositive of Theorem 1(1), matches `main_a_le_b`.

## Findings

### 1. Sign hypothesis for relation (2) in the limit — unchecked as stated

Claim, Theorem 2 (§3): “If \(f-g\) does not change sign on the support of \(\mu\), then \(L_\infty\) is in normal form, so relation (2) holds in the limit.”

Lean: `limit_mem_Theta` in `TheoremBExtra.lean`. The hypothesis is
\[
(\forall y,\; g(y)\le f(y))\lor(\forall y,\; f(y)\le g(y)),
\]
a condition at every real, not only on the support of \(\mu\). The conclusion is \(a=b\) and \(cd=0\) for the abstract profile of the sample \((f(x_i),g(x_i))\).

What differs: the answer’s hypothesis is weaker than the theorem’s. If \(\mu\) is supported on \([0,\infty)\), \(f(y)=e^y\) and \(g=1\), then \(f-g\ge 0\) on the support, so every realised block has tilt \(\ge 0\) and \(L_\infty\) is in normal form, but \(f-g\) is negative on \((-\infty,0)\) and `limit_mem_Theta` does not apply. No theorem assumes the inequality only on a set of full measure, or only at the sampled \(\rho_i\).

Seriousness: the claim is unchecked as stated. The global-sign case is checked.

### 2. §5 says every such ensemble lands on a normal form — the claim is wrong

Claim, §5: “For the Gaussian ensemble of §3, the profile of \(L\) converges to the profile of a form in normal form as the embedding dimension \(N\) grows (Theorem 2).”

Lean: `theoremB_ae` gives convergence to the block profile of \(\alpha_i=f(\rho_i)\), \(\beta_i=g(\rho_i)\) for every positive \(f(\rho),g(\rho)\). `main_mem_Theta_iff` puts that profile on \(\Theta\) only when the blocks are similarly ordered and the tilts share a sign. `limit_mem_Theta` adds the global sign hypothesis. The ensemble in §3 is any nondecreasing \(f,g:\mathbb R\to(0,\infty)\).

What differs: \(f(y)=e^y\) and \(g=1\) are in the ensemble. They are similarly ordered, but for \(\rho=(-1,1)\) the tilts have opposite signs, so both \(c\) and \(d\) are positive. The limit profile is not the profile of a normal form. Theorem 2 in §3 states the sign restriction; §5 drops it and still cites Theorem 2. The opening sentence, “a natural Gaussian ensemble whose profiles converge to that class”, is true if read as existence (take \(f-g\) of one sign). §5 is a statement about the whole ensemble of §3.

Seriousness: the claim is wrong.

### 3. Correlated Gaussian ensemble — unchecked as stated

Claim, §3: “\(f,g\) constant, \(f\neq g\): up to scale, the question’s correlated Gaussian ensemble \(K=rQ+\sqrt{1-r^2}G\), with \(f/g=(1+r)/(1-r)\).” The §6 row says `correlated_gaussian_law` checks this.

Lean: `correlated_gaussian_law` in `SpecialCases.lean` is a statement about one pair of real random variables. For \(|r|<1\) and \(X,Y\) independent standard normal, with \(K=rX+\sqrt{1-r^2}Y\), the law of \((X+K,\,K-X)\) is the product of centered normals of variances \(2(1+r)\) and \(2(1-r)\). The theorem does not mention \(f\), \(g\), matrices, or profiles.

What differs: the file comment, not the theorem, sets \(f=(1+r)/2\) and \(g=(1-r)/2\). Those variances equal \(4f\) and \(4g\), so the ratio \(f/g\) is right, and “up to scale” is the right relation between one entry of the question’s model and one entry of the ensemble. Nothing in Lean says the \(n\times N\) ensembles are equal up to scale, or that their profiles agree. The answer also does not record \(|r|<1\), which the theorem assumes; that restriction is the natural domain of the question’s formula.

Seriousness: the claim is unchecked as stated. The scalar variance computation is the right core, and the ratio is one arithmetic step from it.

### 4. Two §3 remarks that no theorem states

Claim: “in the ensemble, each head is a sum of \(n\) independent blocks.”

At finite \(N\), \(L\) is not a sum of rank-one forms on orthogonal planes. `blocks_of_limit_gram` is the exact orthogonal decomposition of the Gram limit, and `theoremB_ae` is convergence to its profile. The next sentence correctly says the row norms are only close to \(4f(\rho_i)\) and \(4g(\rho_i)\).

Seriousness: read literally, the claim is wrong. It is a gloss, and the limit statement next to it is checked.

Claim: “the position of \(\pi(L_\infty)\) along \(\Theta\) is determined by the joint law of \((t,f+g)\), but not by the law of \(t\) alone.”

`cd_limit_ae` is the ratio \(\mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]\). With \(t=(f-g)/(f+g)\) from `blocks_of_limit_gram`, that ratio is the \((f+g)^2\)-weighted mean of \(t|t|\). No theorem says this quantity is not a function of the law of \(t\) alone.

Seriousness: unchecked as stated. The underlying limit formula is checked, and the weighted-mean reading is the same formula. Low seriousness.

The sentence “only the spread of the \(r_i\) can show relation (1) failing” (§1) is the same sort of remark. The sum of the \(r_i\) is `logdet_identity`. Low seriousness.

## §6

These table rows and the paragraph above the table overstate what is packaged as a theorem.

- “Every theorem and identity in §1–§3 is checked … with no unproved steps.” Findings 1 and 3 are steps the named theorems do not take. Finding 2 is a later summary, not a §1–§3 identity.
- “Lean computes the profile from Mathlib’s decreasingly sorted eigenvalues.” That is `eigS` and `eigT2` in `GenProfile.lean`, used for §1 and for `theoremB_ae`. Theorem 1’s profile is any decreasing list whose multiset equals the characteristic-polynomial roots (`SpectralLists` in `Main.lean`). `roots_charpoly_eq_eigenvalues` in `Weyl.lean` identifies the two, and `lists_at_limit` uses that identification for the limit configuration. Harmless difference in packaging.
- The row “\(a-b\to 0\)” is attributed to `limit_a_eq_b`. That theorem is \(a=b\) for the limit profile. Convergence of \(a_N-b_N\) to \(0\) is that equality plus the two limits in `theoremB_ae`. The previous row supplies those limits. Harmless, if the two rows are read together.
- The row for `correlated_gaussian_law` says the theorem checks that the question’s ensemble is the case \(f/g=(1+r)/(1-r)\). The theorem checks the scalar law in finding 3. This row is inaccurate.
- `const_profile` checks the four coordinates of the constant profile. It does not, by itself, mention the Gaussian ensemble. Together with `theoremB_ae` it matches the baseline sentence. Harmless omission in the citation.

The other §6 rows match the theorem statements, with the domain gap of finding 1 living in the §3 wording (“on the support of \(\mu\)”) rather than in the §6 paraphrase (“when \(f-g\) does not change sign”).

## Claim checked hardest

Theorem 2’s sentence “almost surely \(\pi(L)\) converges to \(\pi(L_\infty)\), where \(L_\infty\) is a sum of rank-one forms on orthogonal planes with \(\alpha_i=f(\rho_i)\) and \(\beta_i=g(\rho_i)\).”

`theoremB_ae` concludes that the general profile `(gA,gB,gC,gD)`, built from Mathlib’s decreasing eigenvalues and from the Gram formulas for the Frobenius norms, converges to `(profA,profB,profC,profD)` of the lists \(f(\rho),g(\rho)\). It does not mention an operator \(L_\infty\). The identification is `blocks_of_limit_gram` (those lists are \(\alpha,\beta\) of an `OrthoBlocks`, with \(Lx=\sum_i\langle q_i,x\rangle k_i\)) together with `gprof_at_limit` (at that Gram, the general profile equals the abstract profile, and `gErr` is \(0\) when the lists are similarly ordered) and `Main.lean` (the abstract profile is the operator profile \(p_a,p_b,p_c,p_d\)). The quantifiers match: \(n\) fixed, \(N\to\infty\), \(\rho\) frozen, almost sure over the Gaussian columns. I do not see an unformalized mathematical step in that chain. The sign restriction in finding 1 is a separate sentence of Theorem 2.
