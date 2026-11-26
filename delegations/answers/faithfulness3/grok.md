The Lean statements match the claims in §1, §2, §3, and the Lean-checked sentences in §7; I found no false claim and no claim that the cited theorems fail to reach.

The claim I checked hardest was Theorem 2: the ensemble formulas for \(Q\) and \(K\), the identification \(\alpha_i=f(\rho_i)\), \(\beta_i=g(\rho_i)\), and the limit of \(c-d\). They match. Row \(i\) of the answer’s \(Q\) and \(K\) is \(\sqrt{f_i}\,P_i/\sqrt{N}\mp\sqrt{g_i}\,M_i/\sqrt{N}\). That is `qOf` and `kOf` in `TheoremBFull.lean`. `blocks_of_limit_gram` (`TheoremB.lean`) states that rows with the limit Gram form an `OrthoBlocks` with \(\alpha_i=f_i\), \(\beta_i=g_i\), and \(|t_i|<1\). The tilt is then \(t_i=(f_i-g_i)/(f_i+g_i)\), from `α_add_β` and `α_sub_β` in `Geometry.lean`. `cd_eq_ratio` (`TheoremBExtra.lean`) states
\[
c-d=\frac{\sum_i(f-g)|f-g|(\rho_i)}{\sum_i(f+g)(\rho_i)^2},
\]
which is \(\sum_i w_i t_i|t_i|\) from Theorem 1(3). `cd_limit_ae` is the strong law for that ratio. `sigT` takes eigenvalue \(2j\) of \(T^\top T\), which is the singular value counted once; `lists_at_limit` and `prod_sig_eq_det` use that pairing.

## §1

These match the text.

- Rank-\(n\) forms have an SVD presentation `formL (σ•v) u`, and the profile, `lamP`, `lamM`, `sigT`, and `gErr` depend only on the operator: `exists_svd_rows`, `gprof_of_formL_eq` (`Bridge.lean`). `formL` is \(Lx=\sum_i\langle q_i,x\rangle k_i\), i.e. \(L=K^\top Q\).
- The same \((\Sigma,W)\), with \(W_{ij}=\langle u_i,v_j\rangle\), gives an orthogonal conjugation \(L\mapsto OLO^\top\), and the profile, spectral lists, and relation-(1) error are invariant: `exists_isometry_of_same_W`, `formL_isometry`, `gprof_isometry`, `gprof_eq_of_same_W`, `lists_isometry`.
- \(a=\tfrac12(1-m_2-q)\) and \(a-b=c+d-m_2-q\), with \(m_2\) and \(q\) as written in the answer: `gA_identity`, `gprof_sum_eq_one`, `gA_sub_gB_identity` (`Identities.lean`). `gA`, `gB`, `gC`, `gD` are \(\|T\|^2/\|L\|^2\), \(2\langle\lambda_+,\lambda_-\rangle/\|L\|^2\), and the two squared positive-part norms. `lamP` and `lamM` are the decreasing positive eigenvalues of \(S\) and the decreasing absolute values of the negative ones.
- For linearly independent stacked rows (rank \(F=2n\)) and \(2n\le N\), \(\prod\sigma(T)_i^2=\prod\lambda_{+,i}\lambda_{-,i}=\det G/4^n\), so the log-ratios sum to zero, and equal log-ratios are zero: `prod_sig_eq_det`, `prod_lam_eq_det`, `logdet_identity`, `logratio_sum_zero`, `eq_zero_of_sum_zero_of_const`. `gramRows` is the Gram matrix of the rows of \(Q\) followed by the rows of \(K\).

## §2

`SimilarlyOrdered`, `OrthoBlocks`, \(\alpha_i=s_i(1+t_i)/2\), and \(\beta_i=s_i(1-t_i)/2\) are the answer’s definitions. Orthogonal planes are the off-diagonal vanishings `uu`, `uv`, `vv`. \(|t_i|<1\) is \(u_i\neq\pm v_i\).

- Lemma 1 matches. `S_add`, `S_sub`, `neg_T_sq_add`, and `neg_T_sq_sub` (`Geometry.lean`) are the block eigenvector equations, and `α_pos`, `β_pos` give \(\alpha_i>0\), \(\beta_i>0\). `charpoly_S` and `charpoly_neg_T_sq` (`Spectral.lean`) say the spectrum of \(S\) is \(\{\alpha_i,-\beta_i\}\) plus zeros, and the nonzero spectrum of \(T^\top T\) is \(\alpha_i\beta_i\) twice each.
- Theorem 1(1)–(4) match `main_a_le_b`, `main_a_eq_b_iff`, `main_relation_one`, `main_c_sub_d`, `main_d_eq_zero_iff`, `main_c_eq_zero_iff`, and `main_mem_Theta_iff`. The profile coordinates `pa`, `pb`, `pc`, `pd` are the answer’s \(a,b,c,d\), using decreasing spectral lists (`SpectralLists`). Relation (1) is \(\mathrm{sv}_k=\sqrt{\mathrm{lp}_k\mathrm{lm}_k}\) at every \(k\). Membership in \(\Theta\) is \(a=b\) and \(cd=0\). Normal form is similar ordering and one sign of the tilts. The hypotheses \(n\ge1\), \(|t_i|<1\), and \(2n\le N\) are the answer’s class ( \(n\) mutually orthogonal 2-planes).
- Theorem 1(5) matches `theta_attained`: every \((a,a,c,d)\) with \(a>0\), \(c,d\ge0\), \(cd=0\), and \(2a+c+d=1\) is the profile of one block in \(\mathbb R^2\) in normal form. Those conditions are the points of \(\Theta\) other than \((0,0,1,0)\) and \((0,0,0,1)\).

## §3

- `theoremB_ae` is the conditional statement: for fixed \(f(\rho_i)>0\) and \(g(\rho_i)>0\), i.i.d. standard Gaussian columns, almost surely \((a,b,c,d)\) converges to `profA`, `profB`, `profC`, `profD` of those values, and if the lists are similarly ordered then the relation-(1) relative error `gErr` converges to \(0\). `gErr` is \(\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|/\|\sigma(T)\|\).
- Similar ordering for nondecreasing \(f,g\), hence \(a=b\) for the limit profile and \(a-b\to0\), matches `similarlyOrdered_of_monotone` and `limit_a_eq_b`. `Monotone` is nondecreasing, not strictly increasing.
- If \(f-g\) does not change sign on \(\mathbb R\), the limit profile lies on \(\Theta\): `limit_mem_Theta`. With Theorem 1(4) and \(\alpha=f\), \(\beta=g\), that is normal form, so relation (2) holds for the limit.
- The \(n\to\infty\) limit of \(c(L_\infty)-d(L_\infty)\) matches `cd_eq_ratio` and `cd_limit_ae`, under i.i.d. \(\rho\) and \(\mathbb E[(f+g)(\rho)^2]<\infty\). Integrability of the numerator is derived in the proof from that hypothesis. The index shift `Fin (n+1)` does not change the limit.
- The Gaussian baseline: constant \(f=g=c>0\) has profile \((\tfrac12,\tfrac12,0,0)\) for every \(n\ge1\), by `const_profile`. Composed with `theoremB_ae`, the \(N\to\infty\) limit is that point.
- `correlated_gaussian_law` states that one entry of \((Q+K,\,K-Q)\) in the question’s model, for \(|r|<1\), has the law of independent centered Gaussians of variances \(2(1+r)\) and \(2(1-r)\). `gaussianReal 0 v` is that variance: the characteristic function in the file is \(\exp(itm-vt^2/2)\).

## §7

- Theorem 2 is an \(N\to\infty\) limit at fixed \(n\). `theoremB_ae` has \(n\) fixed. The fixed-ratio regime is not that theorem.
- `const_one_sub_two_a` states that the constant limit form has \(1-2a=(f-g)^2/(f+g)^2\). That is the answer’s \(x\).
- `fixed_ratio_bound` states \(x\le y\le x(1+1/\kappa)\) for the two closed forms, for \(\kappa\ge1\) and \(f,g>0\). For \(f\neq g\) this is a relative gap \((y-x)/x\le1/\kappa\). For \(f=g\) it forces \(y=0\). The answer’s sentence that Lean checks this bound, and checks \(x\), and does not check the fixed-ratio formula as a limit, matches these statements.
- The last bullet is accurate: the §4 table, the other-model medians, the LayerNorm percentages, the finite-\(N\) fits, and the fixed-ratio formula as a description of \(1-2a\) are not Lean theorems.

## Harmless differences

- Exported existence of \(L_\infty\). `theoremB_ae` states convergence of the four coordinates to `prof*`. `blocks_of_limit_gram` and `gprof_at_limit` identify `prof*` with the profile of an `OrthoBlocks` with \(\alpha_i=f_i\), \(\beta_i=g_i\), given rows whose Gram is already the limit Gram. A witness for those rows is built inside the proof of `profile_tendsto` (`limit_config`, private) and is not a separate exported existence theorem. The profile convergence the answer states is fully exported; the sentence “where \(L_\infty\) is a sum of rank-one forms…” uses that conditional identification. This does not change the coordinates of the limit.
- `weighted_tilt` is the pointwise identity \((f+g)^2\,t|t|=(f-g)|f-g|\). The answer’s reading of the ratio of expectations as the \((f+g)^2\)-weighted mean of \(t|t|\) is that identity under the integrability hypothesis of `cd_limit_ae`. There is no separate theorem about the integrals.
- The choice \(f=(1+r)/2\), \(g=(1-r)/2\) is not inside `correlated_gaussian_law`. It is the arithmetic \(4\cdot(1\pm r)/2=2(1\pm r)\), which links that theorem to one entry of \(\sqrt N\,(Q+K,\,K-Q)\) in the ensemble. The §6 row states only the variance law, and that row matches the theorem.
- `cd_limit_ae` and `logdet_identity` take measurability of \(f\), \(g\), and \(\rho\) as hypotheses. A nondecreasing function \(\mathbb R\to\mathbb R\) is Borel, so this does not shrink the class in the answer. Pairwise independence in the strong laws is weaker than the answer’s i.i.d. assumption.
- `gA_sub_gB_identity` assumes \(2n\le N\). The identity bullet in §1 does not repeat it. The question’s standing hypothesis \(n\le N/2\), and the previous bullet, supply it. `gA_identity` has no such hypothesis.
- The §6 line for Lemma 1 names the characteristic-polynomial theorems and `α_pos`, `β_pos`. The per-block eigenvector equations are `S_add`, `S_sub`, `neg_T_sq_add`, and `neg_T_sq_sub` in the same `Geometry.lean` file the table cites. The lemma is checked.
- In the parenthetical on models, \(1/\kappa\) for \(\kappa=12\) is \(8.3\%\), and the answer writes \(5\)–\(8\%\). That parenthetical is not a Lean claim.

## What no Lean theorem covers

The answer already says so, and it is accurate: the medians in §4 and in the first three §7 bullets, and the fixed-ratio expression as the limit of \(1-2a\) at \(N=\kappa n\). The decimals \(0.1111\) and \(0.1579\) are \(x\) and \(y\) at \(f=2\), \(g=1\), \(\kappa=2\); Lean does not evaluate them. The measured \(0.1598\) is not a theorem.

I did not re-run the build or `#print axioms`. The comparison above is of statements and definitions. The §6 description of how the profile is computed (decreasing Mathlib eigenvalues, or decreasing enumerations of characteristic-polynomial roots, identified by `roots_charpoly_eq_eigenvalues`) matches `GenProfile.lean`, `SpectralLists`, and `Weyl.lean`.
