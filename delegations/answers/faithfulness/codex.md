NEGATIVE: the main formalized results substantially match their stated domains, but the answer contains a false unrestricted characterization and overstates complete Lean coverage.

I read the supplied answer, question, and the statements and definitions in all 21 project files. Answer line numbers below refer to [answer_draft.md](/Users/andrew/maisi/questions/2026-11-20-odesky/answer_draft.md); Lean paths are relative to `/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/`. I also queried `#print axioms` for all 30 declarations named in the §6 table and §7 bound, using the existing compiled project without rebuilding it. Each reported exactly `propext`, `Classical.choice`, and `Quot.sound`. I did not edit the supplied files or verify the empirical measurements.

1. **The unrestricted characterization following Theorem 1 is false.**

   **Claim:** answer line 35: “the forms that ‘behave like rank-one forms’ … are exactly the forms in normal form.”

   **Lean:** `Odesky.OrthoBlocks.main_mem_Theta_iff`, [Main.lean:153](/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/Main.lean:153). Its input already includes `B : OrthoBlocks n N`. It characterizes membership in Θ **within that class**. It does not infer an orthogonal-plane decomposition from membership in Θ, or even from both relations together.

   This is more than an absent formal proof. Take

   \[
   Q=\begin{pmatrix}0&1&0&1\\0&0&1&0\end{pmatrix},\qquad
   K=\begin{pmatrix}1&0&0&0\\0&1&0&0\end{pmatrix},\qquad
   L=K^\top Q=\begin{pmatrix}
   0&1&0&1\\0&0&1&0\\0&0&0&0\\0&0&0&0
   \end{pmatrix}.
   \]

   Here `rank L = 2`, `N = 4`, and the four stacked rows of Q and K are linearly independent. Put
   \(p=(\sqrt5+1)/4\), \(q=(\sqrt5-1)/4\).
   The eigenvalues of S are \(p,q,-q,-p\), and the singular values of T are \(p,p,q,q\). Thus both sorted lists \(\lambda_+\) and \(\lambda_-\), and the once-counted singular list, equal \((p,q)\). Also \(\|L\|_F^2=3\) and \(\|T\|_F^2=3/2\). Consequently relation (1) is exact and
   \(\pi(L)=(1/2,1/2,0,0)\in\Theta\).

   Nevertheless \(L^3=0\) and \(L^2\ne0\). In an orthogonal-plane decomposition, each \(u_i\) is an eigenvector of L with eigenvalue \(\sigma_i t_i\). Nilpotence forces all \(t_i=0\), which forces \(L^2=0\). Therefore this L has no such decomposition. I checked the matrix calculations with exact integer arithmetic: the characteristic polynomials of `2S` and `2T` are respectively \(z^4-3z^2+1\) and \(z^4+3z^2+1\).

   **Severity: the claim is wrong as an unrestricted characterization.** The numbered Theorem 1(4), which explicitly retains the orthogonal-plane premise, is not contradicted. Restrict line 35 to “among sums of rank-one forms on orthogonal planes.”

2. **The support-only sign hypothesis is weaker than the cited Lean hypothesis. The summary also omits the sign hypothesis entirely.**

   **Claim:** answer line 42: “If \(f-g\) does not change sign on the support of \(\mu\), then \(L_\infty\) is in normal form.” The §6 row at line 90 attributes this consequence to `limit_mem_Theta`.

   **Lean:** `Odesky.limit_mem_Theta`, [TheoremBExtra.lean:35](/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/TheoremBExtra.lean:35), assumes

   ```lean
   hsign : (∀ y, g y ≤ f y) ∨ (∀ y, f y ≤ g y)
   ```

   Here `y : ℝ`; there is no support restriction, latent law, or almost-everywhere qualifier. For example, let `(f(y),g(y))` be `(1,2)` for `y < 1/2` and `(4,3)` otherwise. Both functions are positive and nondecreasing. With \(\mu=\delta_0\), the answer's support hypothesis holds, but neither disjunct of Lean's `hsign` holds.

   The support-only conclusion is mathematically valid almost surely: sampled latent values lie in the support almost surely, and `Profile.mem_Theta_iff` can then use the signs of the sampled blocks. The supplied project does not perform that support-to-sample transfer. The cited `limit_mem_Theta` alone does not check the advertised weaker hypothesis.

   **Severity: the claim is unchecked as stated by its cited theorem; this is a coverage gap, not a counterexample to the intended almost-sure mathematical statement.**

   Separately, answer line 75 says that the ensemble of §3 converges to the profile of a form in normal form without retaining any sign condition. This is false. Use the same f and g with \(\mu=(\delta_0+\delta_1)/2\), and take `n = 2`. With probability `1/2`, one sampled latent value is 0 and the other is 1. The block pairs are then `(1,2)` and `(4,3)`, and the limit profile is
   \[
   (a,b,c,d)=(14/29,14/29,1/58,1/58),
   \]
   which is outside Θ. **Severity for the unconditional summary: the claim is wrong.**

3. **The almost-sure limit in n uses a coupling that the answer leaves implicit.**

   **Claim:** answer lines 39 and 42–43 first draw `n` latent variables, then claim an almost-sure limit as `n → ∞`.

   **Lean:** `Odesky.cd_limit_ae`, [TheoremBExtra.lean:65](/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/TheoremBExtra.lean:65), takes one sequence `ρ : ℕ → Ω → ℝ`. Its nth expression uses the first `n + 1` entries of that same sequence. `Probability.ratio_slln` uses the same prefix convention.

   The answer explicitly specifies the common infinite Gaussian arrays for the limit in N, but does not similarly specify one infinite latent sequence for the limit in n. Fixed-n marginal sampling prescriptions alone do not specify an almost-sure sequence limit. The checked assertion is the natural nested-prefix interpretation, not an assertion about arbitrary ways of coupling or resampling heads at different n.

   **Severity: unchecked as a claim without a specified coupling; harmless after explicitly adopting one infinite i.i.d. latent sequence.** The latter almost-sure statement is over the latent sequence. The first, conditioned fixed-n statement is over the Gaussian arrays. These are distinct probability assertions in the code.

4. **The statement about a joint law determining the position needs an additional limit and the sign restriction.**

   **Claim:** answer line 52: “the position of \(\pi(L_\infty)\) along Θ is determined by the joint law of \((t,f+g)\), but not by the law of t alone.”

   **Lean:** the closest results are `cd_eq_ratio` and `cd_limit_ae` in `TheoremBExtra.lean:52,65`. No theorem states the quoted assertion.

   For fixed n, \(L_\infty\) still depends on the sampled latent values. Their joint law determines the distribution of its profile, not its realized position. For example, with equal probabilities on 0 and 1, let f take values 1 and 3, and let g be constantly 1. For `n = 1`, the two possible limit profiles are `(1/2,1/2,0,0)` and `(3/8,3/8,1/4,0)`. Both arise from the same law. Also, without the sign condition, the profile need not lie on Θ at all, as finding 2 shows.

   With the moment and common-sign assumptions and the further `n → ∞` limit, the intended assertion follows from the displayed expectation ratio. The assertion that the tilt law alone is insufficient is true in general, but the project does not formalize a comparison of two laws demonstrating it. For example, equally likely tilts 0 and `1/2`, with strengths `f+g` respectively `(2,4)` or `(2,8)`, give limiting `c-d` equal to `1/5` or `4/17`. Both examples admit positive nondecreasing f and g and have `f ≥ g`.

   **Severity: unchecked as stated, and false if read as determining the fixed-n realized profile.** The corrected large-n interpretation is consistent with `cd_limit_ae`.

5. **The proof sketch calls the Frobenius norms polynomials, but Lean proves this for their squares.**

   **Claim:** answer line 46: “The Frobenius norms of L and T are polynomials in the Gram matrix.”

   **Lean:** `frobL` and `frobT`, [GenProfile.lean:114](/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/GenProfile.lean:114), denote **squared** Frobenius norms. `frobL_eq` and `frobT_eq` identify them with sums of squared norms on an orthonormal basis. In `TheoremBFull.lean:406–428`, `PhiL`, `PhiT`, `frobL_eq_Phi`, `frobT_eq_Phi`, `PhiL_cont`, and `PhiT_cont` concern those squares.

   The literal prose claim is false. Already for one block with `f = g = 1` and Gram matrix \(\begin{pmatrix}1&r\\r&1\end{pmatrix}\), the norm of L is \(2\sqrt{1-r^2}\), whereas its square is polynomial in r.

   **Severity: the claim is wrong, but this is a minor wording error.** Replace “Frobenius norms” by “squared Frobenius norms.” The formal convergence argument uses the correct quantities.

6. **The special-case law theorem checks a scalar transformation, not the whole matrix-ensemble identification.**

   **Claims:** answer lines 49–50 and §6 line 92 identify the constant-f,g ensemble with independent or correlated Gaussian matrices.

   **Lean:** `Odesky.correlated_gaussian_law`, [SpecialCases.lean:43](/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/SpecialCases.lean:43), proves the pushforward identity
   \[
   (X,Y)\mapsto(X+K,K-X),\quad K=rX+\sqrt{1-r^2}Y,
   \]
   from a product of two standard scalar Gaussian measures to a product of scalar Gaussian measures with variances `2(1+r)` and `2(1-r)`. This is the correct substantive scalar identity.

   The statement does not mention `qOf`, `kOf`, an array or matrix, N, or general positive constants f and g. The project does not state the inverse-transformation, scaling, and product-over-entries result that identifies the complete ensembles. Those steps are mathematically valid, but remain outside the supplied formal chain. Setting `r = 0` likewise supplies the scalar fact behind independence of Q and K, rather than a matrix independence theorem.

   **Severity: the full ensemble-identification claim is unchecked as stated under the requested no-unformalized-step standard; the scalar law is correct.** The theorem also explicitly assumes `|r| < 1`. This agrees with positive f and g, but does not include the degenerate correlated models `r = ±1`.

7. **Additional mathematical prose has no corresponding completed theorem statement.**

   Answer line 35 also says a normal form can have every rank `n ≥ 1`. This is true, but `theta_attained` in `TheoremAExtra.lean:83` constructs only `OrthoBlocks 1 2`. The other main theorems take an existing `OrthoBlocks n N`; they do not assert existence with `rank L = n` for each n. A construction on coordinate planes and a rank calculation supply the missing result. **Severity: unchecked as stated, with an elementary mathematical repair.** This does not diminish the actual Theorem 1(5), which asks only for some witness.

   Answer line 48 says the finite-N head is a sum of n independent blocks. The construction does give independent rank-one summands, but no cited theorem asserts their mutual independence. `theoremB_ae` proves convergence from column assumptions and does not make a block-independence assertion. Its deliberately weaker pairwise independence of columns is sufficient for convergence. **Severity: this additional probability assertion is not formally checked as stated.** Here “blocks” means rank-one summands; at finite N their planes are not generally mutually orthogonal.

The following checks **match**, with the qualifications identified above. The table uses `File.theorem:line` as a file locator, not as a Lean namespace.

| Answer claim | Lean statements and definitions checked | Assessment |
|---|---|---|
| §1, lines 5 and 11: L, S, T, the profile, and spectral conventions | `GenProfile.formL`, `formLt`, `formS`, `formT`, `eigS`, `eigT2`, `lamP`, `lamM`, `sigT`, `gA`–`gD`; `frobL_eq`, `frobT_eq` | Correct orientation: `formL q k x = Σ ⟨q_i,x⟩k_i` is `KᵀQ`. The positive list takes the largest eigenvalues; the negative list negates the smallest in reverse order. `sigT` takes square roots at zero-based indices `0,2,4,…`. Frobenius denominators and positive/negative parts match. |
| §1, line 13: same `(Σ,W)` determines the congruence class and invariants | `Congruence.exists_isometry_of_same_W:170`, `gprof_isometry:186`, `gprof_eq_of_same_W:205`; internal `formL_map`, `eigS_map`, `eigT2_map` | Matches for fixed ambient N. The isometry is an invertible linear isometry, so this is orthogonal congruence. The Lean result does not even need `N ≥ 2n` for the congruence assertion. It preserves the actual spectral lists as well as the profile and relative error. |
| §1, lines 14–15: both identities involving `m₂` and q | `Identities.Wm`, `Fsq`, `m2`, `qrec`; `gA_identity:227`, `gprof_sum_eq_one:236`, `gA_sub_gB_identity:244` | Matches. `qrec` sums ordered off-diagonal pairs, with the stated normalization. The hypotheses are nonempty positive singular weights and orthonormal left/right families; the second identity also uses `2n ≤ N`, as in the question. Sorting the singular weights is unnecessary for these identities. |
| §1, line 16: log-product identity and zero mean log-ratio | `LogDet.stackRows:318`, `gramRows:321`, `lists_pos:563`, `prod_lam_eq_det:578`, `prod_sig_eq_det:636`, `logdet_identity:691` | Matches. Linear independence of the stacked rows is exactly full row rank. The Gram matrix is ordered Q then K. Both products equal `det G / 4^n`, and all logged entries are proved positive. The common expression `½ log det G − n log 2` and mean-zero statement are algebraic reformulations of these identities. No formal numerical spread statistic is defined; the statement that a nonzero log-ratio vector of zero mean has nonzero spread is the elementary interpretation. |
| §2, line 22: orthogonal planes, tilts, similar ordering, normal form | `Geometry.OrthoBlocks:30`, `t:46`, `α:49`, `β:52`; `Rearrangement.SimilarlyOrdered:17`, `SortsDesc:21`; RHS of `Main.main_mem_Theta_iff` | Correct definitions. Orthogonality includes u/u, v/v, and cross u/v between different blocks. The main statements explicitly add `abs(t_i) < 1`, matching the answer's nondegenerate planes and declared tilt range. They add `n ≠ 0`, appropriate for a defined nonzero profile. “Normal form” is expanded as a conjunction, not hidden in a weaker definition. |
| Lemma 1, line 24 | `Geometry.S_add`, `S_sub`, `neg_T_sq_add`, `neg_T_sq_sub`, `α_pos`, `β_pos`; `Spectral.charpoly_S:197`, `charpoly_neg_T_sq:205`, `roots_S_pos:234`, `roots_S_neg:248`, `roots_neg_T_sq_pos:264` | Matches, including the double multiplicity of the antisymmetric singular value and the ambient zero eigenvalues. |
| Theorem 1(1), line 27 | `Main.main_a_le_b:112`, `main_a_eq_b_iff:176` | Matches, including the equality case with ties. |
| Theorem 1(2), line 28 | `Main.main_relation_one:123` | Matches at every index of the decreasing lists. The common ordering hypothesis is explicit. |
| Theorem 1(3), line 29 | `Main.main_c_sub_d:137`; `TheoremAExtra.main_d_eq_zero_iff:43`, `main_c_eq_zero_iff:59` | Matches. All three conclusions retain the similar-ordering hypothesis. The weight is exactly `s_i² / ‖L‖²`, and the tilt signs have the correct orientation. |
| Theorem 1(4), line 30 | `Main.main_mem_Theta_iff:153`; `Profile.prof_sum_eq_one:51`, `mem_Theta_iff:111` | Matches within `OrthoBlocks`. The membership condition is written as `a = b ∧ c*d = 0`; nonnegativity follows from the profile formulas, and the sum-one identity is proved. The omitted explicit simplex predicate is harmless. Finding 1 concerns the subsequent unrestricted prose. |
| Theorem 1(5), line 31 | `TheoremAExtra.theta_attained:83` | Matches exactly: arbitrary `a>0`, `c,d≥0`, `cd=0`, `2a+c+d=1`; an actual one-block operator in dimension two is produced, with the profile verified for every orthonormal basis. On Θ, `a>0` excludes exactly the two endpoints. |
| Theorem 1 proof sketch, line 33 | `Spectral.frob_L:342`, `frob_T:362`; `Rearrangement.similarlyOrdered_iff_common_sort:34`, `blockwise_le_sorted:65`, `blockwise_eq_sorted_iff:74`, `relation_one:107` | Matches the sorted-pairing argument, the common-permutation criterion, and the norm normalization. |
| §3, lines 39–42: conditioned Gaussian construction and fixed-n convergence | `TheoremBFull.qOf:41`, `kOf:46`, `colVec:542`, `theoremB_ae:560`, `profile_tendsto:462`; `Gaussian.gaussian_prod_integrable`, `gaussian_second_moment`; `Probability.gram_slln` | Matches the explicitly conditioned assertion. `fv,gv` are fixed before the almost-everywhere quantifier. `colVec` uses initial columns of one sequence and divides by `√N`. Thus `qOf+kOf` and `kOf−qOf` have precisely the factors 2 in the answer. Pairwise independent identically distributed columns are weaker than the stated i.i.d. assumption, not an extra restriction. |
| §3: the limit profile belongs to an actual orthogonal-plane form | `TheoremB.blocks_of_limit_gram:123`; `TheoremBFull.limit_config:192`; `Limit.lists_at_limit:95`, `gprof_at_limit:228` | The algebraic `profA`–`profD` targets are connected to actual operators, rather than merely named “profiles.” The block eigenvalues are `fv,gv`; the singular weight is `fv+gv`; the tilt is `(fv−gv)/(fv+gv)`. There is no assertion that the growing-dimensional matrices themselves converge. |
| §3: similar ordering, `a−b→0`, relation (1) in the limit | `TheoremBExtra.similarlyOrdered_of_monotone:21`, `limit_a_eq_b:28`; `TheoremBFull.theoremB_ae`; `Main.main_relation_one` | Matches. Subtracting the two checked component limits gives `a−b→0`. The relative-error limit explicitly requires similar ordering, which monotonicity supplies. The limiting denominator is positive. |
| §3, lines 43–44: the expectation ratio and weighted-mean formula | `TheoremBExtra.cd_eq_ratio:52`, `cd_limit_ae:65`; `Probability.ratio_slln:61`; `Profile.profC_sub_profD:95` | Matches for one infinite latent sequence, as in finding 3. Integrability of the numerator and strict positivity of the denominator expectation are proved, not assumed. Measurability of monotone real functions follows from Mathlib's `Monotone.measurable`; this is not an extra substantive hypothesis. The code even proves this ratio limit without a common-sign assumption. The weighted-mean description is the identity `(f+g)² t abs(t) = (f−g) abs(f−g)`. |
| §3 proof sketch and row-size statement, lines 46 and 48 | `Orthonormalize.exists_orthonormal_near:52`; `Perturb.formL_perturb:88`, `formLt_perturb:99`; `Weyl.weyl_abs:116`; `TheoremBFull.eig_perturb`, `step_bounds`, `PhiL_cont`, `PhiT_cont`; `Probability.gram_slln` | The substantive convergence steps are checked, including bounds independent of N when n and the strengths are fixed. Gaussian row norms tending to one, followed by the displayed scaling, give the stated squared row norms. Correct the norms/squares wording as in finding 5. |
| §3 baseline limit, line 49 | `SpecialCases.const_profile:20`, together with `theoremB_ae` and `gprof_at_limit` | The limit profile `(1/2,1/2,0,0)` is checked for every positive constant and every positive n. The separate matrix-independence wording has the coverage qualification in finding 6. |
| §7, line 99: comparison of the two displayed formulas | `Ratio.fixed_ratio_bound:14` | Matches as an algebraic inequality. It proves `x ≤ y ≤ x(1+1/κ)` for `κ≥1`, `f,g>0`, a domain containing the question's `κ≥2`. For `f≠g`, this is exactly `0≤(y−x)/x≤1/κ`. For `f=g`, both expressions are zero; a literal relative quotient is undefined, while the proved multiplicative bound remains valid. This is a harmless boundary clarification. |

Two definition details do not invalidate those matching results. First, `Main.SpectralLists` uses decreasing lists specified by characteristic-polynomial root multisets, rather than directly using Mathlib's eigenvalue function. `spectralLists_exists` proves existence, and the sorting arguments prove the relevant uniqueness. These are genuine spectral lists, not arbitrary lists assumed to equal the desired answer. Second, `GenProfile` extends spectral lists by zero and totalizes division. In particular, `gErr` is zero when its singular-norm denominator is zero. The informal relative error is undefined there. This extension is harmless on the full-rank/nondegenerate domains used for the log theorem, Theorem 1, and the eventual Gaussian limit; outside those domains the answer needs a zero-padding/zero-denominator convention.

For **§6**, the axiom statement at line 79 is confirmed by the 30 queries. The blanket assertions at lines 3 and 79 that every theorem or identity in the answer is checked are not justified: findings 1–7 identify false prose, a narrower sign hypothesis, an implicit probability coupling, and omitted formal assembly. In the table, line 90 overstates the support-only consequence, and line 92 describes a full ensemble identification where the named theorem checks its scalar ingredient. The other rows accurately identify the main results, subject to their stated domains. The statement that every check “computes” the profile from Mathlib's sorted eigenvalues is imprecise for `Main.lean`, which uses the equivalent root-multiset specification; this is a harmless presentation difference, not a fake-spectrum issue.

For **§7**, lines 96–98 report measurements or descriptive fits and have no Lean theorem; that is appropriate. The fixed-ratio limit formula at line 99 likewise has no Lean theorem, as the answer explicitly acknowledges. `fixed_ratio_bound` compares two real expressions and does not prove that either is a joint `n,N → ∞` random-matrix limit. Theorem 2 indeed does not cover that joint regime. The unqualified phrase “the limit differs” is supported here only by the stated numerical observation, and even the two proposed expressions coincide when `f=g`. The final disclaimer at line 100 is incomplete if intended to list all material outside Lean: the additional coverage gaps above are not measurements or the fixed-ratio observation.

**The claim I checked hardest was Theorem 2's fixed-n profile convergence.** I traced the Gaussian normalization, the order of the fixed-strength and almost-everywhere quantifiers, the Gram limit, orthonormalization and perturbation bounds, sorted spectral extraction, squared Frobenius norms, and the identification of the limit with an actual orthogonal-plane form. That core claim matches. The negative verdict comes from the answer's stronger surrounding claims and its blanket verification claim, not from a discovered failure of that convergence formalization.
