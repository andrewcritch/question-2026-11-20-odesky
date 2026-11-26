Qualified pass: the central theorem statements match, but the blanket claim of complete Lean coverage overstates the transfer to the question’s unnormalized Gaussian model.

I checked the supplied answer, question, cited theorem statements, and their project definitions independently. I found no mathematical counterexample to Theorem 1 or Theorem 2, and no hidden hypothesis that narrows either theorem’s substantive conclusion. The findings below concern a missing formal transfer, conventions at degenerate forms, and the interpretation of the fixed-ratio bound. They do not establish that either central theorem is wrong.

Answer line numbers refer to `answer_draft.md`. Lean paths below are relative to `/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/`. I also queried `#print axioms` for every theorem named in the §6 table, plus `ratio_slln`, `fixed_ratio_bound`, and `const_one_sub_two_a`, using the existing built project. Each returned only `propext`, `Classical.choice`, and `Quot.sound`. This was a statement audit, not a fresh rebuild of every source file. I changed no source file.

**Findings**

1. **The identification with the original Gaussian model leaves a formal transfer unchecked.**

   **Claim:** Lines 48–50 call the question’s correlated Gaussian model a special case; line 73 repeats that conclusion. Line 77 says every theorem and identity in §§1–3 is checked “with no unproved steps.”

   **Lean:** `SpecialCases.lean:43`, `correlated_gaussian_law`; `SpecialCases.lean:20`, `const_profile`; `TheoremBFull.lean:560`, `theoremB_ae`.

   **Difference:** `correlated_gaussian_law` proves precisely the joint law of the two scalar quantities
   \[
   X+(rX+\sqrt{1-r^2}Y),\qquad (rX+\sqrt{1-r^2}Y)-X.
   \]
   Its conclusion is the product of centered Gaussian laws with variances \(2(1+r)\) and \(2(1-r)\). This part of line 49 and the narrowly worded §6 table entry at line 91 match exactly.

   The original model has unnormalized standard Gaussian entries. The ensemble used by `theoremB_ae` divides the Gaussian rows by \(\sqrt N\). Thus, with the stated constants, the corresponding operators satisfy in law
   \[
   L_{\mathrm{original}}=N L_{\mathrm{ensemble}}.
   \]
   Transferring the profile conclusion requires \(\pi(NL)=\pi(L)\), and transferring the relative-error conclusion requires the corresponding scale invariance of that error. Neither the cited statements nor another theorem in the supplied project states or proves this invariance for `gA`, `gB`, `gC`, `gD`, and `gErr`. The project also stops at an entrywise law rather than an assembled array-law identification. Mathlib’s `gaussianReal_map_const_mul` supplies the scalar Gaussian scaling fact, but it does not supply the missing profile theorem.

   **Severity:** **Unchecked as stated**, limited to this transfer and the blanket completeness assertion. The transfer is mathematically valid; line 49 explicitly acknowledges the normalization, so this is not a claimed numerical or sign error. The normalized Gaussian baseline and its limit are covered. A profile scale-invariance lemma and a model-identification corollary would close the formal gap.

2. **The universal statements about spectra and error use an unstated extension at degenerate heads.**

   **Claim:** Lines 5 and 11–15 use the question’s spectral lists for rank-\(n\) forms generally; §6 lines 81–82 also mention the relation-(1) error.

   **Lean:** `GenProfile.lean:103–110`, `eigAt`, `lamP`, `lamM`, `sigT`; `GenProfile.lean:156`, `gErr`; `Bridge.lean:115`, `gprof_of_formL_eq`; `Identities.lean:227–244`, the general profile identities.

   **Difference:** Lean uses lists of length `n`, padded with zeros when necessary. It also uses Lean’s total division, so an error with zero denominator receives a value. For example, \(n=1\), \(N=2\), \(Q=K=(1,0)\) gives a rank-one symmetric operator. Lean has `lamP = [1]`, `lamM = [0]`, `sigT = [0]`, and `gErr = 0`. The question’s description as three lists of positive numbers does not literally cover this case, and its relative-error quotient is \(0/0\).

   **Severity:** **Harmless difference on the nondegenerate domain**, but an explicit convention is needed for the universal wording. Zero padding makes the profile identities meaningful and agrees with the question’s intended rank-one endpoints. A relative error at \(T=0\) needs a separate convention or exclusion. This does not affect the log identity, which assumes independent stacked rows, or the positive-strength limit configuration.

3. **The fixed-ratio bound is a bound on a proposed expression, not a verified random-matrix limit.**

   **Claim:** Line 99: “Writing \(x\) for the iterated-limit value and \(y\) for the fixed-ratio value, \(x\le y\le x(1+1/\kappa)\)” and “Lean checks this bound.”

   **Lean:** `Ratio.lean:14`, `fixed_ratio_bound`; `Extras.lean:45`, `const_one_sub_two_a`.

   **Difference:** `fixed_ratio_bound` defines `x` and `y` by the two displayed rational expressions. It contains no matrices, probability, or limit. It assumes \(\kappa\ge1\) and \(f,g>0\). The answer’s ambient \(N\ge2n\) gives \(\kappa\ge2\), so that hypothesis is harmless. `const_one_sub_two_a` correctly identifies the iterated-limit expression through the already checked limit profile. Nothing identifies the proposed `y` with an actual fixed-ratio almost-sure limit.

   **Severity:** **Harmless when read with the explicit “numerical observation” qualification in lines 99–100; unchecked as a claim about the actual fixed-ratio limit.** The algebraic bound, the relative bound for \(f\ne g\), and the substitution \(f=g\Rightarrow x=y=0\) are correct for the expressions. The 5–8% statement is rounded arithmetic, not an additional asymptotic theorem.

**Definition correspondence**

- `formL q k` is \(x\mapsto\sum_i\langle q_i,x\rangle k_i\), exactly \(K^\top Q\). `formLt_adjoint` verifies the transpose interpretation. `formS` and `formT` have the correct factors and signs.
- `eigS` and `eigT2` use decreasing eigenvalues of \(S\) and \(-T^2=T^\top T\). `lamM` reverses the full eigenvalue list before negating, so it sorts absolute negative eigenvalues decreasingly. `sigT` takes positions \(0,2,4,\ldots\) before square roots. The pairing is justified in the block characteristic-polynomial results and, for the log-determinant argument, by `LogDet.lean`’s `pair_eq`.
- `frobL` and `frobT` are **squared** Frobenius norms, despite their short names. `frobL_eq` and `frobT_eq` identify them with sums of squared image norms over an orthonormal basis. `gA`–`gD` and `pa`–`pd` consequently have the question’s normalization. `gErr` has exactly the stated Euclidean relative-error formula on its nonzero-denominator domain.
- `OrthoBlocks` encodes positive weights, unit vectors, and all cross-block orthogonality conditions. It permits degenerate pairs in the structure itself, but the relevant theorems explicitly require `∀ i, |B.t i| < 1`. For unit vectors this is the answer’s exclusion \(u_i\ne\pm v_i\). `t`, `α`, and `β` are the stated formulas. `SimilarlyOrdered` is exactly the pairwise product inequality. Normal form is expressed by the conjunction of similar ordering and a common weak sign for all tilts.
- `SpectralLists` constrains both ordering and the complete multisets of positive/negative roots, with multiplicities. It is not an arbitrary choice of lists: `spectralLists_exists` proves existence. `Weyl.lean:134`, `roots_charpoly_eq_eigenvalues`, connects characteristic-polynomial roots to Mathlib eigenvalues.
- The Lean membership conclusions express \(a=b\) and \(cd=0\), without defining a named set `Theta`. This is harmless for these profiles: their nonnegativity follows from the formulas and positive denominators, and `prof_sum_eq_one`/`gprof_sum_eq_one` supply the simplex equation.

**Claim-by-claim correspondence**

| Answer claim | Lean statements and assessment |
|---|---|
| §1, line 11: a rank-\(n\) head has the stated SVD representation | `Bridge.lean:138`, `exists_svd_rows`, returns positive coefficients, two orthonormal families, and equality of the represented operator. This is an SVD in the answer’s unsorted convention. The theorem uses `n` rows and rank `n`, matching the head convention used in this answer. `gprof_of_formL_eq` transports the profile and lists. **Matches.** |
| §1, line 13: same \((\Sigma,W)\) implies orthogonal congruence and equal profile/relations | `Congruence.lean:170`, `exists_isometry_of_same_W`, gives one ambient linear isometry carrying both indexed families to the other pair. `Extras.lean:56`, `formL_isometry`, supplies conjugation; an orthogonal inverse is its transpose. `gprof_isometry`, `gprof_eq_of_same_W`, and `Bridge.lean:219`, `lists_isometry`, cover profiles, error, and lists. The isometry theorem is stronger than the answer: it does not need \(N\ge2n\). **Matches**, subject to finding 2’s convention. |
| §1, lines 14–15: definitions of \(F,m_2,q\) and both exact identities | `Identities.lean`’s `Fsq`, `m2`, and `qrec` use exactly the displayed sums; `qrec` includes both ordered off-diagonal pairs. `gA_identity`, `gprof_sum_eq_one`, and `gA_sub_gB_identity` give the stated identities. Nonzero `n`, positive singular values, and orthonormality are explicit. The second identity uses \(2n\le N\), already part of the question’s setup. **Matches.** |
| §1, line 16: determinant products and logarithmic identity | `LogDet.lean:578`, `prod_lam_eq_det`; `:636`, `prod_sig_eq_det`; `:691`, `logdet_identity`. `stackRows` and `gramRows` are precisely the stacked rows and their Gram matrix. Linear independence of these \(2n\) rows is exactly \(\operatorname{rank}F=2n\). `lists_pos` ensures that the logarithms concern positive values. **Matches.** |
| §1, line 16: log-ratios sum to zero and equal ratios vanish | `Extras.lean:27`, `logratio_sum_zero`, and `:32`, `eq_zero_of_sum_zero_of_const`. The latter’s `NeZero n` is the answer’s \(n\ge1\). Positivity from `lists_pos` makes zero log-ratio equivalent to relation (1). **Matches.** |
| §2, line 24: Lemma 1 | `Geometry.lean`’s `α_pos`, `β_pos`, `S_add`, `S_sub`, `neg_T_sq_add`, and `neg_T_sq_sub`; `Spectral.lean:197–264`, `charpoly_S`, `charpoly_neg_T_sq`, `roots_S_pos`, `roots_S_neg`, `roots_neg_T_sq_pos`. The squared singular value is \(\alpha_i\beta_i\), twice per plane, with only the stated ambient zero eigenvalues. **Matches.** |
| §2, line 27: Theorem 1(1), inequality and exact equality criterion | `Main.lean:112`, `main_a_le_b`, and `:176`, `main_a_eq_b_iff`. The equality criterion is the answer’s pairwise similar ordering, including ties. **Matches.** |
| §2, line 28: Theorem 1(2), equality at every spectral index | `Main.lean:123`, `main_relation_one`. It quantifies over every `k`, with sorted lists, and concludes equality of singular values rather than merely a product or norm identity. **Matches.** |
| §2, line 29: Theorem 1(3), weighted tilt formula | `Main.lean:137`, `main_c_sub_d`, has weights `B.s i ^ 2 / B.nL b`. `Spectral.lean`’s `frob_L` identifies the denominator with \(F\). **Matches.** |
| §2, line 29: Theorem 1(3), the two zero-coordinate equivalences | `TheoremAExtra.lean:43`, `main_d_eq_zero_iff`, and `:59`, `main_c_eq_zero_iff`. Both retain the similar-ordering hypothesis and use weak tilt inequalities. **Matches.** |
| §2, line 30: Theorem 1(4), normal form iff membership in \(\Theta\) | `Main.lean:153`, `main_mem_Theta_iff`. Both directions and the common-sign alternative agree. **Matches.** |
| §2, line 31: Theorem 1(5), attainment away from the endpoints | `TheoremAExtra.lean:83`, `theta_attained`, takes \(a>0\), \(c,d\ge0\), \(cd=0\), and \(2a+c+d=1\), exactly the nonendpoint points \((a,a,c,d)\) of \(\Theta\). It returns an actual nondegenerate normal-form block in \(\mathbb R^2\), with the required profile for every orthonormal basis. The answer does not require the witness to retain a previously fixed block count; §6 expressly says one block. **Matches.** |
| §2, lines 33–35: sorting/rearrangement argument, common sorting, and scope | `Rearrangement.lean`’s `blockwise_le_sorted`, `blockwise_eq_sorted_iff`, and `similarlyOrdered_iff_common_sort`, together with the spectral and Frobenius results above, supply the argument. Equal tilts reduce the displayed formulas to the rank-one profile. The restriction to orthogonal planes remains in every operator theorem. **Matches.** |
| §3, lines 39–42: normalized ensemble and fixed-\(n\) profile convergence | `TheoremBFull.lean:41`, `qOf`; `:46`, `kOf`; `:542`, `colVec`; `:560`, `theoremB_ae`. These give exactly \(Q=\sqrt f\,P/\sqrt N-\sqrt g\,M/\sqrt N\), \(K=\sqrt f\,P/\sqrt N+\sqrt g\,M/\sqrt N\), using the same infinite sequence of columns for all `N`. All four profile coordinates converge almost surely. **Matches.** |
| §3, line 42: the numerical target is the profile of an actual orthogonal-plane form with \(\alpha=f(\rho),\beta=g(\rho)\) | `TheoremB.lean:123`, `blocks_of_limit_gram`, constructs the blocks from exact Gram data. `TheoremBFull.lean:192`, `limit_config`, supplies those data from an orthonormal family; one can instantiate it with the standard basis in dimension \(2n\). `Limit.lean:95`, `lists_at_limit`, and `:228`, `gprof_at_limit`, identify the actual operator profile. Thus the target formulas have the asserted operator interpretation. **Matches through these supporting statements**, not through `theoremB_ae` alone. |
| §3, line 42: similar ordering, \(a-b\to0\), and relation (1) in the limit | `TheoremBExtra.lean:21`, `similarlyOrdered_of_monotone`, and `:28`, `limit_a_eq_b`, give ordering and equality of the limiting coordinates. Coordinate convergence gives the difference limit. `theoremB_ae` also directly concludes convergence of `gErr` to zero under similar ordering; `lists_at_limit` gives exact indexed equality at the limit. **Matches.** |
| §3, line 42: common sign gives normal form and relation (2) | `TheoremBExtra.lean:35`, `limit_mem_Theta`, assumes exactly the global alternative \((\forall y,g(y)\le f(y))\lor(\forall y,f(y)\le g(y))\). The block construction and Theorem 1 identify this with the sign condition on the limit tilts. **Matches.** |
| §3, lines 42–43: almost-sure limit as the block count increases | `TheoremBExtra.lean:52`, `cd_eq_ratio`, and `:65`, `cd_limit_ae`, with `Probability.lean:61`, `ratio_slln`. The numerator and denominator match exactly. The sequence uses the first `n+1` latent variables; this harmless shift excludes zero blocks. **Matches.** |
| §3, line 44: weighted-mean interpretation | `Extras.lean:22`, `weighted_tilt`, proves the pointwise identity \((f+g)^2t|t|=(f-g)|f-g|\), with the correct positive denominator. Together with the ratio formula it gives exactly the stated interpretation. **Matches.** |
| §3, line 46: proof through Gram convergence, orthonormalization, perturbation, and Weyl | `Probability.lean`, `gram_slln`; `Gaussian.lean`, `gaussian_prod_integrable` and `gaussian_second_moment`; `Orthonormalize.lean:52`, `exists_orthonormal_near`; `Perturb.lean`, `formL_perturb` and `formLt_perturb`; `Weyl.lean:116`, `weyl_abs`; and the lemmas inside `TheoremBFull.lean`. The perturbation constants depend on fixed strengths and block count, not ambient dimension. The Gram polynomials for the two squared norms appear as `PhiL` and `PhiT`. **Matches.** |
| §3, line 48: squared row norms approach \(4f(\rho_i)\) and \(4g(\rho_i)\) | This is the diagonal Gram convergence from `gram_slln`/`colVec_inner`, applied to the displayed definitions of \(Q+K\) and \(K-Q\). **Matches as a direct specialization.** |
| §3, lines 49–50: correlated entry law and baseline midpoint | `SpecialCases.lean:43`, `correlated_gaussian_law`, exactly checks the entry law stated in §6. `:20`, `const_profile`, checks the midpoint for any positive common constant and any nonzero block count. Its connection to the normalized operator follows from the limit results. **Matches these statements; finding 1 concerns the transfer to the unnormalized original model.** |
| §7, line 99: iterated-limit expression and fixed-ratio comparison | `Extras.lean:45`, `const_one_sub_two_a`, and `Ratio.lean:14`, `fixed_ratio_bound`. **Matches the algebraic comparison; see finding 3 for its probabilistic scope.** |

**Quantifiers and hypotheses checked most closely**

The claim I checked hardest was **Theorem 2’s convergence of the actual operator profile**, including its identification with a realizable limit form. `theoremB_ae` fixes `n`, `fv`, and `gv` before the almost-everywhere quantifier. Its randomness is the Gaussian column sequence. That is the answer’s “condition on \(\rho\)” reading; it does not silently average over the latent strengths. The column independence hypothesis is pairwise independence, weaker than the answer’s i.i.d. assumption, while the coordinates of the first column have joint independence and the standard Gaussian law. Identical distribution propagates that column law. No extra moment assumption on the latent strengths is imposed for this fixed-\(n\) result.

The headline theorem does not assume continuity of the profile. Although the older auxiliary theorem `Probability.limit_of_continuousAt` has such a hypothesis, `theoremB_ae` invokes `profile_tendsto`, where orthonormalization and Weyl estimates prove the needed convergence. This is a substantive checked bridge, not an unproved assumption hidden in a theorem parameter.

For the second limit, `cd_limit_ae` fixes the functions and uses an infinite identically distributed latent sequence. Its explicit measurability assumptions on `f` and `g` do not narrow the answer: monotone real functions are Borel measurable (`Monotone.measurable` in Mathlib). The sole integrability assumption is the stated second moment of \(f+g\). The proof derives numerator integrability and strict positivity of the expected denominator; neither is an unstated extra assumption. There is no exchange of limits and no claim about \(N=\kappa n\).

**Claims outside Lean coverage and the accuracy of §6**

The measurements and descriptive fits in §4 and §7 lines 96–98 have no Lean coverage. The purported fixed-ratio limiting formula and the measured numbers at line 99 also have no Lean coverage. The answer explicitly says so at lines 54 and 100; that limitation is accurately disclosed. The application “a measured head with \(a>b\) cannot have the orthogonal-plane representation” is the contrapositive of the checked Theorem 1(1); the measurements supplying its premise remain external.

I found no further substantive mathematical claim in the requested sections that lacks the corresponding theorem or a direct specialization of the checked formulas. The qualitative descriptions of naturalness, training effects, and fit quality are not formal mathematical conclusions.

The §6 table’s theorem names and mathematical content are accurate, with the conventions and scope qualifications above. In particular, line 91 carefully claims only an entrywise Gaussian-law identity, and line 88 can be substantiated using the exact-configuration construction described above. The axiom assertion is confirmed for the named results. The overstatement is the broader assurance at lines 3 and 77 that all mathematical transfers in the answer are checked with no unproved steps: the original-model transfer in finding 1 is not present in the supplied formalization.
