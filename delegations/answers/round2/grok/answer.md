# A spectral-block ensemble for GPT-2 heads

The ensemble below is one recipe for all 144 raw GPT-2 small heads. It uses the measured singular values of \(L=K^\top Q\) as a covariate. It has three parameters per head when the block scales are global, and five when the two end-block scales are per head. Both fits are reported. The five-parameter fit is the one that reaches the relation-(1) error. The three-parameter fit is the one that predicts \(a-b\) from a statistic that is not \(q\).

Raw \(L\) only. LayerNorm-folded heads were not refit.

## 1. Sampling recipe

Fix \(n=64\). Write singular values \(\sigma_1\ge\cdots\ge\sigma_n>0\), \(F=\sum_i\sigma_i^2\). Split modes into three index blocks: top \(T=\{1,\ldots,8\}\), middle \(M=\{9,\ldots,56\}\), bottom \(B=\{57,\ldots,64\}\).

**Covariate.** Use the head's measured \(\Sigma\). The participation ratio is then not a prediction. A shared gamma law for \(\sigma_i^2\) was already shown in round 1 to miss the spread of the participation ratio, and this round does not add a spectral mechanism.

**Per head.**

- Alignments. Draw \(g_i\) i.i.d. standard normal and set
  \[
  t_i=\mathrm{clip}(\mu+s_t g_i,-0.999,0.999).
  \]
  Two parameters \((\mu,s_t)\).
- Reciprocal correlation \(\rho\in[-1,1]\), one parameter. This is the parameter that crosses \(a=b\): \(\rho>0\) pushes \(a-b\) down, \(\rho<0\) pushes \(a-b\) up (section 2).

**Global constants**, from the median over the 144 raw heads.

| constant | value | role |
|---|---:|---|
| \(\eta_M\) | 0.0438 | RMS of middle pairs |
| \(\eta_X\) | 0.0425 | RMS of cross-block pairs |
| \(\eta_T\) | 0.0743 | RMS of top-block pairs, if not per head |
| \(\eta_B\) | 0.141 | RMS of bottom-block pairs, if not per head |
| \(\rho_B\) | \(-0.834\) | correlation inside the bottom block |
| \(\nu\) | 5 | Student-\(t\) degrees of freedom on the end blocks |
| block size | 8 | top and bottom |

The five-parameter version replaces \((\eta_T,\eta_B)\) by the head's own top-block and bottom-block RMS. That is two further parameters.

**Off-diagonal pairs.** For each unordered pair \(\{i,j\}\), independently:

- If both indices lie in \(B\), draw a unit-variance Student-\(t_\nu\) pair with correlation \(\rho_B\) and scale \(\eta_B\). The \(t\) scale mixture is shared inside the pair (one \(\chi^2_\nu\) for both entries), so a spike hits \(E_{ij}\) and \(E_{ji}\) together. With \(\rho_B<0\) the pair is skew: \(E_{ji}\) has the opposite sign of \(E_{ij}\).
- Otherwise draw a Gaussian pair with correlation \(\rho\) and scale \(\eta_T\), \(\eta_M\), or \(\eta_X\) according to the region.

Set the diagonal of \(W\) to \((t_i)\) and the off-diagonal to these pairs. If \(\|W\|_{\mathrm{op}}>0.999\), replace the singular values of \(W\) by their minimum with \(0.999\). The projection is part of the model: \(W=U^\top V\) is a contraction.

**Query and key.** Let \(R\) be the positive semidefinite square root of \(I-W^\top W\). Draw a Haar \(N\times 2n\) frame \(F\) with \(N=768\). Set
\[
U=F\begin{pmatrix}I_n\\0\end{pmatrix},\qquad
V=F\begin{pmatrix}W\\R\end{pmatrix},\qquad
Q=\Sigma^{1/2}V^\top,\qquad
K=\Sigma^{1/2}U^\top.
\]
Then \(K^\top Q\) has singular values \(\Sigma\) and overlap \(U^\top V=W\). A different \(F\) is an orthogonal congruence and does not change the profile, the relation-(1) error, or \(W\).

**How the parameters are read off a head.**

- \(\mu=\sum_i w_i t_i\) and \(s_t^2=(\sum_i w_i(t_i-\mu)^2)/(1-1/\mathrm{PR})\), with \(w_i=\sigma_i^2/F\) and \(\mathrm{PR}=F^2/\sum\sigma_i^4\). These match the mean and the expected \(\sigma^2\)-weighted variance of the clipped-Gaussian law, up to the clip.
- Three-parameter fit, predictive: \(\rho\) is the Pearson correlation of \((E_{ij},E_{ji})\) over pairs that are not in the bottom block.
- Five-parameter fit: \(\eta_T\) and \(\eta_B\) are the RMS of those blocks, and \(\rho\) is chosen so that \(\mathbb E[q]=\rho\,S_{\mathrm{rest}}+\rho_B S_B\) equals the measured \(q\), then clipped to \([-0.999,0.999]\). Here \(S_{\mathrm{rest}}=\sum\sigma_i\sigma_j\eta_{ij}^2/F\) over ordered pairs outside \(B\), and likewise \(S_B\). Matching \(q\) makes \(a-b\) only partly a prediction (section 3).

## 2. Mechanisms

Notation from the record: \(W=D+E\), \(m_2=\sum\sigma_i^2 t_i^2/F\), \(q=\sum_{i\neq j}\sigma_i\sigma_j E_{ij}E_{ji}/F\), and
\[
a-b=c+d-m_2-q.
\]
The identity holds to \(10^{-15}\) on all 144 raw heads.

### (i) Crossing \(a=b\)

\(q\) is the \(\sigma\)-weighted sum of the products \(E_{ij}E_{ji}\). A pair with correlation \(\rho\) has \(\mathbb E[E_{ij}E_{ji}]=\rho\,\eta_{ij}^2\). Negative \(\rho\) makes \(q\) negative. Once \(q<c+d-m_2\), the identity gives \(a>b\).

On the raw heads this is not a small correction. The same-sign fraction among the largest 5% of pairs is 0.63 on the 100 heads with \(a<b\) and 0.42 on the 44 heads with \(a>b\). The unweighted non-bottom correlation \(\rho\) correlates with \(a-b\) at \(-0.85\). The top block carries more of \(q\) per entry than the middle, because the weights \(\sigma_i\sigma_j\) are larger there: the part of \(q\) from the top \(8\times 8\) correlates with the full \(q\) at 0.77. Low-PR heads (L0H3, L0H4, L0H7, L1H10) put almost all of their negative \(q\) in that block, and their top-block RMS is 0.14–0.21 against a median of 0.074.

The bottom block does not drive \(a-b\). Its correlation is strongly negative (\(\rho_B=-0.83\) at the median), but the singular values there are small, so the contribution to \(q\) is small. Zeroing that block moves the median of \(a-b\) by about \(-0.002\).

Diagonal \(W\) cannot do this. With the measured \((\Sigma,t_i)\) and \(E=0\), all 144 heads have \(a-b\le 0\) and the median relation-(1) error is 0.026. That restates R4.

### (ii) Relation-(1) error

Relation (1) is exact on each mode when \(W\) is diagonal (R2), and the log-mean is exact for every head (R5). The error is the sorted mismatch. Two pieces produce it here.

- Spread of \(t_i\). Sorting \(\lambda_\pm\) against a heterogeneous diagonal already gives median error 0.026.
- Within-block off-diagonal mass. Replacing the measured off-diagonal by a diagonal leaves 0.026. Keeping only the three diagonal blocks of \(E\) (top, middle, bottom) and zeroing every cross-block entry leaves median error 0.058 against the full 0.059. Cross-block entries are the wrong place. Shuffling middle pairs as intact pairs \((E_{ij},E_{ji})\), which keeps every magnitude and every within-pair sign and destroys positions, leaves the error at 0.058. Giving the two entries of each middle pair independent signs drops it to 0.049. Forcing every middle pair to be symmetric raises it to 0.104; forcing every middle pair to be skew raises it to 0.075.

So the error above the diagonal floor sits in the within-pair products, inside spectral blocks, and it is larger when those products are coherent. The ensemble's \(\rho\) and the heavier end-block scales are that mechanism. It is not a derivation from a training objective. It is the structure the ablations isolate.

The fit does not reach the full error on the extreme heads (section 3). At \(|\rho|=1\) and at the measured block RMS, \(L=K^\top Q\) for L0H3, L0H7, and L5H9 still has too little error. Homogeneous correlation inside a block spreads the products across all pairs in the block. The weights \(\sigma_i\sigma_j\) reward concentration on a few strong pairs. A one-pair spike with the same block RMS does the opposite: it overshoots the error (median 0.091 against 0.059) and, because amplitudes then exceed 1, the contraction projection fires on 59% of draws. The data lie between a homogeneous \(t\) block and a single spike. That interpolation was not fit.

### (iii) Heavy tails, and a correction to the symmetry claim

The off-diagonal kurtosis has median 20.6. It is not spread through \(W\).

- Of 377 entries with absolute value above \(5\) times the head's off-diagonal RMS, 255 lie in the bottom \(8\times 8\) and 79 lie in the top \(8\times 8\).
- Zeroing the off-diagonal of the bottom \(8\times 8\) drops the median kurtosis from 20.6 to 3.69. The middle block alone has kurtosis 3.12. The top block alone has kurtosis 3.19 at the median.
- Inside the bottom block the pair correlation has median \(-0.83\), and the block's own kurtosis has median 9.0. The large bottom entries are skew, with a heavy tail.
- The bottom-block RMS correlates with the participation ratio at \(+0.43\) and with the median relative gap of the bottom singular values at \(-0.12\). A gap-mixing explanation of the scale was checked and does not hold. The location of the tail is measured. Why the weak subspace is skew is not derived.

The symmetry score used in R8 does not say that the large pairs are symmetric. For a pair, \(|E_{ij}+E_{ji}|/(|E_{ij}|+|E_{ji}|)\) equals 1 when one entry is zero and the other is not. On 40 Gaussian \(64\times 64\) matrices the top 5% of pairs have median score 0.79, with 10th–90th percentiles 0.75 and 0.83. The trained median is 0.80, with percentiles 0.68 and 0.91. The Gaussian null sits on the trained value. The trained top-decile mean product is negative (\(-0.0018\)), and the median balance \(\min(|E_{ij}|,|E_{ji}|)/\max(|E_{ij}|,|E_{ji}|)\) in the top 5% is 0.32. The large entries are one-sided or skew. They are not a symmetric excess over the Gaussian.

R8's sign-flip ablation is a different statement and was not re-run here. What was re-run: independent signs on middle pairs drop the median error from 0.059 to 0.049, and a common sign flip of each pair leaves it at 0.059. Within-pair signs matter. The score 0.80 does not identify those pairs as symmetric.

The ensemble produces the tail by a \(t_5\) law on the two end blocks, skew in the bottom block. Section 3 shows that this undershoots the kurtosis (median 8.8 against 20.6). The \(t_5\) marginal has kurtosis 9, which matches the bottom block's own kurtosis, but after mixing with the Gaussian bulk and after the contraction projection the matrix kurtosis comes out near 9 rather than 20. Replacing the \(t_5\) block by one skew pair whose amplitude matches the block RMS pushes the median kurtosis to 34 and the median error to 0.091, with the projection active on most draws. Both tail laws were checked. Neither matches the kurtosis and the profile at once.

## 3. Fit on all 144 raw heads

Eight Monte Carlo draws per head in the three-parameter fit, six in the five-parameter fit. Predictive numbers are means of those draws. Seeds and scripts: `fit_ensemble.py`, `fit_ensemble2.py`. Measurements of \(W\) were recomputed with the same profile function as the simulations; the relation-(1) error matches the record (median 0.0589, percentiles 0.0369 and 0.1559).

**Fitted inputs, three-parameter version.** \((\mu,s_t)\) from the diagonal moments, \(\rho\) from the non-bottom pair correlation, all three block scales global. The participation ratio is the covariate \(\Sigma\).

**Predicted, three-parameter version.** \(a-b\) is predicted. \(c-d\) and the diagonal share are consequences of \((\mu,s_t)\) and are marked as fitted in the last column.

| statistic | measured median [p10, p90] | predicted median [p10, p90] | corr | role |
|---|---|---|---:|---|
| relation-(1) error | 0.0589 [0.0369, 0.1559] | 0.0497 [0.0237, 0.1338] | 0.74 | predicted |
| \(a-b\) | −0.0121 [−0.0562, +0.0203] | −0.0188 [−0.0816, +0.0084] | 0.66 | predicted |
| \(c-d\) | +0.0002 [−0.0660, +0.0624] | +0.0005 [−0.0355, +0.0594] | 0.99 | fitted via \((\mu,s_t)\) |
| \(\min(c,d)\) | 0.0001 [0.0000, 0.0040] | 0.0000 [0.0000, 0.0002] | 0.37 | predicted |
| diagonal share | 0.184 [0.039, 0.552] | 0.187 [0.044, 0.528] | 0.94 | fitted via \((\mu,s_t)\) |
| off-diagonal RMS | 0.0483 [0.0417, 0.0539] | 0.0465 [0.0459, 0.0470] | 0.44 | predicted |
| off-diagonal kurtosis | 20.6 [4.4, 54.4] | 7.8 [6.1, 11.2] | −0.11 | predicted |
| participation ratio | 45.7 [24.6, 52.5] | 45.7 [24.6, 52.5] | 1 | covariate |

Sign of \(a-b\): 29 of the 44 positive heads are predicted positive, and the sign agrees on 87% of heads. The predicted \(a-b\) is shifted down by about 0.007. The \(c-d\) tails are too thin (10th percentile −0.036 against −0.066). The Gaussian law for \(t_i\) has kurtosis 3. Round 1 reported a within-head kurtosis of \(t_i\) near 4; that number was not recomputed here. The off-diagonal RMS is almost constant across simulated heads, so its correlation is a weak test. Kurtosis is not reproduced.

Matching \(\rho\) to \(q\) instead, still with global scales, is a different use of the same ensemble. Then \(a-b\) is partly fitted (correlation 0.87), the error correlation rises to 0.82, the error median stays 0.049, 35 of 44 positive heads are recovered, and 6% of heads clip at \(|\rho|=0.999\). Kurtosis is unchanged. Global scales cannot supply the \(|q|\) of those clipped heads.

**Fitted inputs, five-parameter version.** The same \((\mu,s_t)\), plus the head's \(\eta_T\) and \(\eta_B\), plus \(\rho\) matched to \(q\). Four percent of heads still clip.

| statistic | measured median [p10, p90] | predicted median [p10, p90] | corr | role |
|---|---|---|---:|---|
| relation-(1) error | 0.0589 [0.0369, 0.1559] | 0.0546 [0.0263, 0.1417] | 0.87 | predicted |
| \(a-b\) | −0.0121 [−0.0562, +0.0203] | −0.0194 [−0.0852, +0.0155] | 0.92 | partly fitted via \(q\) |
| \(c-d\) | +0.0002 [−0.0660, +0.0624] | +0.0007 [−0.0413, +0.0592] | 0.99 | fitted via \((\mu,s_t)\) |
| \(\min(c,d)\) | 0.0001 [0.0000, 0.0040] | 0.0000 [0.0000, 0.0002] | 0.36 | predicted |
| diagonal share | 0.184 [0.039, 0.552] | 0.185 [0.042, 0.546] | 0.94 | fitted via \((\mu,s_t)\) and the scales |
| off-diagonal RMS | 0.0483 [0.0417, 0.0539] | 0.0465 [0.0439, 0.0494] | 0.48 | partly predicted |
| off-diagonal kurtosis | 20.6 [4.4, 54.4] | 8.8 [3.8, 18.9] | 0.57 | predicted |
| participation ratio | 45.7 [24.6, 52.5] | 45.7 [24.6, 52.5] | 1 | covariate |

The relation-(1) median moves from 0.050 to 0.055, against 0.059 measured, and the correlation from 0.74 to 0.87. That is the gain from giving the end blocks their own scales. The 10th percentile of the error is still low (0.026 against 0.037). Kurtosis moves from 7.8 with correlation about 0 to 8.8 with correlation 0.57. The level stays about half the measured level, and the 90th percentile is 19 against 54. Sign of \(a-b\) agrees on 89% of heads; 32 of 44 positive heads are recovered. The downward bias in \(a-b\) remains, about 0.007, including in the \(q\)-matched fit, so the samples do not realize the targeted \(q\). The contraction projection is the likely cause. It was not separated out draw by draw in this fit.

\(\min(c,d)\) is already about 0 in the data (90th percentile 0.004). The ensemble also sits at 0. The correlation is a comparison of two near-zero series.

## 4. What would falsify it, and the worst heads

The ensemble is falsified if any of these holds on these heads or on a second model.

1. The sign of \(a-b\) disagrees with the sign of the non-bottom pair correlation on much more than the present 13% of heads, or \(a-b\) stops tracking \(q\). On this fit the predictive correlation is 0.66 and the sign agreement is 87%. A correlation below about 0.4 on a second model would retire \(\rho\) as the crossing parameter.
2. Zeroing the bottom \(8\times 8\) off-diagonal leaves the kurtosis near 20, or that block's pair correlation is not negative. The present drop is from 20.6 to 3.7, and the median correlation is \(-0.83\).
3. Heads with \(a>b\) and low participation ratio do not carry elevated, negatively correlated mass in the top block. L0H3, L0H4, L0H7, and L1H10 are the present examples (top-block RMS 0.14–0.21, and \(q\) from that block equal to the whole \(q\)).
4. The relation-(1) error of a head is insensitive to within-pair signs inside spectral blocks. The middle-block sign ablation moves the median from 0.059 to 0.049.
5. A kurtosis near 20 and a relation-(1) error near 0.06 are produced together by an i.i.d. heavy-tailed matrix, or by one reciprocal spike, without the error overshooting. The one-spike trial on these heads gave kurtosis 34 and error 0.091.

The worst heads under the five-parameter fit, by absolute error in the relation-(1) prediction:

| head | measured error | predicted | measured \(a-b\) | predicted \(a-b\) | \(\eta_T\) | \(\rho\) |
|---|---:|---:|---:|---:|---:|---:|
| L0H7 | 0.362 | 0.129 | +0.141 | +0.061 | 0.149 | −1 (clipped) |
| L0H3 | 0.381 | 0.225 | +0.195 | +0.146 | 0.155 | −1 (clipped) |
| L5H9 | 0.441 | 0.315 | −0.254 | −0.204 | 0.124 | +1 (clipped) |
| L0H4 | 0.330 | 0.213 | +0.161 | +0.142 | 0.137 | −1 (clipped) |
| L0H1 | 0.191 | 0.094 | −0.044 | −0.026 | 0.049 | +0.29 |
| L1H11 | 0.160 | 0.075 | +0.001 | −0.030 | 0.143 | −0.07 |

L0H3, L0H4, and L0H7 are low-PR early heads whose negative \(q\) is concentrated on the top modes beyond what \(\rho=-1\) and the observed top-block RMS realize after projection. L5H9 is the opposite end: \(q=+0.21\), of which the top block supplies only \(+0.03\), kurtosis 4.2, error 0.44. Its reciprocal mass is in the middle, and a homogeneous \(\rho=+1\) at \(\eta_M=0.044\) is not concentrated enough. L0H1 is a strongly aligned head (the diagonal carries the error) whose off-diagonal model adds too little. These six heads are where a constant correlation inside a block is the wrong shape.

## 5. Standing of the ensemble

The recipe covers both sides of \(a=b\) with one correlation \(\rho\). On the three-parameter fit that correlation, read from \(W\) and not from \(q\), recovers the sign of \(a-b\) on 87% of heads and ranks the heads with correlation 0.66. Giving the end blocks their measured scales and matching \(q\) raises the relation-(1) correlation to 0.87 and the median error from 0.050 to 0.055, against 0.059 measured and against 0.026 for the diagonal. That is as close as this family got.

It does not produce the kurtosis. The tail is real, it sits in the bottom \(8\times 8\), and it is skew. A \(t_5\) block with the right RMS yields kurtosis about 9. A single skew spike with the same RMS yields kurtosis about 34 and too much relation-(1) error. The record's description of those large pairs as symmetric is the Gaussian value of the symmetry score; the score's null was not in the record and is 0.79 here.

Two limitations are part of the result. The singular-value spectrum is an input, so the participation ratio is not explained. The contraction projection biases \(a-b\) down by about 0.007 even when \(q\) is the fitting target, and that bias was not removed. A second model was not fit.

Scripts in this directory: `diagnose_fast.py` (the \(W\) measurements and the saved `gpt2_raw_stats.npz`), `fit_ensemble.py` (three-parameter fit), `fit_ensemble2.py` (five-parameter fit), `fit_spike.py` (the one-spike tail, which fails). `diagnose_structure.py` is an earlier pass and is not the source of the numbers above.
