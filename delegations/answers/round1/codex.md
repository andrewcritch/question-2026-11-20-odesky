**Recommendation.** Use a random distribution of alignment strengths in the **singular-vector basis**, together with **correlated reciprocal off-diagonal overlaps**. My best tested version has three parameters per head. It reproduces several aggregate statistics and predicts head-to-head variation, but it does **not** reproduce all the supplied observations. In particular, it underestimates relation-(1) error and fails on some extreme heads. I would treat it as a useful reference ensemble, not as an explanation of training.

The most useful new finding is that the off-diagonal overlaps carry a scalar statistic that almost determines departures from `a=b`. A model that explains only the distribution of the diagonal alignments misses this effect. I tested three candidate families below, including a more mechanistic two-parameter model that failed substantially.

All empirical results here use the supplied GPT-2 weights and scripts. No external literature claims are needed for the proposed models or the derivations.

**An exact identity and a quantitative obstruction.** Write

\[
F=\sum_i\sigma_i^2,\quad w_i=\sigma_i^2/F,\quad
W=D+E,\quad D=\operatorname{diag}(t_i),\quad E_{ii}=0,
\]
\[
m_2=\sum_iw_it_i^2=\bar t^2+\operatorname{std}_w(t)^2,
\qquad q=\frac{1}{F}\sum_{i\ne j}\sigma_i\sigma_j E_{ij}E_{ji}.
\]

Here `q` measures reciprocal overlap, with weights from the singular values. Cyclicity of trace gives

\[
\frac{\operatorname{tr}(L^2)}F
=\frac{\operatorname{tr}(\Sigma W\Sigma W)}F=m_2+q,
\qquad
\boxed{a=\frac{1-m_2-q}{2}},
\qquad
\boxed{a-b=c+d-m_2-q}.
\]

For diagonal `W`, put \(p_i=\sigma_i(1+t_i)/2\) and \(r_i=\sigma_i(1-t_i)/2\). Before sorting, \(2\sum_i p_ir_i/F=a\). The rearrangement inequality gives

\[
b=2\langle p^\downarrow,r^\downarrow\rangle/F\ge a.
\]

Thus **every diagonal-overlap ensemble has `a-b ≤ 0`**, for every spectrum and every distribution of alignments. This excludes exact diagonal blocks for 44/144 raw heads and 82/144 LayerNorm-folded heads. This conclusion does not depend on a perturbative approximation.

I replaced each measured `W` by its diagonal, keeping its actual `Σ` and all 64 actual `t_i`. The results were:

| Statistic | Raw heads | LayerNorm-folded heads |
|---|---:|---:|
| Median measured error in (1) | 0.05893 | 0.07256 |
| Median error after deleting off-diagonal overlaps | 0.02639 | 0.02356 |
| Correlation of `q` with measured `a-b` | −0.9677 | −0.9961 |
| Correlation of `abs(q)` with error in (1) | 0.8775 | 0.9449 |
| Correlation of `(a-b)_block − q` with measured `a-b` | 0.9927 | 0.9983 |
| Mean absolute error of that last prediction | 0.00382 | 0.00458 |
| Mean absolute change in `c-d` after deletion | 0.00263 | 0.00345 |

The last approximation is equivalent, by the exact identity, to the empirical statement that `c+d` changes little when these overlaps are deleted. It is a diagnostic using the measured matrix, not a generative prediction.

This qualifies the supplied statement that off-diagonal effects are second order. They are second order in individual entries, but there are \(n(n-1)\) reciprocal products. Their aggregate is quantitatively important. For raw heads, `q` has median 0.00728 and 10th–90th percentiles [−0.02919, 0.03408], with more extreme negative values in some heads. The folded 10th percentile is −0.25043.

**Common construction for candidates 1 and 2.** Given positive `Σ` and a strict contraction `W`, draw an independent Haar orthonormal `2n`-frame \(O\in\mathbb R^{N\times2n}\), and set

\[
U=O\begin{bmatrix}I\\0\end{bmatrix},\quad
V=O\begin{bmatrix}W\\(I-W^TW)^{1/2}\end{bmatrix},\quad
K=\Sigma^{1/2}U^T,\quad Q=\Sigma^{1/2}V^T.
\]

Then \(K^TQ=U\Sigma V^T\) and \(U^TV=W\) exactly. This specifies actual query/key pairs; their particular head-space gauge is not intended to model the trained gauge.

There are two distinct ways to supply `Σ`:

- **Conditional test:** retain the head's measured spectrum. This isolates the overlap model; it is not a low-parameter explanation of the spectrum. The 64 singular values are supplied covariates.
- **Complete ensemble:** draw \(\sigma_i^2\) independently from \(\operatorname{Gamma}(\kappa,1/\kappa)\), then sort. Use one shared \(\kappa=2.44328\). This fixes arbitrary overall scale and uses no spectral parameter per head. An absolute scale can be added if needed; it affects none of the requested normalized statistics.

For this Gamma law, \(\mathbb E[1/\mathrm{PR}]=(\kappa+1)/(n\kappa+1)\). I chose `κ` by matching this expression to the reciprocal of the measured median PR. This is a convenient spectral closure, not a training theory. It gives a median PR near 46 but misses the observed variation across heads.

**Candidate 1: random diagonal alignments.** This is a useful baseline with **two parameters per head**, \(\mu\in(-1,1)\) and \(v\in(0,1-\mu^2)\). Define

\[
\nu=(1-\mu^2)/v-1,\qquad
B_i\overset{\mathrm{iid}}\sim
\operatorname{Beta}\left(\tfrac{1+\mu}{2}\nu,
                        \tfrac{1-\mu}{2}\nu\right),
\quad t_i=2B_i-1,\quad W=\operatorname{diag}(t_i).
\]

Then \(\mathbb E t_i=\mu\), \(\operatorname{Var}t_i=v\). For fixed `Σ`, the expected weighted sample variance is \(v(1-1/\mathrm{PR})\). I therefore estimated

\[
\widehat\mu=\bar t,\qquad
\widehat v=\operatorname{std}_w(t)^2/(1-1/\mathrm{PR}).
\]

The Beta law supplies bounded heterogeneous alignments without storing all `t_i`. It includes mixed signs and nearly uniform alignment as limiting regimes. One possible training interpretation is that separate learned features acquire different preferences for matching or opposing the corresponding query feature. Orthogonality of the feature pairs remains a substantive assumption.

Its block formulas explain approximate relation (1) when sorting changes pairings little. They explain spread along `Θ` when most alignments have one sign and sorting loss is small. If all `t_i` are nonnegative, sorted positive eigenvalues dominate sorted negative magnitudes, so `d=0` exactly; the negative case gives `c=0`. Mixed signs and large dispersion do not guarantee proximity to `Θ`.

This candidate reproduces the fitted diagonal moments and much of `c-d`, but has zero off-diagonal RMS, diagonal share one, and the sign obstruction above. **It is ruled out as a model of the full measured statistics.**

**Candidate 2: heterogeneous alignments with elliptic overlap noise.** Draw `t_i` as in candidate 1. Independently draw off-diagonal Gaussian pairs with

\[
\mathbb E E_{ij}=0,\qquad
\mathbb E E_{ij}^2=\eta^2,\qquad
\mathbb E E_{ij}E_{ji}=\rho\eta^2,
\quad E_{ii}=0.
\]

Different unordered pairs are independent. Equivalently, mix independent symmetric and skew-symmetric Gaussian noise with variance proportions \((1+\rho)/2\) and \((1-\rho)/2\). Set

\[
W=\mathcal P_{0.999}(D+E),
\]

where \(\mathcal P_c\) clips each singular value to at most `c`. This is the Frobenius projection onto the operator-norm ball; it makes every sample realizable. It is part of the model, not an optional numerical repair.

There are **three parameters per head**: `μ`, `v`, and `ρ`. I fixed the shared noise scale at the median raw-head off-diagonal RMS, \(\eta=0.0482849\). The cap is a fixed convention. Setting `ρ=0` gives a two-parameter subfamily.

Before projection,

\[
\mathbb E q=\rho\eta^2 C_\Sigma,\qquad
C_\Sigma=\frac{(\sum_i\sigma_i)^2}{\sum_i\sigma_i^2}-1.
\]

Positive reciprocal correlation pushes symmetric energy upward; negative reciprocal correlation pushes antisymmetric energy upward. The diagonal share is approximately

\[
\frac{\mu^2+v}{\mu^2+v+(n-1)\eta^2}.
\]

These formulas explain why diagonal share rises with head alignment and why a scalar reciprocal-correlation parameter is useful in addition to alignment mean and spread. They apply before clipping and are heuristics for the projected ensemble.

I tested two estimates of `ρ`:

- Unweighted: \(\widehat\rho=\sum_{i\ne j}E_{ij}E_{ji}/\sum_{i\ne j}E_{ij}^2\).
- Weighted: \(\widehat\rho=\operatorname{clip}(q/(\eta^2C_\Sigma),-0.999,0.999)\).

The weighted version performed better and is the version recommended here. **Fitting `q`, together with the two diagonal moments, is equivalent to fitting the symmetric/antisymmetric energy split.** Consequently its `a-b` result is only partly predictive. Neither `b`, `c-d`, nor the sorted relation-(1) error was used as a fitting target.

This is the most useful descriptive candidate I tested. Its Gaussian residual has a short covariance description, but the diagonal specialization and reciprocal covariance are assumptions about training, not consequences derived from its loss. It also treats singular modes as exchangeable, so it cannot explain systematic dependence of alignment or residual covariance on singular-value index.

**Candidate 3: Gaussian feature pairs with random correlations.** This has a more direct interpretation in terms of query/key features and **two fitted parameters per head**. Fix shared effective input dimension `m=430` and shared strength shape `k=10`. Draw a Haar `m`-frame \(J\in\mathbb R^{N\times m}\). Independently for each row, draw

\[
x_i,y_i\sim N(0,I_m/m),\quad
r_i=2B_i-1,\quad
d_i=\sqrt{\operatorname{Gamma}(10,1/10)},
\]
\[
K_i=\sqrt{d_i}\,x_i^TJ^T,\qquad
Q_i=\sqrt{d_i}\left(r_ix_i+\sqrt{1-r_i^2}\,y_i\right)^TJ^T.
\]

Use the same two-parameter Beta family for `r_i`. Here the correlations vary by row rather than by singular mode. The common subspace gives overlap fluctuations on the order of \(m^{-1/2}\approx0.0482\); heterogeneous strengths broaden the spectrum. `m` is an effective-dimension hypothesis, not a measured literal subspace dimension. The chosen strength law gives a useful median PR but was not optimized over alternatives.

I fitted the two Beta parameters to the resulting **SVD** alignment mean and spread, using simulation. This distinction matters: row correlations are not the diagonal entries of `UᵀV` after singular-vector mixing.

The fit reproduced these alignment summaries fairly well but failed the central spectral test. When positive and negative row correlations mix, substantial symmetric structure can reside off the diagonal in the SVD basis. Merely making Gaussian row correlations heterogeneous does not produce the desired ensemble.

**Numerical comparison.** I used all 144 raw heads. Candidates 1–2 used 32 Monte Carlo draws per head. Candidate 3 used four common-random-number draws for fitting and 16 separate draws for evaluation. The table gives medians over heads of predictive means; the measured column contains one trained realization per head. These are in-sample descriptive comparisons, not validation on unseen models or heads.

| Statistic | Measured | Diagonal Beta | Beta + independent noise | Beta + weighted elliptic noise | Gaussian feature pairs |
|---|---:|---:|---:|---:|---:|
| Error in (1) | 0.0589 | 0.0299 | 0.0239 | 0.0391 | 0.1261 |
| `a-b` | −0.0121 | −0.0081 | −0.0094 | −0.0188 | −0.0797 |
| Diagonal share | 0.1835 | 1.0000 | 0.1823 | 0.1841 | 0.0890 |
| Weighted alignment spread | 0.0924 | 0.0928 | 0.0934 | 0.0922 | 0.0874 |
| Off-diagonal RMS | 0.0483 | 0 | 0.0483 | 0.0483 | 0.0556 |

Candidates 1–2 in this table retain the actual `Σ`. Candidate 3 generates the entire spectrum. The simulation also caps candidate 1's diagonal entries in magnitude at 0.999, affecting 0.087% of draws. Matching the first two alignment moments is a fit, and matching median off-diagonal RMS in candidate 2 is calibration, not a prediction.

For the weighted elliptic candidate:

| Unfitted or partly predicted statistic | Correlation with measured values | Mean absolute error |
|---|---:|---:|
| Error in (1) | 0.849 | 0.0277 |
| `a-b` (partly fitted through `q`) | 0.880 | 0.0133 |
| `c-d` | 0.991 | 0.0118 |
| Diagonal share | 0.941 | 0.0498 |

The independent-noise subfamily gives only 0.529 correlation for error in (1) and 0.211 for `a-b`. The unweighted elliptic version improves these to 0.743 and 0.618. The distinction between weighted and unweighted reciprocity is evidence against completely exchangeable residuals.

Replacing the actual spectrum in the weighted elliptic candidate by the shared Gamma spectrum leaves its main results similar: median error 0.0391, correlation 0.831 for that error, and correlation 0.888 for `a-b`. However, generated PR has median 46.13 and 10th–90th percentiles [42.53, 49.14], versus trained [24.6, 52.5]. Thus the complete three-parameter ensemble misses spectral heterogeneity. A head-specific `κ` adds one parameter and can fit PR, but does not establish the spectral law.

The Gaussian feature candidate gives an especially clear failure: its predicted error-(1) 90th percentile is 0.906, versus 0.156 measured, despite mean absolute alignment-mean and alignment-spread errors of only 0.0120 and 0.00744. Its median PR is 45.41. Correct diagonal summaries and plausible effective rank are therefore insufficient.

**Failures and falsification.** The weighted elliptic ensemble already fails several checks:

- It underestimates the typical error in (1). Its predicted 10th–90th percentiles are [0.0192, 0.1342], versus [0.0369, 0.1559].
- The contraction projection activates in 15.8% of conditional draws. Near extreme alignment, it materially changes the fitted diagonal moments. For L0H5 it predicts mean alignment 0.816 instead of 0.911, and a mean minimum alignment of 0.662 instead of the observed −0.023. The weak singular directions are not exchangeable with the strong ones.
- Seven heads require clipping the weighted `ρ` estimate at the allowed endpoints. For L0H3, measured `q=−0.19697` exceeds what homogeneous residual variance can supply in magnitude. The model predicts error 0.188 instead of 0.381. Concentration of reciprocal overlaps in spectrally important directions matters.
- Its shared noise scale omits real variation in off-diagonal RMS. Its shared Gamma spectrum omits large variation in PR. I did not fit an ensemble to the folded heads; only the exact diagnostic and diagonal-deletion experiment cover them.

For a stronger version of candidate 2, the decisive next measurements are the matrices \(\mathbb E[E_{ij}^2]\) and \(\mathbb E[E_{ij}E_{ji}]\) as functions of singular-value index, and the conditional distribution of `t_i` given `σ_i`. Test these on heads excluded from calibration. A persistent dependence on index falsifies the exchangeability assumption; the extreme-head results already suggest such dependence. A next model can retain the same three summaries while replacing homogeneous Gaussian noise with structured residuals, but choosing that structure without measuring it would add unsupported assumptions.

My preference is therefore **candidate 2 as a reference model**, with candidate 3 as a useful failed mechanistic explanation. The target is well-posed as a statistical approximation problem, but the supplied marginal statistics do not identify an ensemble or a training mechanism. I have not found a validated one- or two-parameter model that reproduces all of them. The strongest result from these checks is the additional constraint: a successful model needs to explain **spectrally weighted reciprocal overlap**, not just heterogeneous diagonal alignment.

**Files and reproducibility.** All scripts and outputs are in this working directory:

- `investigate.py`: extracts `Σ,W` by thin QR and a 64×64 SVD, computes actual and diagonal-block profiles, and writes `heads.npz` and `diagnostics.csv`.
- `summarize_diagnostics.py`: writes `diagnostic_summary.json`, checks the exact energy identity, and compares the compressed profile calculation to an independent direct-matrix calculation.
- `fit_ensemble.py`: fits/evaluates candidates 1–2 and ablations; writes `ensemble_parameters.csv`, `ensemble_predictions.csv`, and `ensemble_summary.json`. Seed 20261124.
- `standalone_check.py`: evaluates the complete Gamma-spectrum version; writes `standalone_predictions.csv` and `standalone_summary.json`.
- `feature_ensemble.py`: fits/evaluates candidate 3; writes `feature_predictions.csv` and `feature_summary.json`. Seed 8142.

Run these in the order listed, using the supplied environment's Python with `-I`. Each script that imports a local helper explicitly adds its own directory to the import path. No input files were modified.

Across raw and folded heads, the recomputed `a,b,c,d,err1,tbar,tstd,offrms,PR` differed from the supplied CSV by at most \(6.97\times10^{-6}\). The original script forms raw `L` in float32; this extraction starts in float64. The exact energy identity held to \(9\times10^{-16}\). The independent direct-matrix check agreed in relation-(1) error to \(1.2\times10^{-16}\).
