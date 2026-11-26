**Result: one tested eight-parameter ensemble reproduces the typical relation-(1) error, both signs of $a-b$, and the scale of the heavy tails. It does not fit all 144 heads adequately. I do not claim a complete affirmative answer to the project goal.**

The proposed ensemble is a Gaussian overlap background with a small number of spectrally localized skew couplings, specified in the SVD gauge. It generates the whole singular spectrum from one fitted scalar; it does not retain a head's 64 singular values. On all 144 raw GPT-2 heads, its predicted relation-(1) error has median **0.05923**, against **0.05893** measured, and Pearson correlation **0.905**. Its $a-b$ correlation is **0.950**. It predicts the correct sign for **130/144** heads. However, it underestimates several extreme heads, overestimates diagonal share, and substantially underestimates the small nonzero values of $\min(c,d)$.

All measurements below use **raw $L=K^TQ$**, without LayerNorm folding. I read the complete project record and treated R1, R2, R4, and R5 as givens. No project input file was modified.

**1. A diagnostic that changes the interpretation of the large pairs.**

Write

\[
D=\operatorname{diag}(W),\qquad
E=W-D,\qquad H=(E+E^T)/2,\qquad J=(E-E^T)/2.
\]

Here $H$ and $J$ refer to the symmetric and skew parts of the **overlap**, not of $L$. The recomputed per-head statistics are:

| Statistic | Median [P10, P90] |
|---|---:|
| Off-diagonal kurtosis of $H$ | 3.633 [3.280, 5.096] |
| Off-diagonal kurtosis of $J$ | 53.87 [6.499, 155.93] |
| Fraction of the fourth moment contributed by the pure $J^4$ term | 0.8505 [0.2435, 0.9605] |
| Symmetry score among largest 5% of pairs | 0.8037 [0.6761, 0.9066] |
| Same score among largest 1% | 0.7103 [0.5516, 0.8670] |
| Same score among largest 0.5% | 0.6296 [0.3798, 0.8247] |
| Same score among largest 0.1% | 0.3570 [0.0293, 0.7549] |

The symmetry score and pair selection are exactly those in R8. For the fourth-moment fraction I used

\[
\frac{\sum_{i<j}J_{ij}^4}
{\sum_{i<j}(H_{ij}^4+6H_{ij}^2J_{ij}^2+J_{ij}^4)}.
\]

The denominator is half the sum of the fourth powers of all off-diagonal entries of $E$. Thus the statistic does include the mixed term.

These findings **do not contradict the checked top-5% statistic in R8**. They show that it cannot be extrapolated to the extreme tail. The numerous moderately large pairs lean symmetric; the much rarer extreme pairs lean skew and dominate the fourth moment. A model of sparse *symmetric* spikes would target the wrong fourth-moment component on a typical head.

An additional ablation retained each head's actual spectrum and diagonal. Its median relation-(1) errors were:

| Overlap retained | Median error |
|---|---:|
| Actual $W$ | 0.05893 |
| $D$ | 0.02639 |
| $D+H$ | 0.13795 |
| $D+J$ | 0.10036 |

For realizability the ablation code caps singular values at 0.999. The actual heads were unaffected. These ablations are diagnostics, not generative predictions. They show substantial cancellation between symmetric and skew contributions; it is inaccurate to interpret the full error as a positive sum of their separate errors.

**2. Precise sampling recipe.**

Fix $n=64$, $N=768$, and $M=n(n-1)/2=2016$. The eight head parameters are

\[
(\theta,\mu,\xi,\delta,\eta_H,\eta_J,f,\beta),
\]

with $\theta,\delta,\eta_H,\eta_J\ge0$, $0<f<1$, and real $\mu,\xi,\beta$. The shared constants are

\[
\alpha=0.53996028,\qquad m=9,\qquad c_*=0.999.
\]

Here $\alpha$ and $m$ were calibrated from overlap statistics as described below. The cap $c_*$ is a fixed numerical convention. The recipe has eight fitted scalars per head and two calibrated global constants. All requested statistics are scale invariant, so I set $\sum_i\sigma_i^2=1$. An optional overall scale would be a ninth head parameter if absolute weight norms were required.

1. **Generate the spectrum.** Let

   \[
   z_i=\Phi^{-1}\!\left(1-\frac{i-1/2}{n}\right),\qquad
   \sigma_i=\frac{e^{\theta z_i}}
   {(\sum_j e^{2\theta z_j})^{1/2}},\quad i=1,\ldots,n.
   \]

   This is a deterministic lognormal-quantile spectrum within an otherwise random matrix ensemble. It is a one-parameter spectral closure, not a claim that the observed singular values are lognormal samples.

2. **Draw the diagonal.** Put $w_i=\sigma_i^2$ and

   \[
   \ell_i=\log\sigma_i-\sum_jw_j\log\sigma_j,\qquad
   t_i=\mu+\xi\ell_i+\delta Z_i,
   \]

   where the $Z_i$ are independent standard normals. Set $D=\operatorname{diag}(t_i)$.

3. **Draw the symmetric background.** Index upper-triangular pairs by $e=(i,j)$, $i<j$, and put $v_e=\sigma_i\sigma_j$. Draw independent standard normals $G_e$, form $h_e=v_e^{\alpha/2}G_e$, and rescale the vector so that

   \[
   M^{-1}\sum_e h_e^2=\eta_H^2.
   \]

   Set $H_{ij}=H_{ji}=h_e$, $H_{ii}=0$.

4. **Draw the skew background and sparse couplings.** Draw an independent Gaussian vector $g\in\mathbb R^M$ and rescale it to

   \[
   M^{-1}\|g\|^2=\eta_J^2(1-f).
   \]

   Independently choose $m=9$ pair indices $I_1,\ldots,I_m$, with replacement, with probabilities

   \[
   \Pr(I_k=e)=\pi_e=\frac{v_e^\beta}{\sum_a v_a^\beta}.
   \]

   Draw independent standard normals $Y_1,\ldots,Y_m$. Form $u_e=\sum_{k:I_k=e}Y_k$, and rescale $u$ to

   \[
   M^{-1}\|u\|^2=\eta_J^2 f.
   \]

   Its norm is nonzero almost surely. Set $J_{ij}=g_e+u_e$, $J_{ji}=-J_{ij}$, $J_{ii}=0$. Repeated pair selections accumulate before the rescaling. The dense and sparse vectors are independent before their separate norm normalizations.

5. **Make the overlap realizable.** Form $W_0=D+H+J$. If $W_0=A\operatorname{diag}(s_k)B^T$ is an SVD, set

   \[
   W=A\operatorname{diag}(\min(s_k,c_*))B^T.
   \]

   This projection is part of the ensemble. It is not omitted when reporting its predictions.

6. **Sample actual $Q,K$.** Draw an independent Haar orthonormal $2n$-frame $O=[O_1\ O_2]\in\mathbb R^{N\times2n}$, and set

   \[
   U=O_1,\quad V=O_1W+O_2(I-W^TW)^{1/2},
   \]
   \[
   K=\Sigma^{1/2}U^T,\qquad Q=\Sigma^{1/2}V^T.
   \]

   Then $U^TU=V^TV=I$, $U^TV=W$, and $K^TQ=U\Sigma V^T$. This defines a distribution of genuine $n\times N$ query/key pairs. It models their bilinear form, not their learned head-space gauge. In particular, balanced $QQ^T=KK^T=\Sigma$ here is a gauge choice, not a claim about the measured raw row Gram matrices.

This is a phenomenological sparse random-matrix ensemble in the complete invariant of R1. It is not a derivation from a training objective. Its localization law and diagonal regression are substantive modeling assumptions.

**3. Mechanisms and exact statements.**

**Both sides of $a=b$.** Before projection, for this decomposition,

\[
q=\frac{2}{F}\sum_{i<j}\sigma_i\sigma_j
       (H_{ij}^2-J_{ij}^2),\qquad F=\sum_i\sigma_i^2.
\]

This identity is exact, including when $H,J$ are dependent. The cross terms cancel pair by pair. Together with R4,

\[
a-b=c+d-m_2-q.
\]

The relative symmetric/skew energy and the placement of the skew energy therefore provide a mechanism unavailable to diagonal models. Positive $\beta$ places sparse skew couplings preferentially among large singular directions; negative $\beta$ places them among small ones. Their influence on $q$ differs even at the same unweighted overlap RMS.

There is also an exact crossing argument within the family. Set $\theta=0$ and $\mu=\xi=\delta=0$, so that $\Sigma$ is scalar. With $\eta_J=0$, $W$ is symmetric and orthogonally diagonalizable in the SVD gauge; R4 gives $a\le b$. With $\eta_H=0$, $W$ is skew, its symmetric spectrum has equal positive and negative lists, and

\[
c=d=0,\qquad a-b=\|W\|_F^2/n>0
\]

for nonzero $W$. The contraction projection preserves symmetry or skew symmetry in these two limits. Continuity supplies transitions as their relative amplitudes change. Thus the recipe has no diagonal-model sign obstruction.

**Relation-(1) error.** For a transparent two-mode example, take $\Sigma=I_2$ and

\[
W=\begin{pmatrix}0&r\\-r&0\end{pmatrix},\qquad 0<r<1.
\]

The two positive and two negative symmetric eigenvalue magnitudes are all $\sqrt{1-r^2}/2$. The two distinct-list antisymmetric singular values are $(1+r)/2,(1-r)/2$. Consequently

\[
a-b=r^2,\qquad
\operatorname{err}_1^2=
\frac{2(1-\sqrt{1-r^2})}{1+r^2}.
\]

Thus an isolated skew coupling produces an error of order $r$, while the energy departure is of order $r^2$. The log-mean identity R5 still holds. Replacing the minus sign in $W$ by a plus gives $a-b=-r^2$ and error squared $2(1-\sqrt{1-r^2})/(1-r^2)$. These statements were also checked numerically.

In the full sampler, sparse couplings perturb a few spectral modes strongly, while the two backgrounds can partly cancel in $q$. This is the proposed mechanism for nontrivial sorted error near $a=b$. **The assertion that it supplies the observed full typical error is numerical**, not a theorem for this ensemble: the final median is 0.05923 and the measured median is 0.05893. The upper tail is still too small.

**Heavy tails with a symmetric-leaning top 5%.** The sparse skew component has at most nine selected pairs before projection. Its large coordinates supply the fourth moment. Most other pairs contain only the two Gaussian backgrounds, with the symmetric background typically stronger than the dense skew background. Those more numerous moderate pairs account for the top-5% symmetry bias. The final prediction is 0.836 versus 0.804 measured; this bias is somewhat too strong.

For an unnormalized version with $m$ independent Gaussian impulses of scale $\tau$, a fixed pair has sparse variance $m\pi_e\tau^2$ and fourth cumulant $3m\pi_e(1-\pi_e)\tau^4$. This exact elementary calculation explains why rare pair selection gives heavy tails. The separate norm rescalings and contraction projection change these formulas; applying them unchanged to the implemented sampler would be a heuristic.

**Spread along $\Theta$.** In the limit $\eta_H=\eta_J=\delta=\xi=0$, with $|\mu|<c_*$, the model has $W=\mu I$. R2 gives exactly

\[
(a,b,c,d)=((1-\mu^2)/2,(1-\mu^2)/2,(\mu)_+^2,(\mu)_-^2).
\]

Thus the family contains the full rank-one profile curve up to the cap. Small perturbations preserve approximate relations by continuity away from degeneracy. The fitted finite-noise regime requires numerical evaluation; closeness to $\Theta$ is not guaranteed for arbitrary parameters.

**4. What was fitted, and what was predicted.**

For each raw head I extracted $\sigma,W$ by thin QR factorizations and a $64\times64$ SVD. The eight fitting summaries are:

* Participation ratio, used to solve for $\theta$ exactly in the quantile spectrum.
* The weighted intercept, slope, and residual variance of $t_i=W_{ii}$ against centered $\log\sigma_i$, with weights $\sigma_i^2/F$. These give $\mu,\xi,\delta$.
* The off-diagonal RMS values of $H$ and $J$, giving $\eta_H,\eta_J$.
* A robust estimate of the non-Gaussian fraction of skew variance, giving $f$.
* The spectrally weighted second moment of $J$, giving $\beta$.

More precisely, for the diagonal fit, with weighted residuals $r_i=t_i-\mu-\xi\ell_i$, I used

\[
\delta^2=\frac{\sum_iw_i r_i^2}{\max(1-2/\mathrm{PR},0.1)}.
\]

This is an approximate finite-sample correction, not an exact unbiased-regression formula. For the skew fraction,

\[
f=\operatorname{clip}_{[.001,.999]}
\left(1-\frac{(\operatorname{median}_{i<j}|J_{ij}|/0.67448975)^2}{\eta_J^2}\right).
\]

Neither clipping endpoint was used by any of the 144 heads. This estimate treats the median as a measure of the Gaussian background; it is a modeling approximation.

Normalize the observed spectrum to $F=1$, set $v_{ij}=\sigma_i\sigma_j$, and write

\[
\gamma_J=\frac{\sum_{i<j}v_{ij}J_{ij}^2}{\sum_{i<j}J_{ij}^2},
\qquad \bar v=M^{-1}\sum_{i<j}v_{ij}.
\]

I fitted $\beta$ by

\[
\frac{\sum_e v_e^{\beta+1}}{\sum_e v_e^\beta}
=\operatorname{clip}_{[1.001v_{\min},\ .999v_{\max}]}
\frac{\gamma_J-(1-f)\bar v}{f}.
\]

The fitted $\beta$ transfers to the generated quantile spectrum. This fit ignores the bias from normalizing a finite number of impulses and from the final contraction projection; those biases remain visible in the results.

The shared $\alpha$ is the median of 144 analogous power-law exponents fitted to the weighted second moment of $H$. The shared impulse count $m=9$ was selected to match **median overlap kurtosis**, using pilot runs at $m=8,16$ and interpolation in $1/(m+2)$. Thus the agreement in median kurtosis is a **global calibration**, not an independent prediction. The per-head kurtosis variation was not fitted. As a sensitivity check, applying this calibration separately to even- and odd-indexed heads gives $m=9$ in both halves, and $\alpha=0.5544,0.5400$; this is not an out-of-sample validation run.

No $a,b,c,d$, sorted symmetric/antisymmetric spectrum, or relation-(1) error was an optimization target. However, the weighted overlap moments constrain $q$, so $a-b$ is **partly fitted through its energy mechanism**. Likewise, off-diagonal RMS is fitted, and PR is fitted exactly. The diagonal weighted moments constrain, but do not directly fit, $c-d$, diagonal share, and $\min(c,d)$.

I inspected exploratory variants on these same heads before choosing this family. Accordingly, “predicted” below means **not used as a numerical fitting target**, not independent confirmation on unseen heads or models.

Fitted parameter medians [P10, P90] were:

| Parameter | Median [P10, P90] |
|---|---:|
| $\theta$ | 0.3006 [0.2282, 0.5395] |
| $\mu$ | 0.003374 [−0.1920, 0.2429] |
| $\xi$, diagonal slope | 0.03765 [−0.2387, 0.4634] |
| $\delta$ | 0.07651 [0.05250, 0.1440] |
| $\eta_H$ | 0.03234 [0.02786, 0.03951] |
| $\eta_J$ | 0.03452 [0.02628, 0.04045] |
| $f$ | 0.3624 [0.1505, 0.4972] |
| $\beta$ | −1.844 [−4.617, 3.516] |

**5. All-head evaluation.**

The final evaluation used **128 independent draws per head**, 18,432 draws in total, with a new random seed after the pilot runs. Quantiles below are across the 144 head-specific predictive means. They are not quantiles of the pooled simulated heads. Correlations are Pearson correlations between a head's measured statistic and its predictive mean.

The relation-(1) error is

\[
\operatorname{err}_1=
\frac{\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|_2}{\|\sigma(T)\|_2},
\]

with all three lists sorted as in the question. Kurtosis is the uncentered fourth-moment ratio over off-diagonal entries, as in R8.

| Statistic and status | Measured median [P10, P90] | Predicted median [P10, P90] | $r$ | MAE |
|---|---:|---:|---:|---:|
| Relation-(1) error — predicted | 0.05893 [0.03686, 0.15594] | 0.05923 [0.03878, 0.13311] | 0.9052 | 0.01846 |
| $a-b$ — partly constrained by fitted moments | −0.01215 [−0.05621, 0.02029] | −0.01070 [−0.06368, 0.02360] | 0.9502 | 0.009442 |
| $c-d$ — predicted | 0.0001646 [−0.06600, 0.06241] | 0.00007258 [−0.05940, 0.05980] | 0.9972 | 0.004885 |
| $\min(c,d)$ — predicted | 0.0001128 [0, 0.003970] | 0.00001490 [0, 0.002265] | 0.8869 | 0.0006080 |
| Diagonal share of $W$ — predicted | 0.1835 [0.03891, 0.5519] | 0.2139 [0.04411, 0.6354] | 0.9681 | 0.03758 |
| Off-diagonal RMS — fitted before projection | 0.04828 [0.04165, 0.05385] | 0.04780 [0.04117, 0.05316] | 0.9794 | 0.0006125 |
| Off-diagonal kurtosis — median globally calibrated | 20.62 [4.409, 54.44] | 20.65 [5.523, 45.50] | 0.8345 | 8.220 |
| Participation ratio — fitted exactly | 45.70 [24.60, 52.48] | 45.70 [24.60, 52.48] | 1.0000 | $9.2\times10^{-12}$ |
| Top-5% symmetry score — predicted | 0.8037 [0.6761, 0.9066] | 0.8364 [0.7401, 0.9137] | 0.8897 | 0.04394 |

For completeness, the fitted diagonal summaries and the partly constrained reciprocal energy give:

| Statistic | Measured median [P10, P90] | Predicted median [P10, P90] | $r$ |
|---|---:|---:|---:|
| Weighted diagonal mean | 0.003374 [−0.1920, 0.2429] | 0.002123 [−0.1914, 0.2432] | 0.9994 |
| Weighted diagonal standard deviation | 0.09244 [0.05729, 0.2464] | 0.09330 [0.05694, 0.2257] | 0.9949 |
| $q$ | 0.007278 [−0.02919, 0.03408] | 0.003623 [−0.03409, 0.03924] | 0.9380 |

The agreement of the central error level is not obtained by pooling a successful negative-sign population with a failing positive-sign population:

| Actual sign group | Heads | Actual error median [P10, P90] | Predicted error median [P10, P90] | $r$ |
|---|---:|---:|---:|---:|
| $a>b$ | 44 | 0.04640 [0.03487, 0.16090] | 0.04900 [0.03949, 0.16868] | 0.9097 |
| $a<b$ | 100 | 0.06253 [0.03894, 0.14673] | 0.06184 [0.03826, 0.12588] | 0.9065 |

There are 48 positive predictive means versus 44 positive actual heads. The sign agrees on 130 heads: 39/44 actual positive heads and 91/100 actual negative heads. This is descriptive prediction using overlap fitting summaries; it is not an independent sign forecast from training metadata.

The median Monte Carlo standard error of a head's predicted relation-(1) error is 0.000744; the maximum is 0.00679. The Monte Carlo uncertainty is much smaller than the largest model discrepancies.

**6. Failures, worst heads, and falsification.**

The following are the largest absolute relation-(1) error discrepancies, with zero-based head labels:

| Head | Actual error | Predicted error | Actual $a-b$ | Predicted $a-b$ |
|---|---:|---:|---:|---:|
| L0H7 | 0.3623 | 0.1946 | 0.1414 | 0.07463 |
| L0H9 | 0.3262 | 0.1806 | −0.1095 | −0.09672 |
| L0H3 | 0.3811 | 0.2445 | 0.1950 | 0.1334 |
| L0H4 | 0.3297 | 0.2031 | 0.1609 | 0.1181 |
| L5H9 | 0.4407 | 0.3172 | −0.2544 | −0.2160 |
| L0H5 | 0.1989 | 0.1130 | −0.02316 | −0.01805 |
| L1H9 | 0.02181 | 0.1066 | −0.01328 | −0.08303 |
| L1H2 | 0.05823 | 0.1336 | −0.01241 | 0.02389 |

Other material failures are:

* **Mixed-sign profile mass:** the median $\min(c,d)$ is too small by a factor of about 7.6; its P90 is too small by about 43%. For L0H7 the prediction is 0.01598 versus 0.03404, and for L4H11 it is $4.0\times10^{-5}$ versus 0.007272.
* **Diagonal share:** L1H4 is predicted at 0.5824 versus 0.2189; L0H7 at 0.7271 versus 0.4029. The one-slope diagonal law transfers poorly between the measured and quantile spectra in some heads.
* **Extreme directional profile:** L0H9 has predicted $c-d=-0.3041$ versus −0.4280; L0H5 has 0.7480 versus 0.8216.
* **Tail variation:** L11H10 has predicted overlap kurtosis 83.10 versus 135.25; L0H10 has 157.24 versus 111.71. One shared impulse count does not explain all tail variation.
* **Contraction effects:** projection activates in 45.6% of all draws. The median, across heads, of mean relative squared projection correction is only 0.000227, but some extreme heads are projected on every draw. Their locally important moments change appreciably. For L0H7, predicted $q=-0.09738$ versus −0.16595 measured.

The plug-in 90% simulation intervals cover the actual relation-(1) error on only **68.1%** of heads, diagonal share on **55.6%**, and $\min(c,d)$ on **58.3%**. These intervals omit parameter uncertainty, so they are not a formal hypothesis test with a calibrated null distribution. Nevertheless, the discrepancies are too systematic to describe the ensemble as a satisfactory model of every head.

As a diagnostic, I reran the final overlap sampler with the **actual 64 singular values** of each head, using 64 draws per head. This is not the low-parameter candidate. Its error median is 0.06071, correlation 0.9023, and MAE 0.01793, compared with 0.05923, 0.9052, and 0.01846 for the complete candidate. Supplying the actual spectrum therefore does not remove the principal error discrepancy. It improves $a-b$ MAE from 0.00944 to 0.00725, but diagonal share and $\min(c,d)$ remain biased.

The ensemble is already falsified as an accurate conditional distribution for all these heads at the reported level of resolution. As a rough descriptive family, it has the following further falsifiers:

1. On an independent model or reserved layers, fit only the eight stated summaries and fix the shared constants in advance. Persistent errors in the relation-(1) scale, sign frequency, or interval coverage would reject its generality. The present global calibration is not such a validation.
2. Test the assumption that the sparse pair-location probabilities depend only on the product $\sigma_i\sigma_j$. Residual dependence on the gap $|i-j|$, channel communities, or the two ranks separately would reject that localization law.
3. Test the Gaussian affine diagonal law conditional on singular-value size. The present diagonal-share and $\min(c,d)$ failures already indicate that one mean slope and one residual variance are insufficient in some heads.
4. Test the “few skew impulses plus Gaussian backgrounds” distribution using tail fractions other than the calibrated kurtosis. Its top-5% symmetry score is already systematically high. Matching a single fourth moment cannot validate its tail law.

The clearest next mathematical constraint is that a better sampler needs **jointly realizable overlap moments**, especially in the large singular directions, so that enforcing contraction does not erase the fitted reciprocal energy. Adding an error-scale multiplier would not address this failure.

**7. Reproducibility and numerical checks.**

The final tested sampler is `ensemble.py --variant shot`; the other variants in that script are exploratory controls. Files in this workspace include:

* `extract.py`, `heads.npz`, `actual.csv`: raw-head extraction and measurements.
* `ensemble.py`: fitting and sampling, with the exact implementation of the contraction projection.
* `final_parameters.csv`, `final_predictions.csv`, `final_summary.json`: eight-parameter fit and 128-draw evaluation. The parameter CSV also includes `chi`, a redundant diagnostic not used by the selected sampler.
* `calibrate.py`, `calibration.json`: shared-constant calibration from overlap statistics; its pilot inputs are `shot8_predictions.csv` and `shot_predictions.csv`.
* `ablations.py`, `fourth_moments.csv`, `ablation_predictions.csv`: independent symmetric/skew and tail diagnostics.
* `validate.py`, `validation.json`: direct matrix and realization checks.
* `summarize.py`, `tables.md`, `diagnostic_summary.json`: tables, sign counts, worst heads, and Monte Carlo precision.
* `final_conditional_predictions.csv`, `final_conditional_summary.json`: the actual-spectrum diagnostic, kept separate from the complete ensemble.

With `PY` denoting the user-supplied Python executable, the main evaluation commands are:

```sh
"$PY" -I extract.py
heavy-run --workers 8 --label final-shot-ensemble -- "$PY" -I ensemble.py \
  --R 128 --variant shot --p .004464285714285714 \
  --alpha .53996028 --seed 571133 --label final
"$PY" -I validate.py
"$PY" -I summarize.py
```

Here `--p` is converted to the impulse count by `round(p*2016)` in the selected variant, giving $m=9$. Random seeds are deterministic functions of the base seed and head index. Each process pool reads `HEAVY_MAX_WORKERS` and uses `maxtasksperchild=1`.

Checks completed:

* The compressed profile calculation agreed with independent direct $768\times768$ calculations on five selected actual heads to $2.7\times10^{-15}$.
* Explicit generated $Q,K$ agreed with their compressed profiles on four selected draws to $1.5\times10^{-15}$; orthonormal-frame and overlap errors were below $1.0\times10^{-14}$.
* The two-mode positive/negative sign examples agreed with the stated formulas.
* The maximum absolute log-mean residual from R5 on the 144 actual heads was $5.2\times10^{-13}$.

All worker-pool jobs were invoked through the requested `heavy-run --workers 8` wrapper and were sequential within this session. The wrapper reported that the shared `/tmp` lock was unwritable under this session's filesystem sandbox and ran without that lock, while retaining the worker cap. I did not alter the shared wrapper or any project files.

The report and all final checks were completed within the 40-minute bound. This is a completed, qualified report of a candidate that explains several central statistics and has explicit remaining failures, rather than a claimed solution for all heads.
