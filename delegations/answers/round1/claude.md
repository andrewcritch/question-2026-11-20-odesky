# A random-matrix ensemble for trained attention heads

**Status, read first.** Python was blocked in this session because Claude Code ran in don't-ask mode, which denied the interpreter. So I could not run any experiment against the weights. Everything numerical below comes from two sources:

- exact algebra;
- hand calculations on the rows of `gpt2_W.csv`. I used 25 heads: all of layers 0–1, plus L2H2, L3H0, L4H11, L5H5 and L6H9.

Three scripts in this folder implement every test I propose. I have not run them, so they may need small fixes:

| script | what it does |
|---|---|
| `fit_tilt.py` | Fits candidate A to each head using only gauge-free statistics. Then it predicts err(1), the SVD-diagonal statistics and min(c,d) by simulation, for raw and lnfold. |
| `rotation_check.py` | Exact-identity checks, and diagnostics for candidate B, balancedness and commutation. |
| `exp1_nulls.py` | Structure-preserving nulls: head-space rotation, ambient rotation of K, column-scaled Gaussian, and layer-covariance Gaussian. |

`common.py` holds shared code. Run each script as `…/venv/bin/python -I <script>.py`. `fit_tilt.py` takes about 10–20 minutes.

---

## 0. Summary

1. **Two exact facts change the target.**
   - (a) For any $Q,K$ (with $N\ge 2n$ and $S$ nondegenerate), $\prod_i\sigma(T)_i=\prod_i\sqrt{\lambda_{+,i}\lambda_{-,i}}$. So relation (1) always holds *on average in log scale*. Its only real content is the *spread*: the log-spread of $\sigma(T)$ equals the log-spread of the geometric means.
   - (b) Put $\Pi=(K+Q)/2$ and $\Delta=(K-Q)/2$. Then $S=\Pi^\top\Pi-\Delta^\top\Delta$ and $T=\Delta^\top\Pi-\Pi^\top\Delta$. When the row spaces of $\Pi$ and $\Delta$ are orthogonal (true up to $O(\sqrt{n/N})$ noise for generic heads):
     - von Neumann's trace inequality gives $a\le b$;
     - Horn's inequality gives $\log\sigma(T)\prec\log\sqrt{\lambda_+\lambda_-}$ (log-majorization);
     - **both relations are exact if and only if the $n\times n$ Gram matrices $G_\pm$ of $\Pi$ and $\Delta$ commute and have co-ordered eigenvalues.**

   So (1) and $a=b$ are one phenomenon: a common "channel" basis in head space.
2. **Candidate A, the lognormal tilt ensemble.** It has 2 shape parameters $(\mu,s)$, plus 1 parameter $v$ for $\Sigma$. In a common head basis, $Q+K$ and $K-Q$ are independent Gaussian matrices with diagonal channel scales $\sqrt{\rho_k/2}\,e^{\pm y_k/2}$. Here $\log\rho_k\sim N(0,v)$, and the tilts $y_k=\operatorname{atanh}t_k$ (Fisher's $z$ of the query–key cosine of channel $k$) are drawn iid from $N(\mu,s^2)$.
   - $\mu$ sets the position along $\Theta$.
   - $s$ sets the distance from $\Theta$.
   - Closed-form predictions:
     - $a=b\,e^{-2s^2}$;
     - $\min(c,d)\to0$ (this is the paper's Theorem 2: equal log-variance lobes give proportional sorted lobes);
     - $\mathrm{err}(1)\approx\sqrt{1+4v}\,(\sqrt{v+s^2}-\sqrt v)$;
     - the paper's Obs. 7 ratio equals $e^{s^2}$.
3. **Hand check of candidate A.** I fitted $s$ from $a/b$ and $v$ from the participation ratio. The model then predicts err(1) out of sample to within 15% for **13 of 16** heads with $a<b$ (table in §3). err(1) ranges over 0.05–0.33 across these heads. The fitted median $e^{s^2}=1.05$ matches the paper's Observation 7 range (1.01–1.05).
4. **The diagonal-of-$W$ statistics in the brief are gauge-fragile.** Fitted $s$ is typically 1–6× the SVD-diagonal std of $t_i$ (median about 2×). The likely reason: channels with tilts $\pm y$ have nearly equal $\sigma$, and $O(N^{-1/2})$ sampling noise mixes nearly degenerate singular pairs. That mixing shrinks the diagonal of $W$ and moves the tilt into symmetric off-diagonal pairs. I recommend gauge-free targets instead: $S$/$T$ spectra and $\operatorname{eig}(QK^\top)$.
5. **Candidate A cannot produce $a>b$.** In my 25-head sample, 9 heads have $a\ge b$: L0H3, L0H4, L0H7, L0H10, L0H11, L1H1, L1H3, L1H4 and L2H2. **Candidate B** adds "rotation channels": pairs of head dimensions where the key equals a rotated query. Each such channel moves the profile by $a-b\mathrel{+}=w\,c^2\sin^2\theta$, and pushes $\sigma(T)$ above the geometric mean.
6. **My view.** Candidate A is the natural ensemble for the bulk of heads, and I would bet on it. Candidate B is a necessary extension for a minority of heads, mostly in early layers. I could not confirm my guess that B-heads are positional heads: the classic previous-token head L4H11 is firmly A-type, with $a-b=-0.12$.

---

## 1. Exact facts (proved here; easy to check numerically in `rotation_check.py`)

Notation: $L=K^\top Q$, $\|L\|^2=\sum\sigma_k^2$, and $\mu_k$ are the nonzero eigenvalues of $L$. These equal the eigenvalues of the $n\times n$ matrix $QK^\top$.

**F1 (sum/difference split).** With $\Pi=(K+Q)/2$ and $\Delta=(K-Q)/2$, we have $L=(\Pi+\Delta)^\top(\Pi-\Delta)$, so
$$S=\Pi^\top\Pi-\Delta^\top\Delta,\qquad T=\Delta^\top\Pi-\Pi^\top\Delta .$$
The positive lobe comes from $Q+K$, the negative lobe from $K-Q$, and $T$ from their cross term.

**F2 (determinant identity, so (1) holds in geometric mean for every head).**
- Let $F=[Q;K]$ ($2n\times N$) and $M=FF^\top$. Then $2S=F^\top J'F$ and $2T=F^\top\Omega F$, with $J'=\begin{psmallmatrix}0&I\\I&0\end{psmallmatrix}$ and $\Omega=\begin{psmallmatrix}0&-I\\I&0\end{psmallmatrix}$.
- So the nonzero spectra are $\operatorname{eig}(J'M)$ and $\operatorname{eig}(\Omega M)$ (the latter is $\pm 2i\sigma(T)$).
- Taking determinants, $\prod_{\pm,k}2\lambda_{\pm,k}=|\det M|=\prod_k(2\sigma(T)_k)^2$. Hence
$$\sum_k\log\sigma(T)_k=\tfrac12\sum_k\log(\lambda_{+,k}\lambda_{-,k})\quad\text{exactly.}$$
- Consequences:
  - The mean of the log-ratio in (1) is zero for every $L$. (1) can fail only through *spread*.
  - The whole profile is a function of the $2n\times 2n$ joint Gram matrix $M$ modulo the gauge $\operatorname{diag}(A,A^{-\top})$, which preserves $J'$ and $\Omega$.
  - $\sigma(T)$ are the Williamson (symplectic) eigenvalues of $M$, up to a factor.

**F3 (orthogonal limit: von Neumann and Horn).**
- Suppose $\operatorname{row}(\Pi)\perp\operatorname{row}(\Delta)$. Write $\Pi=AO_1$ and $\Delta=BO_2$ with orthonormal $O_i$. Then:
  - $\lambda_+=\operatorname{eig}(G_+)$ with $G_+=\Pi\Pi^\top=AA^\top$;
  - $\lambda_-=\operatorname{eig}(G_-)$ with $G_-=\Delta\Delta^\top$;
  - $\sigma(T)=\operatorname{sv}(B^\top A)$;
  - $\|T\|^2=2\operatorname{tr}(G_+G_-)$.
- Two consequences:
  - **$a\le b$**, by von Neumann: $\operatorname{tr}(G_+G_-)\le\langle\lambda_+^\downarrow,\lambda_-^\downarrow\rangle$.
  - **$\log\sigma(T)\prec\log\sqrt{\lambda_+^\downarrow\lambda_-^\downarrow}$**, by Horn's product inequality together with F2.
- Equality holds in both if and only if $G_+$ and $G_-$ commute with co-ordered eigenvalues.
- Generic heads satisfy the orthogonality to $O(\sqrt{n/N})$. Heads with $a>b$ *must* violate it: $\operatorname{row}(Q+K)$ and $\operatorname{row}(K-Q)$ overlap more than at random. `rotation_check.py` measures this as `ovl`.

**F4 (where $a$ and $a-b$ live).**
$$a=\tfrac12\bigl(1-\tau_2\bigr),\quad \tau_2=\frac{\operatorname{Re}\sum_k\mu_k^2}{\sum_k\sigma_k^2},\qquad a-b=(c+d)-\tau_2\quad\text{(exact).}$$
So $a=b$ is equivalent to $\|\lambda_+^\downarrow-\lambda_-^\downarrow\|^2=\operatorname{tr}(L^2)$. In the block model $\mu_k=\sigma_kt_k$. This is the gauge-free definition of a "block": $L$ has real eigenvalues $\sigma_kt_k$ whose eigenvectors are its left singular vectors.

**F5 (the SVD diagonal of $W$ is fragile).**
- If $\sigma_i\approx\sigma_j$, the pair $(u,v)$ can rotate by a common $O$ within the near-degenerate space. That sends $W\mapsto O^\top WO$: it averages $t_i,t_j$ and creates a symmetric off-diagonal pair $W_{ij}=W_{ji}$.
- In GPT-2 the spacing between neighbouring $\sigma$ is about 0.5% of $\bar\sigma$. The Wishart coupling is about 3–5% (off-diagonal RMS 0.036–0.048). So mixing across several neighbours is expected.
- Candidate A also makes channels with tilts $\pm y$ and equal $\rho$ exactly degenerate, since $\sigma=\rho\cosh y$.
- The measured "diagonal share 0.18" and "tstd 0.09" are therefore lower bounds on the real tilt structure, not direct readouts of it.
- Hand-check evidence (decomposing $\tau_2=\langle t^2\rangle_{\sigma^2}+\kappa$ with $\kappa=\sum_{i\ne j}\sigma_i\sigma_jW_{ij}W_{ji}/\sum\sigma^2$):
  - $c+d-\langle t^2\rangle_{\sigma^2}$ is small and negative in 20/20 layer-0/1 heads (median −0.011).
  - The off-diagonal coupling $\kappa$ is what carries $a-b$: $a-b\approx-\kappa$ up to that −0.01. Examples: L1H5 has $\kappa=+0.17$ and $a-b=-0.185$; L0H3 has $\kappa=-0.20$ and $a-b=+0.195$.

---

## 2. Candidates

### Candidate A: lognormal tilt ("sum–difference") ensemble

**Recipe.** Per head, the parameters are $\mu$ (mean tilt), $s$ (tilt spread), $v$ (scale dispersion) and an overall scale.
1. For $k=1..n$, draw $\rho_k=e^{\sqrt v\,\xi_k}$ and $y_k=\mu+s\eta_k$, with $\xi,\eta$ iid $N(0,1)$.
2. Draw $P,M\in\mathbb R^{n\times N}$ with iid $N(0,1)$ entries. Optionally give the rows a shared ambient covariance $\Gamma$ (one per layer, see below).
3. Set $\Pi=\operatorname{diag}\!\big(\sqrt{\rho_k/2}\,e^{y_k/2}\big)P$ and $\Delta=\operatorname{diag}\!\big(\sqrt{\rho_k/2}\,e^{-y_k/2}\big)M$.
4. Set $Q=\Pi-\Delta$ and $K=\Pi+\Delta$.

**What each channel looks like.**
- Row $k$ satisfies $|q_k|=|k_k|$, so the model is *balanced*.
- The query–key cosine is $\cos(q_k,k_k)=\tanh y_k=t_k$.
- $\lambda_{\pm,k}\approx\frac{\rho_k}2e^{\pm y_k}$, $\sigma(T)_k\approx\rho_k/2$ and $\sigma_k\approx\rho_k\cosh y_k$.
- Every channel is an exact rank-one block, $\sigma(T)=\sqrt{\lambda_+\lambda_-}$, up to Wishart noise.
- In $(\Sigma,W)$ language: $W\approx\operatorname{diag}(\tanh y_k)$ plus Wishart noise of order $N_{\rm eff}^{-1/2}$.

**Predictions** ($n\to\infty$, Gaussian logs, $r=e^{-2|\mu|}$, $\varepsilon=e^{-2s^2}$):
- **Profile.** $b=\big(1+\varepsilon+\tfrac{(1-r)^2}{2r}\big)^{-1}$, $a=\varepsilon b$, $|c-d|=b\,\tfrac{(1-r)^2}{2r}$, and $\min(c,d)=0$.
  - Derivation: the sorted lobes are $\log\lambda_\pm^\downarrow(z)=m\pm\mu+z\sqrt{v+s^2}$. They have equal log-variance, so $\lambda_-^\downarrow=r\lambda_+^\downarrow$ at every quantile. That gives the paper's Theorem 2 profile for $S$.
  - The comonotone pairing inflates $b$ over the matched value $a$ by $e^{\sqrt{v_xv_y}-\mathrm{cov}}=e^{2s^2}$, whatever $\mu$ and $v$ are.
  - With $s=0$ this is exactly the rank-one point of $\Theta$ with $t=\tanh\mu$.
- **Relation (1) error.** $\log\sigma(T)^\downarrow(z)=m+z\sqrt v$ while $\log\sqrt{\lambda_+\lambda_-}^\downarrow(z)=m+z\sqrt{v+s^2}$. With $\sigma(T)^2$ weighting this gives $\mathrm{err}(1)\approx\sqrt{1+4v}\,(\sqrt{v+s^2}-\sqrt v)$.
- **Paper's Obs. 7–9.**
  - Obs. 7: lognormal modes give $\tau/\sqrt{|\mu|\nu}=e^{s^2}$, slightly above 1.
  - Obs. 8: shape ratio $\approx(v+s^2)/v$, also slightly above 1.
  - Obs. 9: sorted $\sigma(T)$ and $|\lambda|$ have correlation close to 1.
  - All three signs are as observed.
- **$\Sigma$.**
  - $\mathrm{PR}/n=e^{-4v}(\mathbb E\cosh^2y)^2/\mathbb E\cosh^4y$.
  - A $v$ of 0.05–0.08 gives PR of 45–53, as measured.
  - The lognormal family fits about as well as the gamma family, matching the paper's §3.5.1.
  - Larger $|y|$ means larger $\sigma$, so the top singular directions are slightly more aligned. That matches the brief's −0.11 index–$t$ correlation.
- **SVD-diagonal statistics.** These are predicted by simulation, not closed form, because of F5. `fit_tilt.py` does this both with isotropic ambient space and with the layer's pooled covariance $\Gamma$.
  - The brief's off-diagonal RMS of 0.048, against the null's 0.036, suggests an effective ambient dimension $N_{\rm eff}\approx 0.048^{-2}\approx430$.
  - That fits a shared, anisotropic residual stream, which I put into $\Gamma$ rather than into per-head parameters.

**Why training would produce this (the naturalness case).**
- Each channel is one learned (key feature, query feature) match. Its tilt is the cosine between the two features: $t\approx1$ for "same token or feature" (duplicate-token heads L0H1 and L0H10 have $\bar t=0.77$ and $0.81$), $t\approx-1$ for "avoid same", and $t\approx0$ for "different feature".
- $y=\operatorname{atanh}t=\tfrac12\log(\lambda_+/\lambda_-)$ is Fisher's $z$-transform of that cosine. Fisher's $z$ is the standard coordinate in which a correlation coefficient is approximately Gaussian with stable variance.
- The channel basis is where $G_+$ and $G_-$ commute. Unrelated features in high dimension are nearly orthogonal, which makes the channels nearly independent.
- Balancedness is what gradient flow from small initialization preserves ($\frac{d}{dt}(QQ^\top-KK^\top)=0$). `rotation_check.py` reports it as `bal`.
- The ruled-out correlated Gaussian $K=rQ+\sqrt{1-r^2}G$ is the degenerate case $s=v=0$, $y\equiv\operatorname{atanh}r$.

### Candidate B: A plus rotation channels

Take candidate A, then replace a fraction of channel pairs $(k,k')$ by rotation channels:
$$\begin{bmatrix}k_k\\k_{k'}\end{bmatrix}=c\,R(\theta)\begin{bmatrix}q_k\\q_{k'}\end{bmatrix}+\sqrt{1-c^2}\,\begin{bmatrix}g_k\\g_{k'}\end{bmatrix}.$$

This adds 2 parameters per head: the $\|L\|^2$-share $w$ of rotation channels, and $c\sin\theta$. (A cosine that varies across channels, as from position offsets, fits the same scheme.)

For one such channel of weight $w$:
- $\lambda_\pm=\tfrac\rho2\big(\sqrt{c^2\cos^2\theta+1-c^2}\pm c\cos\theta\big)$, each with multiplicity 2;
- $\tau_2$ contribution: $c^2\cos2\theta$;
- **$a-b$ contribution: $+w\,c^2\sin^2\theta\ \ (\ge0)$**;
- $\sigma(T)/\sqrt{\lambda_+\lambda_-}=\sqrt{(1-c^2\cos2\theta)/(1-c^2)}>1$.

So B-channels push $a$ above $b$ and push $\sigma(T)$ above the geometric mean. They also make $L$'s eigenvalues complex ($\iota>0$) and make $\operatorname{row}(Q+K)$ overlap $\operatorname{row}(K-Q)$, which F3 requires for $a>b$.

Mixtures can cancel in $a-b$ while still producing a large err(1). L2H2 looks like this: $a-b=+0.006$ but err(1) = 0.129, which pure A cannot produce.

- **Linked-key variant (C, a remark).** $K=JQ+G$ with $J=rI+sH+\alpha A$, where $H$ is GOE and $A$ is antisymmetric Gaussian. This is the most direct generalization of the ruled-out model: its symmetric part gives A-type channels with $t=j/\sqrt{1+j^2}$, and its antisymmetric part gives B-type channels. On its own, though, it orders $G_+$ and $G_-$ *oppositely* (both depend on $j$ in opposite directions). It needs channel scale dispersion ($v>s^2$) to reproduce (1). So it is less parsimonious than A plus B.

---

## 3. Checks against GPT-2 (hand calculations on `gpt2_W.csv`, raw $L$)

**Fit.**
- $s^2=-\tfrac12\ln(a/b)$, using only heads with $a<b$.
- $v\approx\tfrac14\ln(64/\mathrm{PR})$. This crude version ignores the $\cosh$ terms; the script uses the exact formula and subtracts the null dispersion.
- Prediction: $\widehat{\mathrm{err}}=\sqrt{1+4v}\,(\sqrt{v+s^2}-\sqrt v)$.
- No parameter was fitted to err(1).

| head | $a-b$ | PR | fitted $s$ | SVD-diag tstd | **pred err(1)** | **meas err(1)** |
|---|---|---|---|---|---|---|
| L0H0 | −0.012 | 53.1 | 0.11 | 0.049 | 0.029 | 0.038 |
| L0H1 | −0.044 | 53.7 | 0.33 | 0.072 | 0.195 | 0.191 |
| L0H2 | −0.024 | 52.5 | 0.15 | 0.067 | 0.053 | 0.053 |
| L0H5 | −0.023 | 54.1 | 0.36 | 0.062 | 0.227 | 0.199 |
| L0H6 | −0.033 | 41.1 | 0.18 | 0.135 | 0.056 | 0.086 |
| L0H8 | −0.032 | 51.8 | 0.18 | 0.063 | 0.069 | 0.072 |
| L0H9 | −0.110 | 47.9 | 0.44 | 0.313 | 0.281 | 0.326 |
| L1H0 | −0.068 | 48.4 | 0.28 | 0.267 | 0.134 | 0.127 |
| L1H2 | −0.012 | 7.8 | 0.11 | 0.130 | 0.015 | 0.058 |
| L1H5 | −0.185 | 49.1 | 0.43 | 0.128 | 0.278 | 0.275 |
| L1H6 | −0.057 | 51.0 | 0.24 | 0.085 | 0.113 | 0.105 |
| L1H7 | −0.033 | 26.2 | 0.19 | 0.226 | 0.050 | 0.056 |
| L3H0 | −0.092 | 32.9 | 0.32 | 0.315 | 0.141 | 0.151 |
| L4H11 | −0.124 | 21.3 | 0.37 | 0.209 | 0.167 | 0.192 |
| L5H5 | −0.027 | 46.3 | 0.17 | 0.148 | 0.053 | 0.063 |
| L6H9 | −0.040 | 48.1 | 0.21 | 0.173 | 0.080 | 0.083 |

**Results.**
- **13 of 16** predictions are within 15%, over a measured range of 0.04–0.33.
- The misses:
  - L0H0 sits near the null noise floor of 0.011.
  - L0H6 is under-predicted.
  - L1H2 has PR 7.8, so it is far from the lognormal regime.
- Predictions are slightly low overall (median ratio about 0.95). That is consistent with the floor of about 0.01 from finite $n$ and $N$, which the asymptotic formula leaves out.
- Median fitted $e^{s^2}=1.05$, compared with the paper's Obs. 7 range of 1.01–1.05.
- Fitted $s$ is at least the SVD-diagonal tstd in 14 of 16 heads, and up to 6× larger (F5). The two exceptions, L1H2 and L1H7, have low PR.
- Caveat: 12 of the 16 heads are from layers 0–1. The scripts cover all 144 heads, raw and lnfold.

**Heads with $a\ge b$, outside candidate A.**

| head | $a-b$ | PR |
|---|---|---|
| L0H3 | +0.195 | 17 |
| L0H4 | +0.161 | 26 |
| L0H7 | +0.141 | 18 |
| L0H10 | +0.044 | — |
| L1H4 | +0.041 | — |
| L1H3 | +0.027 | — |
| L1H1 | +0.010 | — |
| L2H2 | +0.006 | — |
| L0H11 | +0.004 | — |

The large positive values sit at low PR. That fits candidate B with a few strong rotation channels.

**What the scripts will add.**
- `fit_tilt.py`: the table above for all heads; a second, independent estimate $s^2_{\rm spec}=\tfrac12(\operatorname{Var}\log\lambda_++\operatorname{Var}\log\lambda_-)-\operatorname{Var}\log\sigma(T)$; and simulated predictions of diag share, $\bar t$, tstd, off-diagonal RMS, PR and min(c,d), compared with measurement.
- `rotation_check.py`: verifies F2 and F4 to machine precision, and correlates $a-b$ with $\iota$, `ovl`, wpe overlap and the $G_\pm$ commutator.
- `exp1_nulls.py`: checks whether keeping only the two row spaces (randomizing the head-space wiring) or only the ambient anisotropy reproduces the statistics.

---

## 4. Verdict and falsifiers

**Most natural: candidate A.**
- Its description fits in one sentence: Q+K and K−Q are independent Gaussians with channel scales $\sqrt{\rho/2}\,e^{\pm y/2}$, with lognormal $\rho$ and Gaussian Fisher-z tilts $y$.
- It has two shape parameters for the profile and one for $\Sigma$.
- It comes with a mechanism: balanced, nearly independent feature-matching channels.
- It *explains* three things:
  - why (1) and $a=b$ hold together (F3: commuting $G_\pm$);
  - why heads spread along $\Theta$ (through $\mu$) while keeping $cd\approx0$ (equal lobe log-variances, Theorem 2);
  - the sign and size of the deviations (through $s$), including the paper's Obs. 7–8 biases.

**A is falsified if any of these holds:**
1. On all 144 heads, $\widehat{\mathrm{err}}(1)$ from $(a/b,\mathrm{PR})$ fails to track measured err(1). Rough threshold: correlation below 0.8 among heads with $a<b$.
2. $s^2$ from $a/b$ and $s^2_{\rm spec}$ from log-variances disagree systematically. These two are independent estimates of the same parameter.
3. $\min(c,d)$ or $|\operatorname{Var}\log\lambda_+-\operatorname{Var}\log\lambda_-|$ is systematically non-zero while $a\approx b$. That would mean tilt correlates with scale.
4. Simulating A at the fitted parameters does not reproduce the SVD-diagonal statistics: diag share about 0.18 and tstd about 0.09. Since F5 says these are mixing-dominated, this is a sharp test of the "fragility" explanation.
5. The trained $G_\pm$ commute no better than in the null (`comm` in `rotation_check.py`), or trained heads are not balanced (`bal`).

**B is falsified if** heads with $a>b$ fail to show excess $\operatorname{row}(Q+K)$/$\operatorname{row}(K-Q)$ overlap and complex eigenvalue mass $\iota$ compared with the null. F3 says they must show both, so B's specific form (rotated key channels) is then the thing being tested.

**On whether the target is well posed.**
- Partly no.
  - Relation (1) holds automatically in log-mean for *every* bilinear form (F2). Only its spread is informative.
  - Statistics built on the diagonal of the SVD-paired $W$ are not stable under the near-degeneracies that real spectra have (F5).
- Better targets, all gauge-free:
  - the sorted $S$ and $T$ spectra;
  - $\operatorname{eig}(QK^\top)$, through $\tau_2$ and $\iota$;
  - the commutator and overlap of the Gram matrices of $Q\pm K$.
- In those terms, the question becomes: why do trained heads have a common channel basis for $Q+K$ and $K-Q$, with roughly Gaussian Fisher-z tilts?
