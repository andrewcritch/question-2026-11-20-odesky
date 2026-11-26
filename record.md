# Project record

This file is the project record. A claim counts as recorded here and nowhere else. Name, for each recorded claim, where its proof or its numerical evidence was checked.

## R1. Complete invariant in the SVD gauge

Let $L=K^\top Q$ have rank $n$, with SVD $L=U\Sigma V^\top$ ($U,V\in\mathbb R^{N\times n}$ with orthonormal columns), and set $W=U^\top V$. For $N\ge 2n$, the pair $(\Sigma,W)$ determines $L$ up to orthogonal congruence $L\mapsto OLO^\top$, modulo the residual SVD ambiguity $W\mapsto P^\top WP$ ($P$ in the stabilizer of $\Sigma$).

Checked: by hand by the supervising agent. Two $n$-frames in $\mathbb R^N$, $N\ge 2n$, are determined up to $O(N)$ by their Gram matrix $\begin{psmallmatrix}I&W\\W^\top&I\end{psmallmatrix}$, and every contraction $W$ is realized.

## R2. Block model gives exact relation (1) per block

If $W=\mathrm{diag}(t_1,\dots,t_n)$, then $L$ is a sum of the rank-one forms $\sigma_iu_iv_i^\top$ on the mutually orthogonal planes $\mathrm{span}(u_i,v_i)$. Block $i$ has $\lambda_{+}=\sigma_i(1+t_i)/2$, $\lambda_-=\sigma_i(1-t_i)/2$, and $\sigma(T)=\sigma_i\sqrt{1-t_i^2}/2=\sqrt{\lambda_+\lambda_-}$. If moreover all $t_i$ are equal to $t$, the profile equals the rank-one profile with parameter $t$, for every $\Sigma$.

Checked: by hand by the supervising agent. A real $2\times2$ matrix $M=S+T$ satisfies $\det M=\det S+\sigma(T)^2$, so $\sigma(T)^2=\lambda_+\lambda_-$ holds if and only if $\det M=0$.

## R3. GPT-2 small measurements (144 heads, raw $L=K^\top Q$)

Median [10th, 90th percentile]; Gaussian baseline in parentheses.

- Diagonal share of $\|W\|_F^2$: 0.18 [0.04, 0.55] (0.016).
- Within-head σ²-weighted std of $t_i$: 0.09 [0.06, 0.25] (0.036).
- Relative error of relation (1), per sorted index: 0.059 [0.04, 0.16] (0.011).
- $c-d$ matches $\sum\sigma_i^2t_i|t_i|/\sum\sigma_i^2$ with correlation 0.997.
- With LayerNorm gain and centering folded in, 20% of heads have $|a-b|>0.1$ (raw: 7.6%).

Checked: numerical, scratchpad scripts `gpt2_W.py` and `gpt2_more.py` (copies in the delegation brief folder), run by the supervising agent on 2026-11-24. One model only.

## R4. Exact energy identity and the sign obstruction for diagonal models (from Codex, round 1)

Write $F=\sum\sigma_i^2$, $W=D+E$ with $D=\mathrm{diag}(t_i)$ and $E_{ii}=0$, $m_2=\sum\sigma_i^2t_i^2/F$, and $q=\sum_{i\ne j}\sigma_i\sigma_jE_{ij}E_{ji}/F$. Then
$$a=\tfrac12(1-m_2-q),\qquad a-b=c+d-m_2-q .$$
If $W$ is diagonal, then $a\le b$ for every $\Sigma$ and every choice of $t_i$. Every diagonal-$W$ ensemble therefore has $a-b\le 0$.

Proof: $\mathrm{tr}(L^2)=\mathrm{tr}(\Sigma W\Sigma W)$ (transpose and cyclicity) $=F(m_2+q)$, and $a=\tfrac12-\mathrm{tr}(L^2)/(2F)$ (paper, Lemma 5). For diagonal $W$, put $p_i=\sigma_i(1+t_i)/2$ and $r_i=\sigma_i(1-t_i)/2$. Then $aF=\sum\sigma_i^2(1-t_i^2)/2=2\sum p_ir_i$, and $bF=2\langle p^\downarrow,r^\downarrow\rangle\ge 2\sum p_ir_i$ by the rearrangement inequality.

Checked: proof by hand by the supervising agent. Numerical check by the supervising agent (`delegations/round1_brief/check_codex.py`): the identity holds to $3\times10^{-16}$ on all 144 GPT-2 heads; 0 of 144 diagonal surrogates have $a-b>0$; 44 of 144 raw GPT-2 heads have $a-b>0$; $\mathrm{corr}(q,a-b)=-0.968$.

Consequence: about 30% of raw GPT-2 heads cannot come from any diagonal-$W$ model. A successful ensemble needs negative spectrally weighted reciprocal overlap $q$ in those heads.

## R5. Determinant identity: relation (1) holds exactly in log-mean for every head (from Claude node, round 1)

If the stacked map $F=[Q;K]:\mathbb R^N\to\mathbb R^{2n}$ is surjective, then
$$\sum_{i=1}^n\log\sigma(T)_i=\tfrac12\sum_{i=1}^n\log(\lambda_{+,i}\lambda_{-,i}).$$
Relation (1) can therefore fail only through the spread of the log-ratios, never through their mean.

Proof: put $M=FF^\top$ (positive definite), $J'=\begin{psmallmatrix}0&I\\I&0\end{psmallmatrix}$ and $\Omega=\begin{psmallmatrix}0&-I\\I&0\end{psmallmatrix}$. Then $2S=F^\top J'F$ and $2T=F^\top\Omega F$, so the nonzero spectra of $2S$ and $2T$ are the spectra of $J'M$ and $\Omega M$. Since $|\det J'|=\det\Omega=1$, $\prod_i(2\lambda_{+,i})(2\lambda_{-,i})=\det M=\prod_i(2\sigma(T)_i)^2$.

Checked: proof by hand by the supervising agent. Numerical check on all 144 GPT-2 heads (`claude_scripts/rotation_check.py`, run by the supervising agent): maximum deviation $2\times10^{-13}$.

## R6. Diagnostics for heads with $a>b$ (round 1, numerical)

From `claude_scripts/rotation_check.py`, run by the supervising agent on GPT-2 raw $L$; median [10th, 90th] trained versus Gaussian baseline:

- $\iota$ (complex-eigenvalue mass of $L$): 0.029 [0.011, 0.054] versus 0.020; correlation with $a-b$ is +0.74 (Spearman +0.78).
- `ovl` (overlap of row spaces of $Q+K$ and $K-Q$): 0.134 versus 0.086; Spearman with $a-b$ +0.44.
- `comm` (normalized commutator of the Gram matrices $G_\pm$ of $Q\pm K$): 0.167 versus 0.175 null. Trained heads do not commute better than the null by this measure.
- `bal` (balance between $QQ^\top$ and $KK^\top$): 0.228 versus 0.207 null. Trained heads are not more balanced than the null by this measure.
- The three layer-0 heads with the largest $a-b$ (L0H3, L0H4, L0H7) have large overlap with the positional-embedding subspace (`pos` 0.21–0.29); L1H10 and L1H4 do not.

Status: these numbers are recorded; the definitions of `comm` and `bal` are the Claude node's, and the supervising agent has not yet checked that they measure what the Claude node's falsifier 5 intends.

## R7. Fit of candidate A ("lognormal tilt" ensemble) on GPT-2 (round 1, numerical)

Candidate A (Claude node): in a shared head-space channel basis, $Q+K=\mathrm{diag}(\sqrt{2\rho_k}\,e^{y_k/2})P$ and $K-Q=\mathrm{diag}(\sqrt{2\rho_k}\,e^{-y_k/2})M$, with $P,M$ independent Gaussian $n\times N$ matrices, $\log\rho_k\sim N(0,v)$, and $y_k\sim N(\mu,s^2)$ i.i.d. Parameters per head: $\mu,s,v$. Candidate A gives $a\le b$ up to Wishart noise, so it applies only to heads with $a<b$.

Fit: $s$ from $a/b$, $\mu$ from $(c+d)/b$, $v$ from the participation ratio. Matches in $a-b$, $c-d$, and PR are therefore fitted, not predicted. Run by the supervising agent (`claude_scripts/fit_tilt.py`, log `fit_tilt.log`), raw $L$, the 100 heads with $a<b$; medians [10th, 90th]:

| predicted statistic | measured | predicted (isotropic) | correlation across heads |
|---|---|---|---|
| relation-(1) error | 0.063 [0.039, 0.147] | 0.042 [0.017, 0.139] | 0.96 |
| diagonal share of $W$ | 0.208 [0.063, 0.535] | 0.244 [0.069, 0.539] | 0.93 |
| within-head std of $t_i$ | 0.103 [0.061, 0.222] | 0.067 [0.045, 0.119] | 0.65 |
| off-diagonal RMS of $W$ | 0.047 | 0.038 | 0.57 |

- Two independent estimates of $s^2$ (from $a/b$, and from log-variances of the three spectra) correlate at 0.82.
- Candidate A tracks the relation-(1) error across heads (0.96) but underestimates its level by about one third. Codex's candidate 2 shows the same underestimate (round 1 answer `codex.md`).
- LayerNorm-folded heads give similar correlations; 82 of 144 folded heads have $a>b$ and fall outside candidate A.

Null comparison (`exp1_nulls.log`): randomizing the head-space pairing while keeping the row spaces of $Q$ and $K$ ("headrot") drops the diagonal share from 0.208 to 0.020 and the relation-(1) error from 0.059 to 0.020. The structure lives in the head-space pairing of query and key rows, not in the row spaces alone.

Checked: numerical only; the supervising agent ran the scripts and read the fitting code (`fit` in `fit_tilt.py`) to confirm which statistics are fitted.

## R8. The off-diagonal part of $W$ is heavy-tailed, and its large pairs lean symmetric (from Grok, round 1)

On raw GPT-2 heads, the off-diagonal entries of $W$ have median kurtosis 20.6 (Gaussian: 3). Among the 5% largest pairs $(W_{ij},W_{ji})$ by $\max(|W_{ij}|,|W_{ji}|)$, the median of the mean symmetry score $|W_{ij}+W_{ji}|/(|W_{ij}|+|W_{ji}|)$ is 0.80 (1 means symmetric, 0 skew).

Grok reports these ablations, not yet re-run by the supervising agent: zeroing the off-diagonal of $W$ drops the median relation-(1) error from 0.059 to 0.026; replacing it with i.i.d. Gaussian noise of the same RMS also gives 0.026; flipping the signs of whole pairs keeps 0.057; independent random signs give 0.034. So the half of the relation-(1) error that diagonal-plus-Gaussian models miss lives in a few large, preferentially symmetric off-diagonal pairs.

Checked: kurtosis and symmetry score re-computed by the supervising agent (`delegations/round1_brief/check_grok.py`). The supervising agent has not computed a null value for the symmetry score.

**Correction (round 2, checked by the supervising agent with `check_r2.py`):** the symmetry score 0.80 is not evidence of symmetric pairs. Its Gaussian-baseline value (i.i.d. $64\times64$ matrix, 200 draws) is 0.789 [0.752, 0.821]. Do not read R8's top-5% score as "symmetric-leaning". The heavy tail is located and characterized in R11.

## R9. Signed-spike ensemble and the coupling of $t_i$ to $\sigma_i$ (from Antigravity, round 1)

Antigravity candidate 2 ("signed spike"), parameters $r_0\in(-1,1)$ and $\gamma\in\mathbb R$ per head, one global $N_{\rm eff}\approx430$: with $X_0,Y_0,F$ independent Gaussian $n\times N$ matrices (rows of covariance $\Gamma$) and $g\sim N(0,I_n)$,
$$Q=X_0+|\gamma|\,\mathrm{diag}(g)F,\qquad K=r_0X_0+\sqrt{1-r_0^2}\,Y_0+\gamma\,\mathrm{diag}(g)F.$$
Channel $i$ then has scale $s_i=1+\gamma^2g_i^2$ and cosine $r_i=\varepsilon+(r_0-\varepsilon)/s_i$, with $\varepsilon=\mathrm{sign}\,\gamma$. Alignment is a monotone function of channel strength, and the spectrum $\Sigma$ is generated with no spectral parameter. Antigravity reports (fitted to moments of $t_i$ only): diagonal share predicted with correlation 0.96 across heads, PR median 46.2 versus 45.7, PR correlation 0.42, relation-(1) error median 0.039 versus 0.059, $a-b$ correlation only 0.20. It cannot give $a>b$; its candidate 3 adds antisymmetric $2\times2$ channel pairs ($K\mathrel{+}=\Omega JF_{\rm rot}$) for that. These numbers are Antigravity's and are not re-run by the supervising agent.

Check by the supervising agent (`delegations/round1_brief/check_agy.py`): on the 125 GPT-2 heads with $|\bar t|>0.05$ or $\mathrm{std}(t)>0.15$ (unweighted), the within-head $|\mathrm{corr}(\sigma_i,t_i)|$ has median 0.43 [0.09, 0.81]. Candidate 2 samples (isotropic, $N_{\rm eff}=430$, 10 draws each) give 0.44 at $(r_0,\gamma)=(-0.05,0.25)$, 0.48 at $(-0.3,0.4)$, 0.77 at $(-0.6,0.55)$, and 0.14 at $(0.3,-0.3)$. The measured coupling is substantial and within the range candidate 2 produces. The signed index correlation (−0.11, R3 brief) understated this coupling because its sign varies across heads.

Also confirmed independently by Antigravity: the identity of R4 and $\mathrm{corr}(a-b,q)=-0.968$.

## R10. Bound on reciprocal overlap from σ-independent off-diagonal noise (from Claude subagent, round 2)

Let the off-diagonal entries of $W$ have mean zero and variance $o^2$, independent of $\Sigma$, with any correlation $\rho\in[-1,1]$ between $E_{ij}$ and $E_{ji}$. Then
$$|\mathbb E\,q|=|\rho|\,o^2\Bigl(\frac{(\sum_i\sigma_i)^2}{\sum_i\sigma_i^2}-1\Bigr)\le o^2(n-1).$$
At the GPT-2 off-diagonal RMS $o=0.048$ and $n=64$, the bound is $0.145$. The heads L0H3, L0H4, L0H7, and L0H10 have $q\approx-0.2$. Any ensemble that produces those heads therefore needs either off-diagonal mass beyond the GPT-2 RMS, or a reciprocal coupling concentrated on pairs of large singular values (an antisymmetric coupling of the top singular directions).

Checked: bound derived by hand by the supervising agent ($\mathbb E[E_{ij}E_{ji}]=\rho o^2$ and $\sum_{i\ne j}\sigma_i\sigma_j=(\sum\sigma_i)^2-\sum\sigma_i^2$; Cauchy–Schwarz gives $(\sum\sigma_i)^2\le n\sum\sigma_i^2$). The values $q\approx-0.2$ for those heads are the subagent's, consistent with $a-b\approx+0.14$ to $+0.20$ (R6) and $\mathrm{corr}(q,a-b)=-0.97$ (R4).

## R11. The heavy tail of $W$ lives in the bottom singular block and is skew (from Grok and Codex, round 2)

On raw GPT-2 heads, with $E$ the off-diagonal part of $W$, $H=(E+E^\top)/2$ and $J=(E-E^\top)/2$:

- Off-diagonal kurtosis of $H$ has median 3.63 [3.28, 5.10]; of $J$, 53.9 [6.5, 155.9]. The heavy tail is in the skew part.
- Zeroing the $8\times8$ block of $E$ on the eight smallest singular values drops the median kurtosis from 20.6 to 3.69. In the median head, every entry with $|E_{ij}|>5\times$ RMS lies in that block. The median pair correlation $\mathrm{corr}(E_{ij},E_{ji})$ inside that block is $-0.83$.
- Gaussian baseline ($Q,K$ independent Gaussian, 30 draws): kurtosis 2.98, bottom-block pair correlation $-0.02$, bottom-block RMS / overall RMS 0.97. The skew heavy tail in the weak singular directions is learned, not an SVD artifact.
- Because $q$ weights pairs by $\sigma_i\sigma_j$, the bottom block contributes little to $q$ or to the profile; Grok reports that zeroing it moves the median $a-b$ by about $-0.002$ (not re-run).

Checked: numerical, by the supervising agent (`delegations/round1_brief/check_HJ.py`, `check_r2.py`, and an inline Gaussian-baseline run).

## R12. Round-2 candidates: one recipe covers both signs of $a-b$, at a cost in parameters (round 2, numbers reported by delegate agents)

- Codex: eight parameters per head, two global constants. Diagonal $t_i=\mu+\xi\ell_i+\delta Z_i$ (affine in log-singular value), a power-law symmetric Gaussian background, a skew Gaussian background plus $m=9$ sparse skew impulses placed with probability $\propto(\sigma_i\sigma_j)^\beta$; spectrum from one lognormal-quantile parameter. Reports relation-(1) error median 0.0592 versus 0.0589 measured (correlation 0.905), $a-b$ correlation 0.950 (partly fitted through $q$), sign of $a-b$ correct on 130/144 heads. Fails on extreme layer-0 heads, overestimates diagonal share, underestimates $\min(c,d)$ by a factor of about 7.6; 90% intervals cover the relation-(1) error on only 68% of heads.
- Grok: three or five parameters per head, with the measured $\Sigma$ as a covariate; block-structured pair correlations, with a skew Student-$t$ bottom block. Five-parameter version: relation-(1) error median 0.055 (correlation 0.87), sign of $a-b$ correct on 89% of heads; kurtosis about half the measured level. Grok reports that the relation-(1) error above the diagonal floor sits in coherent within-pair products inside spectral blocks, not in cross-block entries.
- Claude subagent: five parameters per head, two global constants; relation-(1) error median 0.052 (ratio 0.91), $a-b$ correlation 0.87.

Common failure in all three: the extreme layer-0 heads (L0H3, L0H4, L0H7, L0H9), whose negative $q$ exceeds what σ-independent noise can give (R10), and whose fitted $q$ the contraction projection erodes.

Checked: the supervising agent has read the three answers; none of these fit numbers has been re-run by the supervising agent.

## R13. Theorem: exact preimage of $\Theta$ among sums of rank-one forms on orthogonal planes (supervising agent, after round 2)

**Setting.** $L=\sum_{i=1}^n\sigma_iu_iv_i^\top$ with $\sigma_i>0$, unit vectors $u_i,v_i$, $t_i=u_i^\top v_i\in(-1,1)$, and the planes $\mathrm{span}(u_i,v_i)$ mutually orthogonal (equivalently $W=\mathrm{diag}(t_i)$ in R1). Put $\alpha_i=\sigma_i(1+t_i)/2$, $\beta_i=\sigma_i(1-t_i)/2$, $w_i=\sigma_i^2/\sum_j\sigma_j^2$. Call $(\alpha,\beta)$ **comonotone** if $(\alpha_i-\alpha_j)(\beta_i-\beta_j)\ge0$ for all $i,j$.

**Theorem.**
1. $a\le b$, with equality if and only if $(\alpha,\beta)$ is comonotone.
2. If $(\alpha,\beta)$ is comonotone, then relation (1) holds exactly at every sorted index.
3. If $(\alpha,\beta)$ is comonotone, then $d=0$ if and only if every $t_i\ge0$, and $c=0$ if and only if every $t_i\le0$; in either case $c-d=\sum_iw_it_i|t_i|$.
4. Hence, within this setting, $\pi(L)\in\Theta$ if and only if $(\alpha,\beta)$ is comonotone and all $t_i$ have one sign. Every point of $\Theta$ except its two vertices $c=1$ and $d=1$ is attained (e.g. $t_i\equiv t\in(-1,1)$); the vertices need $t=\pm1$, which this setting excludes.

**Proof.** By R2, the nonzero spectrum of $S$ is $\{\alpha_i\}\cup\{-\beta_i\}$ and the singular values of $T$ are $\sqrt{\alpha_i\beta_i}$, each twice; and $a\|L\|^2=\|T\|^2=2\sum_i\alpha_i\beta_i$, $b\|L\|^2=2\langle\alpha^\downarrow,\beta^\downarrow\rangle$.
(1) Rearrangement: $\langle\alpha^\downarrow,\beta^\downarrow\rangle\ge\sum_i\alpha_i\beta_i$. If some pair is discordant, swapping $\beta_i,\beta_j$ raises $\sum\alpha_k\beta_k$ by $-(\alpha_i-\alpha_j)(\beta_i-\beta_j)>0$, so the identity pairing is not maximal and the inequality is strict. If no pair is discordant, order the indices by $\alpha$ and break ties by $\beta$; concordance makes $\beta$ nonincreasing in that order too, so one permutation $\pi$ sorts both and equality holds.
(2) With that common $\pi$, $\lambda_{+,k}=\alpha_{\pi(k)}$, $\lambda_{-,k}=\beta_{\pi(k)}$, and $\sqrt{\alpha_{\pi(k)}\beta_{\pi(k)}}$ is nonincreasing in $k$, so it is the sorted list $\sigma(T)$.
(3) With the common $\pi$, $\lambda_{+,k}-\lambda_{-,k}=\sigma_{\pi(k)}t_{\pi(k)}$, which has the sign of $t_{\pi(k)}$; and $(\sigma_it_i)^2/\|L\|^2=w_it_i^2$.
(4) Combine (1) and (3); $\Theta=\{a=b,\ cd=0\}$.

**Equivalent form for balanced channels.** If $L=K^\top Q$ with rows $q_i,k_i$, $|q_i|=|k_i|$, and the $2n$ rows spanning mutually orthogonal planes pairwise as above, then $\alpha_i=|q_i+k_i|^2/4$ and $\beta_i=|k_i-q_i|^2/4$. Comonotone means: the channel norms of $Q+K$ and of $K-Q$ are similarly ordered.

**GPT-2.** In the diagonal surrogate of each raw head (measured $\sigma_i,t_i$, off-diagonal of $W$ set to 0), Kendall's $\tau(\alpha,\beta)$ has median 0.761 [0.565, 0.859]; $\mathrm{corr}(1-\tau,\ \text{relation-(1) error of the surrogate})=0.63$.

Checked: proof by hand by the supervising agent. Numerical check (`delegations/round1_brief/comono.py`): random comonotone block forms give $|a-b|\le10^{-16}$ and relation-(1) error $\le10^{-16}$; generic block forms give $a-b\approx-0.03$ and error $\approx0.07$. **Not yet challenged by a delegate agent.**

## R14. Theorem: a random ensemble whose profiles lie on $\Theta$ in the limit $N\to\infty$ (supervising agent, after round 2)

**Ensemble $\mathcal E(\mu;f,g)$.** Fix $n$. Let $\mu$ be a probability law on $\mathbb R$ (a latent channel strength), and let $f,g:\mathbb R\to(0,\infty)$ be measurable, both nondecreasing. Draw $\rho_1,\dots,\rho_n$ i.i.d. from $\mu$, and independent standard Gaussian matrices $P,M\in\mathbb R^{n\times N}$. Set
$$Q+K=2\,\mathrm{diag}\bigl(\sqrt{f(\rho_i)}\bigr)P/\sqrt N,\qquad K-Q=2\,\mathrm{diag}\bigl(\sqrt{g(\rho_i)}\bigr)M/\sqrt N .$$
Equivalently, channel $i$ has $|q_i|^2\approx|k_i|^2\approx f(\rho_i)+g(\rho_i)$ and $q_i\cdot k_i\approx f(\rho_i)-g(\rho_i)$, so $t_i\approx(f-g)/(f+g)$.

**Theorem.** Conditional on $\rho$, as $N\to\infty$ with $n$ fixed, almost surely $\pi(L)\to\pi_\infty$, and the relation-(1) error tends to 0, where $\pi_\infty$ is the profile of the block form with $\alpha_i=f(\rho_i)$, $\beta_i=g(\rho_i)$. Therefore $a-b\to0$, relation (1) becomes exact, and $\pi_\infty\in\Theta$ whenever $f-g$ has one sign on the support of $\mu$. If moreover $f-g$ has one sign and $n\to\infty$, then $c-d\to\mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]$ almost surely (from R13(3) with $\sigma_i=\alpha_i+\beta_i$ and $\sigma_it_i=\alpha_i-\beta_i$, plus the strong law of large numbers, assuming $\mathbb E[(f+g)^2]<\infty$). The position along $\Theta$ is the $(f+g)^2$-weighted mean of $r|r|$, $r=(f-g)/(f+g)$; it depends on the joint law of $(r,f+g)$, not on the law of $r$ alone (round 3 counterexample: $\rho$ uniform on $\{0,1\}$, $f=(2,3),g=(1,3)$ gives $1/45$, $f=(1,4),g=(1,2)$ gives $1/10$; both have $r\in\{0,1/3\}$ equally likely).

**Proof.** With $F=[Q;K]$ and $M_N=FF^\top$, the nonzero spectra of $2S$ and $2T$ are the spectra of $J'M_N$ and $\Omega M_N$ (R5), and $\|L\|^2=\mathrm{tr}(L^\top L)$ is a polynomial in the entries of $M_N$; so the profile and the relation-(1) error are continuous functions of $M_N$ wherever $\|L\|\ne0$ and $\sigma(T)\ne0$. By the strong law of large numbers, the rows of $P/\sqrt N$ and $M/\sqrt N$ become orthonormal almost surely, so $M_N$ converges almost surely to the Gram matrix of a block form in which $\Pi$ and $\Delta$ rows are mutually orthogonal with $|\pi_i|^2=f(\rho_i)$ and $|\delta_i|^2=g(\rho_i)$. In that limit $S=\Pi^\top\Pi-\Delta^\top\Delta$ has eigenvalues $f(\rho_i)$ and $-g(\rho_i)$, i.e. $\alpha_i=f(\rho_i)$, $\beta_i=g(\rho_i)$. Because $f$ and $g$ are both nondecreasing, $(\alpha,\beta)$ is comonotone, and R13 gives $a=b$, exact relation (1), and $\pi\in\Theta$ when all $t_i$ share a sign.

**Special cases.** $g\equiv$ const: Antigravity's signed-spike ensemble (R9) in the limit. $f/g\equiv$ const: one tilt per head. $f,g$ both constant with $f\ne g$: the correlated Gaussian model of the question. $f,g$ constant: the independent Gaussian model ($f=g$) and its correlated version.

**Round-3 notes.** "Almost surely" presumes one probability space for all $N$ (draw infinite i.i.d. Gaussian arrays and take the first $N$ columns); the conclusion also holds in probability by Gaussian concentration. In R13, read "$W$ diagonal" as "diagonal in some SVD gauge". The $c-d$ formula of R13(3) holds under comonotonicity alone, whatever the signs of $t_i$.

**Scope (round 3).** The $c-d$ limit is an iterated limit: $N\to\infty$ with $n$ fixed, then $n\to\infty$ for the block profiles. A joint limit is **false** in the proportional regime $N=\kappa n$, $n\to\infty$ (Antigravity, round 3): for constant $f\equiv\alpha$, $g\equiv\beta$, $\|L\|^2/n\to(\alpha+\beta)^2+(\alpha-\beta)^2/\kappa$ and $1-2a\to(1+1/\kappa)(\alpha-\beta)^2/((\alpha+\beta)^2+(\alpha-\beta)^2/\kappa)$, not $(\alpha-\beta)^2/(\alpha+\beta)^2$; the departures are $O(1/\kappa)$. Checked: the $\|L\|^2$ term by hand ($\mathbb E[(q_i\cdot q_j)(k_i\cdot k_j)]=(\alpha-\beta)^2/N$ for $i\ne j$), and numerically at $\alpha=2,\beta=1,n=400,N=800$: $1-2a=0.1598$ against $0.1579$ predicted and $0.1111$ for the iterated limit. GPT-2 small has $\kappa=12$. Comonotonicity alone gives $a=b$ and exact relation (1); membership in $\Theta$ needs the one-sign condition in addition (with $f-g$ changing sign, $c>0$ and $d>0$ in the limit). The signed-spike label applies with $g\equiv$ const when the spike coefficient is positive; a negative coefficient gives $f\equiv$ const.

**Round-3 keystone result.** Challenged by Codex (astra/high), Grok, and a Claude subagent; Antigravity also answered, with the same two findings plus the proportional-regime point above. All four confirmed R13(1)–(4) and the fixed-$n$ limit of R14, and all three independently found the two over-broad sentences now corrected (endpoints of $\Theta$; law of $r$ versus joint law). Codex's and Grok's counterexamples were checked by hand by the supervising agent (Codex: $1/5$ versus $4/17$; Grok: $1/13$ versus $25/226$).

**Status.** The convergence step and items 1–3 are checked by hand by the supervising agent. The $c-d$ limit is checked by hand by the supervising agent. Not yet challenged by a delegate agent.

## R15. Second model: GPT-2 medium reproduces the GPT-2 small structure (supervising agent)

Raw $L=K^\top Q$, $n=64$; median [10th, 90th]. Script `delegations/round1_brief/medium.py`, run by the supervising agent.

| statistic | GPT-2 small ($N=768$, 144 heads) | GPT-2 medium ($N=1024$, 384 heads) |
|---|---|---|
| off-diagonal RMS of $W$ | 0.0483 (ratio to $N^{-1/2}$: 1.34) | 0.0422 (ratio to $N^{-1/2}$: 1.35) |
| Kendall $\tau(\alpha,\beta)$, diagonal surrogate (R13) | 0.761 [0.565, 0.859] | 0.769 [0.628, 0.891] |
| relation-(1) error | 0.059 [0.037, 0.156] | 0.051 [0.027, 0.128] |
| diagonal share of $W$ | 0.18 | 0.21 |
| within-head std of $t_i$ | 0.092 | 0.089 |
| fraction of heads with $a>b$ | 0.31 | 0.22 |
| $\mathrm{corr}(q,a-b)$ | −0.968 | −0.974 |
| off-diagonal kurtosis / after zeroing bottom $8\times8$ block | 20.6 / 3.69 | 6.2 / 3.61 |

Consequences: the off-diagonal RMS scales as $N^{-1/2}$ with a fixed factor of about 1.35 (Grok's falsifier 3 in round 1 passes; the effective-dimension reading $N_{\rm eff}\approx0.55N$ survives). The comonotonicity level, the $q$ mechanism for $a-b$, and the location of the heavy tail in the bottom block all carry over.

Checked: numerical, by the supervising agent. Two models of one family only; no RoPE or ALiBi model yet.

## R16. Third model: Pythia-160m (RoPE) (supervising agent)

Raw $d=0$ form $L=K^\top Q$ from `query_key_value` (GPT-NeoX layout, per head $[q;k;v]$ blocks), $N=768$, $n=64$, 144 heads; RoPE on 25% of head dimensions. Script `delegations/round1_brief/pythia.py`. Median [10th, 90th]:

- off-diagonal RMS of $W$: 0.0470 (ratio to $N^{-1/2}$: 1.30).
- Kendall $\tau(\alpha,\beta)$, diagonal surrogate: 0.855 [0.672, 0.908] (GPT-2: 0.76–0.77).
- relation-(1) error: 0.044 [0.020, 0.116].
- diagonal share 0.134; within-head std of $t_i$ 0.083.
- fraction of heads with $a>b$: 0.31; $\mathrm{corr}(q,a-b)=-0.955$.
- off-diagonal kurtosis 3.52 [3.15, 4.89]; no heavy tail.

Consequences: the comonotone structure, the off-diagonal scale $\approx1.3N^{-1/2}$, and the $q$ mechanism for $a-b$ carry over to a RoPE model. The skew heavy tail in the bottom singular block (R11) does **not** appear in Pythia-160m; it is GPT-2-specific. The fraction of heads with $a>b$ is not lower in this RoPE model than in GPT-2 small, contrary to Antigravity's round-1 falsifier 3 (which predicted fewer); that falsifier concerned early layers only and was not tested layer by layer.

Checked: numerical, by the supervising agent. The GPT-NeoX head layout (reshape $(H,3,n,N)$) is from the standard GPT-NeoX convention; not verified against the model's forward pass.

## R17. Lean formalization plan for Theorems A and B (supervising agent, 2026-11-24)

Lean project: `lean/` (Lean v4.28.0, Mathlib v4.28.0). Skeleton statements written and checked against the paper statements by the supervising agent; proofs in progress.

| Layer | File | Content | Paper claim |
|---|---|---|---|
| 1 | `OdeskyLean/Rearrangement.lean` | sorting by permutations; blockwise ≤ sorted pairing, equality iff similarly ordered; relation (1) for the sorted lists; `c-d` numerators; `c=0`, `d=0` iff one-sign | R13(1)–(3), list level |
| 2 | `OdeskyLean/Profile.lean` | profile `(a,b,c,d)` defined from `α, β` and the sorting permutations; `a+b+c+d=1`; `a≤b`; `a=b` iff similarly ordered; `c-d=∑w_it_i|t_i|`; `π∈Θ` iff similarly ordered and one sign | R13(1)–(4) |
| 3 | `OdeskyLean/Geometry.lean` | eigenvector equations of `S`, `T` for a sum of rank-one forms on orthogonal planes on `ℝ^N`; `S=T=0` off the planes; `α+β=s`, `α-β=st`, `αβ=s²(1-t²)/4` | proof step 1 of R13 |
| 4 | `OdeskyLean/Probability.lean` | strong law for the Gram matrix; continuity transfer; strong law for the ratio giving the `c-d` limit | R14 proof |

Gaps, not formalized (named here so that no Lean result is read as stronger than it is):
- G1. From the eigenvector equations of Layer 3 to the sorted spectral lists $\lambda_\pm,\sigma(T)$ and the Frobenius norms $\|L\|^2=\sum s_i^2$, $\|T\|^2=2\sum\alpha_i\beta_i$ used as definitions in Layer 2.
- G2. Continuity of the profile and of the relation-(1) error in the Gram matrix of $[Q;K]$ (taken as the hypothesis `hΦ` of `limit_of_continuousAt`).
- G3. Gaussian moments for the stacked columns of $[P;M]$ (the hypotheses `hint`, `hmom` of `gram_slln`).

**R17 status (2026-11-24).** All four files proved by four `codex-node` delegate agents on sol/low (`gpt-6.1-sol`, effort low), one per file; reports in `delegations/answers/lean1/`. The supervising agent checked: only `sorry` lines were removed relative to the skeleton (statement-by-statement comparison and `git diff`); `lake build` succeeds; `#print axioms` on the headline theorems gives only `propext`, `Classical.choice`, `Quot.sound`. Lean now checks:
- R13(1)–(4) for the profile defined from $(\alpha,\beta)$ and sorting permutations (`Odesky.profA_le_profB`, `profA_eq_profB_iff`, `profC_sub_profD`, `mem_Theta_iff`, `prof_sum_eq_one`), and relation (1) at list level (`relation_one`), with hypotheses $\alpha_i,\beta_i>0$, $n\ge1$.
- R13 proof step 1 as eigenvector equations (`OrthoBlocks.S_add`, `S_sub`, `T_add`, `T_sub`, `neg_T_sq_add`, `neg_T_sq_sub`, `S_perp`, `T_perp`, `inner_add_sub`).
- R14 proof steps 4 and 6 (`gram_slln`, `limit_of_continuousAt`, `ratio_slln`), with the continuity hypothesis G2 and moment hypotheses G3.
Checked up to G1–G3, and no stronger.

**R17 update (2026-11-25).** Gaps G1 and G3 are closed, and Theorem A is checked for the operator itself. Each file below was proved by one `codex-node` delegate agent on sol/low and accepted by the supervising agent (statements unchanged; `lake build` succeeds; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`):
- `OdeskyLean/Spectral.lean` (G1): `charpoly_S` $=\prod_i(X-\alpha_i)(X+\beta_i)\cdot X^{N-2n}$; `charpoly_neg_T_sq` $=\prod_i(X-\alpha_i\beta_i)^2X^{N-2n}$; `roots_S_pos`, `roots_S_neg`, `roots_neg_T_sq_pos`; `frob_L`, `frob_S`, `frob_T` in any orthonormal basis; `sorted_eq_of_multiset`. Hypotheses: $2n\le N$, $|t_i|<1$.
- `OdeskyLean/Gaussian.lean` (G3): `gaussian_prod_integrable`, `gaussian_second_moment` for independent standard Gaussian coordinates.
- `OdeskyLean/Main.lean`: **Theorem A for the operator.** With `SpectralLists` (decreasing lists whose multisets are the positive eigenvalues of $S$, the absolute negative eigenvalues of $S$, and the singular values of $T$ counted once) and Frobenius norms in any orthonormal basis: `main_a_le_b`, `main_relation_one`, `main_c_sub_d`, `main_mem_Theta_iff`; `spectralLists_exists` shows the hypotheses are not vacuous. Hypotheses: $n\ge1$, $2n\le N$, $|t_i|<1$; all are in the paper's setting.
Remaining gap: G2 only (continuity of the sorted eigenvalues in the Gram matrix; Mathlib has no Weyl or Courant–Fischer inequality). In progress: `OdeskyLean/TheoremB.lean` (Gram limit of the ensemble and its limit configuration).
- `OdeskyLean/TheoremB.lean`: `gram_limit` (almost surely, the Gram matrix of the rows of $Q,K$ in the ensemble converges to $\langle q_i,q_l\rangle=\langle k_i,k_l\rangle=\delta_{il}(f_i+g_i)$, $\langle q_i,k_l\rangle=\delta_{il}(f_i-g_i)$, for independent standard Gaussian columns) and `blocks_of_limit_gram` (any rows with that Gram matrix form a sum of rank-one forms on orthogonal planes with $L=K^\top Q$, $\alpha_i=f_i$, $\beta_i=g_i$, $|t_i|<1$). Proved by a `codex-node` delegate agent on sol/low; accepted as above.

**What Lean checks now.** Theorem A in full, for the operator, with hypotheses $n\ge1$, $2n\le N$, $|t_i|<1$. Theorem B: the Gram-matrix limit, the identification of the limit with Theorem A's setting ($\alpha=f$, $\beta=g$), and the $c-d$ ratio limit; the step "profile of $L_N$ $\to$ profile of the limit" is `limit_of_continuousAt` under the hypothesis G2. G2 is not formalized: it needs (i) the nonzero spectra of $S_N,T_N$ as eigenvalues of a $2n\times2n$ symmetric matrix built from the Gram matrix (R5), (ii) Weyl's inequality $|\lambda_k(A)-\lambda_k(B)|\le\|A-B\|$ for sorted eigenvalues (Mathlib has `LinearMap.IsSymmetric.eigenvalues_antitone` but no perturbation bound), and (iii) continuity of the matrix square root. All three are textbook facts.

## R18. Fourth model: BLOOM-560m (ALiBi) (supervising agent)

Raw $L=K^\top Q$ from `h.{l}.self_attention.query_key_value.weight` (per-head $[q;k;v]$ layout, as in GPT-NeoX), $N=1024$, $n=64$, 384 heads; positions enter only through the ALiBi bias, so $L$ is the whole query-key form. Script `delegations/round1_brief/bloom.py` (copy of `pythia.py` with BLOOM key names). Median [10th, 90th]:

- off-diagonal RMS of $W$: 0.0414 (ratio to $N^{-1/2}$: 1.32).
- Kendall $\tau(\alpha,\beta)$, diagonal surrogate: 0.763 [0.512, 0.846].
- relation-(1) error: 0.044 [0.020, 0.131].
- diagonal share of $W$: 0.18; within-head std of $t_i$: 0.089.
- fraction of heads with $a>b$: 0.19; $\mathrm{corr}(q,a-b)=-0.973$.
- off-diagonal kurtosis 3.45 (3.46 after zeroing the bottom $8\times8$ block): BLOOM has no heavy off-diagonal tail, unlike GPT-2 small (20.6).

Consequence: the structure of R13/R15/R16 (diagonal share about 11 times chance, off-diagonal RMS about $1.3N^{-1/2}$, $\tau\approx0.76$, $q$ controlling $a-b$) holds for an ALiBi model too. The heavy tail of R11 is not universal.

Checked: numerical, by the supervising agent, 2026-11-25.

**R17 final (2026-11-25): G2 closed; Theorems A and B are checked in Lean with no gaps.** New files, each accepted by the supervising agent (only `sorry` lines removed relative to the skeleton; full `lake build` succeeds; `#print axioms` on `theoremB_ae`, `profile_tendsto`, and the Theorem A headline theorems gives only `propext`, `Classical.choice`, `Quot.sound`):
- `Weyl.lean` (`weyl_le`, `weyl_abs`, `roots_charpoly_eq_eigenvalues`): `codex-node` sol/low.
- `Orthonormalize.lean` (`exists_orthonormal_near`), `GenProfile.lean` (general profile `gA`–`gD`, `gErr` from Mathlib's sorted eigenvalues; Frobenius norms via the Gram matrix), `Perturb.lean` (`formL_perturb`, `formLt_perturb`, `formL_bound`), `Limit.lean` (`lists_at_limit`, `gprof_at_limit`), `TheoremBFull.lean` (`profile_tendsto`, `theoremB_ae`): Claude `opus` subagents, because `codex-node` launches failed (macOS Automation permission for iTermForSubagents was lost, error -1743).
**Statement of `theoremB_ae`.** Fix $n\ge1$ and $f_i,g_i>0$ (conditioning on $\rho$). Let the columns $Z_j$ of $[P;M]$ be pairwise independent, identically distributed, measurable, with independent standard Gaussian coordinates. Then almost surely, as $N\to\infty$, the profile $(a,b,c,d)$ of $L_N=K_N^\top Q_N$ (from Mathlib's sorted eigenvalues of $S$ and $T^\top T$, and Frobenius norms) tends to the Theorem A profile with $\alpha=f$, $\beta=g$, and, if $(f,g)$ is similarly ordered, the relation-(1) error tends to $0$. The $n\to\infty$ limit of $c-d$ is the separate theorem `ratio_slln`.

## R19. Fifth model: GPT-2 large (supervising agent)

Raw $L=K^\top Q$, $N=1280$, $n=64$, 720 heads; script `delegations/round1_brief/medium.py` on the GPT-2 large weights. Median [10th, 90th]:

- off-diagonal RMS of $W$: 0.0388 (ratio to $N^{-1/2}$: 1.39).
- Kendall $\tau(\alpha,\beta)$, diagonal surrogate: 0.781 [0.618, 0.885].
- relation-(1) error: 0.050 [0.032, 0.113].
- diagonal share of $W$: 0.24; within-head std of $t_i$: 0.095.
- fraction of heads with $a>b$: 0.21; $\mathrm{corr}(q,a-b)=-0.979$.
- off-diagonal kurtosis 5.5 (4.1 after zeroing the bottom $8\times8$ block).

Consequence: the structure of R13/R15/R16/R18 holds at the largest width measured; $\tau$ and the diagonal share rise slightly with width (GPT-2 small, medium, large: $\tau$ 0.76, 0.77, 0.78; diagonal share 0.18, 0.21, 0.24).

Checked: numerical, by the supervising agent, 2026-11-25.
