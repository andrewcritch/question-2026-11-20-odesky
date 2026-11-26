# Random-Matrix Ensembles for Trained Transformer Attention Heads

## Executive Summary

To reproduce the spectral and geometric statistics of trained attention-head bilinear forms $L = K^\top Q \in \mathbb{R}^{N \times N}$ ($Q, K \in \mathbb{R}^{n \times N}$, $n \le N/2$), an ensemble must simultaneously account for four empirical facts in GPT-2 small ($n = 64, N = 768$, 144 heads):

1. **Co-diagonalizability of $\Sigma$ and $W = U^\top V$:** The diagonal share $\sum_{i=1}^n t_i^2 / \|W\|_F^2$ has median $0.184$ ($[0.039, 0.552]$, up to $0.955$), compared to $1/n = 0.0156$ for the Gaussian null, while the off-diagonal RMS stays tightly pinned around $0.048$ ($[0.042, 0.054]$)—on the scale of $1/\sqrt{N_{\text{eff}}}$ ($N_{\text{eff}} \approx 430$) rather than $1/\sqrt{n} = 0.125$.
2. **Wide within-head dispersion of $t_i = W_{ii}$ with top-vs-bulk separation:** Within-head $\sigma^2$-weighted $\mathrm{std}(t_i)$ has median $0.092$ ($[0.057, 0.246]$), and $75.7\%$ of heads satisfy $|\bar{t}| \le 2\,\mathrm{std}(t_i)$. Direct inspection of $(s_i, t_i)$ across GPT-2 heads shows a two-scale structure: a bulk of $\sim 50$ singular modes clustered near a baseline alignment $r_0$, and a hierarchy of larger singular modes pulled coherently toward $+1$ or $-1$ (producing the median correlation $-0.108$ between singular-value index $1,\dots,n$ and signed $t_i$ on $|\bar{t}| > 0.05$).
3. **Asymmetric sign structure of $a - b$:** Purely diagonal $W = \operatorname{diag}(t_i)$ forces $a - b \le 0$ identically (proved below via the rearrangement inequality), explaining why GPT-2's median $a - b = -0.012$ is negative. Conversely, the $\sim 28\%$ of raw heads with $a - b > 0$ (and the $20\%$ of `lnfold` heads with $|a - b| > 0.1$) arise from $2 \times 2$ skew-rotational blocks in $W$ associated with near-degenerate singular pairs (such as positional/shift heads `L0H3`, `L0H4`, `L0H7`). Across all 144 heads, $a - b$ correlates at **$r = 0.968$** with the off-diagonal non-normality trace $-\|L\|_F^{-2}\sum_{i \neq j} \sigma_i \sigma_j W_{ij} W_{ji}$.
4. **Coupled singular-value concentration:** The participation ratio $\mathrm{PR}(\Sigma) = (\sum \sigma_i^2)^2 / \sum \sigma_i^4$ drops from the Marchenko–Pastur null ($54.8$) to $45.7$ ($[24.6, 52.5]$), correlating negatively with $\mathrm{std}(t_i)$ ($r = -0.385$).

Below we present **three nested random-matrix ensembles for $(Q, K)$** with 2 to 3 parameters per head, give analytical derivations for every statistic, report head-by-head fits and unconditional population draws against all 144 GPT-2 heads, and state our judgement and falsification tests. **Candidate 2 (the Signed-Spike Correlated Gaussian Ensemble, 2 parameters per head)** is our primary recommendation for a natural, minimal random-matrix model; **Candidate 3** adds one rotary-skew parameter $\nu \ge 0$ to capture non-normal shift heads with $a - b > 0$.

---

## 1. Three Candidate Ensembles for $(Q, K)$

Throughout, let $n = 64, N = 768$. Let $\Gamma \in \mathbb{R}^{N \times N}$ be a fixed positive-definite residual-stream covariance normalized to $\operatorname{tr}(\Gamma) = 1$ with participation ratio $N_{\text{eff}} = (\operatorname{tr}\Gamma)^2 / \operatorname{tr}(\Gamma^2) \approx 430$ (setting $\Gamma = \frac{1}{N} I_N$ gives the $O_N$-isotropic limit $N_{\text{eff}} = N = 768$; an anisotropic spectrum with $N_{\text{eff}} = 430$ matches the empirical residual-stream covariance of GPT-2 weights). Multiplying $(Q, K) \mapsto (R Q, R K)$ on the left by any shared $R \in O_n(\mathbb{R})$ leaves $L = K^\top Q$ strictly unchanged, so each recipe below may be read either in canonical channel coordinates or conjugated by $R \sim \mathrm{Haar}(O_n)$ to make $(Q, K)$ left-$O_n$-invariant.

### Candidate 1: Heterogeneously Correlated Channel Ensemble
A direct multi-channel generalization of the scalar-correlated Gaussian model $K = r Q + \sqrt{1 - r^2}\, G$, replacing scalar $r$ with a normal distribution of Fisher-transformed channel correlations and Gamma channel scales.

- **Sampling recipe:**
  1. Draw channel variances $s_1, \dots, s_n \stackrel{\text{i.i.d.}}{\sim} \operatorname{Gamma}(\kappa, 1/\kappa)$ and Fisher alignments $z_1, \dots, z_n \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(\mu, \tau^2)$; set $r_i = \tanh(z_i) \in (-1, 1)$.
  2. Draw independent Gaussian matrices $X, Y \in \mathbb{R}^{n \times N}$ with independent rows $\sim \mathcal{N}(0, \Gamma)$.
  3. Set
     $$Q = \operatorname{diag}(\sqrt{s})\, X, \qquad K = \operatorname{diag}(\sqrt{s})\left(\operatorname{diag}(r)\, X + \operatorname{diag}\!\left(\sqrt{1 - r^2}\right) Y\right).$$
- **Parameter count:** **2 parameters per head** ($\mu \in \mathbb{R}$, $\tau \ge 0$), plus 2 global model constants ($\kappa = 20$, $N_{\text{eff}} = 430$). *(Optional 3-parameter variant fits $\kappa_h$ per head to match $\mathrm{PR}_h$.)*

---

### Candidate 2: Signed-Spike Correlated Gaussian Ensemble *(Main 2-Parameter Recommendation)*
A purely linear-Gaussian "correlated bulk + signed feature update" model requiring **no $\tanh$ nonlinearity and no external Gamma distribution**, yet endogenously generating *both* the singular-value spectrum $\Sigma$ ($\mathrm{PR} \approx 46$) and the full distribution of $W$.

- **Sampling recipe:**
  1. Draw three independent Gaussian matrices $X_0, Y_0, F \in \mathbb{R}^{n \times N}$ with independent rows $\sim \mathcal{N}(0, \Gamma)$, and a standard normal vector $g \sim \mathcal{N}(0, I_n)$.
  2. Given head parameters $r_0 \in (-1, 1)$ (bulk correlation) and $\gamma \in \mathbb{R}$ (signed feature-learning amplitude), set
     $$Q = X_0 + |\gamma|\,\operatorname{diag}(g)\, F, \qquad K = \left(r_0 X_0 + \sqrt{1 - r_0^2}\, Y_0\right) + \gamma\,\operatorname{diag}(g)\, F.$$
- **Parameter count:** **2 parameters per head** ($r_0 \in (-1, 1)$, $\gamma \in \mathbb{R}$), plus 1 global residual-stream constant ($N_{\text{eff}} = 430$).
- **Why training produces it:** At initialization, $(Q, K)$ has independent rows ($r_0 = 0, \gamma = 0$). During training with AdamW (where weight decay $\frac{\lambda}{2}(\|Q\|_F^2 + \|K\|_F^2)$ favors norm-balanced updates $\|q_i\| \approx \|k_i\|$), global attention-logit drift shifts the background Q–K correlation to $r_0$ (e.g., $r_0 < 0$ for self-suppressing heads that avoid attending to the current token, or $r_0 > 0$ for globally homophilic heads), while gradient updates on $n$ latent residual-stream features $F$ amplify channel $i$ with random Gaussian loading $|\gamma| g_i$ and coherent head parity $\varepsilon = \operatorname{sign}(\gamma) \in \{+1, -1\}$ ($+1$ for homophilic/induction matching $+f_i f_i^\top$, $-1$ for heterophilic repulsion $-f_i f_i^\top$).

---

### Candidate 3: Symplectic / Rotary-Augmented Signed-Spike Ensemble
Extends Candidate 2 from $1 \times 1$ real channels to $2 \times 2$ real-Schur blocks using the standard symplectic matrix $J = I_{n/2} \otimes \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$, capturing directed/positional shift interactions $f_{2j-1} f_{2j}^\top - f_{2j} f_{2j-1}^\top$.

- **Sampling recipe:**
  1. Generate $(Q_{\text{sym}}, K_{\text{sym}})$ from Candidate 2 with parameters $(r_0, \gamma)$.
  2. Draw an independent Gaussian feature matrix $F_{\text{rot}} \in \mathbb{R}^{n \times N}$ with rows $\sim \mathcal{N}(0, \Gamma)$ and pair amplitudes $\omega_1, \dots, \omega_{n/2} \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, \nu^2)$, repeated pairwise as $\Omega = \operatorname{diag}(\omega_1, \omega_1, \dots, \omega_{n/2}, \omega_{n/2})$.
  3. Set
     $$Q = Q_{\text{sym}} + \Omega F_{\text{rot}}, \qquad K = K_{\text{sym}} + \Omega J F_{\text{rot}}.$$
     *(When $\nu = 0$, Candidate 3 reduces identically to Candidate 2.)*
- **Parameter count:** **3 parameters per head** ($r_0 \in (-1, 1)$, $\gamma \in \mathbb{R}$, $\nu \ge 0$), plus 1 global constant ($N_{\text{eff}} = 430$).

---

## 2. Theoretical Analysis, Exact Identities, and Which Statistics Each Reproduces

### 2.1 Why dense head-space matrix couplings fail (Co-diagonalizability Principle)
A tempting coordinate-free generalization of $K = r Q + \sqrt{1 - r^2}\, G$ is to replace scalar $r$ with a dense symmetric GOE matrix $B = \mu I_n + \tau H_{\mathrm{GOE}}$, e.g., $Q = Z_1 + B^\top Z_2$, $K = Z_2 + B Z_1$ (or multiplying outside by independent channel scales $S_0^{1/2}$). We tested both in `test_candidates.py` (`M1` and `M1b`): they fail sharply (`err1` $= 0.39\text{–}0.61$, $a - b = -0.28\text{ to }-0.36$, `offrms` $= 0.073$, `diagfrac` $= 0.03\text{–}0.05$ at $\mu = 0$).

**Reason:** First, if $S_0 = I_n$, channel singular values $\sigma(\beta_i) = 1 + \beta_i^2$ are even in $\beta_i$, so opposite-sign eigenvalues $+\beta$ and $-\beta$ are degenerate and mixed at $O(1)$ by finite-$N$ inner-product noise. Second, if $S_0 \neq I_n$ does not commute with $B$, the SVD basis of $L$ rotates relative to the eigenbasis of $B$ by an orthogonal matrix $O_{\text{mix}} \in O_n$, turning $W \approx O_{\text{mix}}^\top \operatorname{diag}(r) O_{\text{mix}}$ into a **dense symmetric matrix**. Its diagonal share collapses to $\bar{r}^2 / \overline{r^2}$, while symmetric off-diagonal entries $W_{ij} = W_{ji} \sim \mathrm{std}(r)/\sqrt{n}$ inflate `offrms` and drive $a - b \ll 0$.

Empirically in GPT-2 (`explore_deep.py`), even in the raw neuron basis of `c_attn.weight`, $Q Q^\top$ and $K K^\top$ have diagonal shares **$0.875$** and **$0.892$** (close to the independent-row benchmark $\frac{n}{n + n(n-1)/N_{\text{eff}}} \approx 0.872$), while $K Q^\top$ already has diagonal share **$0.130$** ($8.3\times$ null). Thus Q–K alignment and singular-value scaling **commute** up to finite-$N$ inner-product fluctuations: the modes of Q–K correlation *are* the singular feature channels themselves.

### 2.2 Exact trace identity and rearrangement theorem for $a - b$
Using $L = U \Sigma V^\top$ and $W = U^\top V$ ($t_i = W_{ii}$, $w_i = \sigma_i^2 / \sum_j \sigma_j^2$), Lemma 5 of O'Desky (arXiv:2609.22990) gives $a = \frac{\|T\|_F^2}{\|L\|_F^2} = \frac{1}{2} - \frac{\operatorname{tr}(L^2)}{2\|L\|_F^2}$, where
$$\frac{\operatorname{tr}(L^2)}{\|L\|_F^2} = \frac{\operatorname{tr}(\Sigma W \Sigma W)}{\|L\|_F^2} = \sum_{i=1}^n w_i t_i^2 + \underbrace{\frac{1}{\|L\|_F^2}\sum_{i \neq j} \sigma_i \sigma_j W_{ij} W_{ji}}_{\mathcal{O}_{\text{off}}(W)}.$$

1. **Non-positivity of $a - b$ for diagonal $W$:** If $W = \operatorname{diag}(t_1, \dots, t_n)$, block $i$ has $\lambda_{+,i} = \frac{1}{2}\sigma_i(1 + t_i)$, $\lambda_{-,i} = \frac{1}{2}\sigma_i(1 - t_i)$, and $\sigma_i(T)^2 = \lambda_{+,i} \lambda_{-,i}$. By the **Hardy–Littlewood–Pólya rearrangement inequality**, sorting $\lambda_+$ and $\lambda_-$ separately in decreasing order satisfies
   $$b = \frac{2\langle \lambda_+^\downarrow, \lambda_-^\downarrow \rangle}{\|L\|_F^2} \ge \frac{2\sum_{i=1}^n \lambda_{+,i} \lambda_{-,i}}{\|L\|_F^2} = \frac{2\sum_{i=1}^n \sigma_i(T)^2}{\|L\|_F^2} = a \implies a - b \le 0,$$
   with equality iff $(\lambda_{+,i})$ and $(\lambda_{-,i})$ are comonotonic. Variation of $t_i$ breaks comonotonicity and pushes $a - b < 0$.
2. **Role of $\mathcal{O}_{\text{off}}(W)$:** Across GPT-2's 144 raw heads, setting $W_{\text{off}} = 0$ while keeping $(\Sigma, \operatorname{diag}(t))$ gives median $a - b = -0.004$ ($[-0.016, -0.0015]$, never positive) and median `err1` $= 0.026$, roughly half of the full-$W$ values ($a - b = -0.012$, `err1` $= 0.059$). Across all 144 heads (`explore_deep.py`),
   $$\operatorname{Corr}\!\left(a - b,\; -\mathcal{O}_{\text{off}}(W)\right) = +0.9677.$$
   - **Symmetric off-diagonal leakage ($\mathcal{O}_{\text{off}} > 0 \implies a - b < 0$):** In finite dimension $N_{\text{eff}}$, two channels $i, j$ with nearby singular values $s_i \approx s_j$ have random Gram overlap $O(1/\sqrt{N_{\text{eff}}})$, inducing a small orthogonal rotation $O \in O_n$ between nearby singular indices ($|i - j| \le 3$, where GPT-2's off-diagonal RMS is $1.5\times\text{–}2\times$ larger than at $|i - j| > 10$). Because $O^\top \operatorname{diag}(r) O$ is **symmetric**, $W_{ij} W_{ji} > 0$, pushing $a - b$ down to $-0.012$ at the median (and down to $-0.25$ when $\mathrm{std}(t_i)$ is large and $\Sigma$ is flat, as in `L5H9`).
   - **Skew-symmetric / rotary blocks ($\mathcal{O}_{\text{off}} < 0 \implies a - b > 0$):** A $2 \times 2$ rotation block $W_{\{1,2\}} \approx \rho \begin{pmatrix} \cos\theta & \sin\theta \\ -\sin\theta & \cos\theta \end{pmatrix}$ with $\sigma_1 \approx \sigma_2$ contributes $2 \sigma_1 \sigma_2 W_{12} W_{21} = -2\sigma_1^2 \rho^2 \sin^2\theta < 0$ to $\operatorname{tr}(L^2)$, increasing $a = \|T\|_F^2 / \|L\|_F^2$ while shrinking $\|S\|_F^2$ and driving **$a - b > 0$**. Empirically, GPT-2's most positive $(a - b)$ heads (`L0H3`: $+0.195$, `L0H4`: $+0.161$, `L0H7`: $+0.141$) all exhibit near-degenerate top singular pairs $\sigma_2/\sigma_1 \in [0.961, 0.973]$ and $2 \times 2$ rotation blocks $W_{12} \approx -W_{21} \approx \pm 0.70$.

### 2.3 Exact channel law and monotone alignment-spectrum coupling in Candidate 2
In Candidate 2, conditional on $g = (g_1, \dots, g_n)$ with $g_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$, rows $(q_i, k_i)$ are independent Gaussian pairs with covariance $\begin{pmatrix} 1 + \gamma^2 g_i^2 & r_0 + \varepsilon \gamma^2 g_i^2 \\ r_0 + \varepsilon \gamma^2 g_i^2 & 1 + \gamma^2 g_i^2 \end{pmatrix} \otimes \Gamma$, where $\varepsilon = \operatorname{sign}(\gamma)$. As $N_{\text{eff}} \gg n$, channel $i$ has singular scale and alignment cosine:
$$s_i = 1 + \gamma^2 g_i^2 \qquad (g_i^2 \sim \chi_1^2), \qquad r_i = \frac{r_0 + \varepsilon \gamma^2 g_i^2}{1 + \gamma^2 g_i^2} = \varepsilon + \frac{r_0 - \varepsilon}{s_i}.$$

Every empirical feature of GPT-2 follows directly from this pair of equations:
1. **Endogenous Gamma-like $\Sigma$ and participation ratio:** Since $g_i^2 \sim \chi_1^2 = \operatorname{Gamma}(\frac{1}{2}, 2)$, $s_i = 1 + \gamma^2 g_i^2$ has heavy-tailed upper draws ($g_{\max}^2 \sim 7\text{–}10$ for $n = 64$) above a unit bulk ($g_{\text{med}}^2 = 0.455$). Using $\mathbb{E}[g^2] = 1, \mathbb{E}[g^4] = 3, \mathbb{E}[g^6] = 15, \mathbb{E}[g^8] = 105$, the asymptotic participation ratio (multiplied by the finite-$N$ Marchenko–Pastur factor $\mathrm{PR}_{\text{null}}/n = 54.8/64 \approx 0.856$) is
   $$\mathrm{PR}(\Sigma) \approx 54.8 \times \frac{\left(1 + 2\gamma^2 + 3\gamma^4\right)^2}{1 + 4\gamma^2 + 18\gamma^4 + 60\gamma^6 + 105\gamma^8}.$$
   At $\gamma = 0$, $\mathrm{PR} = 54.8$; at GPT-2's median $|\gamma| \approx 0.30$, $\mathrm{PR} \approx 45.8$ (matching GPT-2's $45.7$ with **zero** spectral parameters); as $|\gamma| \gg 1$, $\mathrm{PR} \to 54.8 \times \frac{9}{105} = 4.7$ (matching the $\mathrm{PR} \approx 4\text{–}5$ collapse regime!). Furthermore, larger $|\gamma|$ simultaneously increases $\mathrm{std}(t_i)$ and lowers $\mathrm{PR}$, explaining $\operatorname{Corr}(\mathrm{PR}, \mathrm{std}(t_i)) < 0$.
2. **No opposite-sign degeneracy mixing:** Because $r_i(s_i) = \varepsilon + (r_0 - \varepsilon)/s_i$ is **strictly monotone in $s_i$**, channels with nearby singular values $s_i \approx s_j$ necessarily have nearby alignments $r_i \approx r_j$. Unlike Candidate 1 (where independent $s_i$ and $r_i$ place opposite-sign $r_i$ at adjacent $s_i$, over-producing symmetric off-diagonal leakage in $W$), Candidate 2 preserves high `diagfrac` and realistic `err1` and $a - b$.
3. **Wide mixed-sign $t_i$ ranges and top-mode alignment bias:**
   - When $r_0 < 0$ and $\gamma > 0$ (e.g., $r_0 = -0.60, \gamma = +0.55$, as in `L5H9`, `L1H1`, `L2H2`, `L0H9`), the $\sim 50$ small-$g_i^2$ bulk modes sit near $r_0 \approx -0.60$ while the top $g_i^2$ spikes reach $r_1 \approx +0.50$, spanning $[-0.60, +0.55]$ with small $|\bar{t}|$.
   - When $r_0 \approx +0.94$ and $\gamma = -0.35$ (`L0H5` regime), 62 bulk modes sit in $[+0.82, +0.95]$ ($\mathrm{PR} \approx 50$) while the single largest-$g_i^2$ draw drops to $r_1 = \frac{0.94 - 0.98}{1 + 0.98} = -0.02$.
   - Because $\sim 56\%$ of GPT-2 heads have $\gamma > 0$, top singular modes (small index $i$) have more positive $t_i$, reproducing $\operatorname{med\,Corr}(i, t_i) \approx -0.11$.
4. **Contraction-damped off-diagonal RMS:** Since rows of $W$ satisfy $\sum_j W_{ij}^2 \le 1$ and the unaligned key residual has variance $1 - r_i^2$, off-diagonal entries have variance $\mathbb{E}[W_{ij}^2] \approx \frac{1 - r_i^2}{N_{\text{eff}}}$, giving
   $$\mathrm{offrms}(W) \approx \sqrt{\frac{1 - \overline{t^2}}{N_{\text{eff}}}}.$$
   At $\overline{t^2} \approx 0.03$, $N_{\text{eff}} = 430$ yields $\mathrm{offrms} \approx 0.0475$ (GPT-2 median: $0.048$), while strongly aligned heads like `L0H5` ($\bar{t} = 0.91$) drop below the isotropic null $1/\sqrt{768} = 0.036$ to $\sqrt{(1 - 0.83)/430} \approx 0.020$ (GPT-2 `L0H5`: $0.0245$), explaining $\operatorname{Corr}(\mathrm{offrms}, |\bar{t}|) = -0.475$.
5. **Prediction of $c - d$:** For nearly proportional sorted spectral lobes $\lambda_{+,i} / \lambda_{-,i} \approx (1 + t_i)/(1 - t_i)$, $\lambda_{+,i}^2 - \lambda_{-,i}^2 = \sigma_i^2 t_i$, and $((\lambda_+ - \lambda_-)_+^2 - (\lambda_+ - \lambda_-)_-^2)/\|L\|_F^2$ reduces to $\sum_i w_i t_i |t_i|$ (`corr` $= 0.997$ in both GPT-2 and Candidates 1–3).

### 2.4 Summary of capabilities by candidate

| Empirical target | Cand. 1 ($2\text{p}: \mu, \tau$) | Cand. 2 ($2\text{p}: r_0, \gamma$) | Cand. 3 ($3\text{p}: r_0, \gamma, \nu$) |
|---|---|---|---|
| `tbar`, `tstd`, $c - d$, $\operatorname{Corr}(c-d, \sum w_i t_i |t_i|) \approx 0.997$ | **Yes** | **Yes** | **Yes** |
| High `diagfrac` ($0.18$) without inflating `err1` / negative $a - b$ | Partial (mixing leak) | **Yes** ($r = 0.96$) | **Yes** ($r = 0.96$) |
| `offrms` $\approx 0.048$ and negative correlation with $|\bar{t}|$ | Weak ($r = -0.23$) | **Yes** ($r = -0.78$) | **Yes** ($r = -0.63$) |
| Endogenous $\Sigma$ (`PR` $\approx 45.7$) & $\operatorname{Corr}(\mathrm{PR}, \mathrm{std}(t_i)) < 0$ | No (needs external $\kappa$) | **Yes** (0 $\Sigma$-params) | **Yes** (0 $\Sigma$-params) |
| Top-vs-bulk tilt ($\operatorname{Corr}(i, t_i) < 0$) & bimodal/skewed $t_i$ ranges | No ($s_i \perp r_i$) | **Yes** | **Yes** |
| Positive $(a - b > 0)$ tail (`L0H3`, `L0H4`, `L0H7`) & `lnfold` surge | No ($a - b \le 0$ bias) | No ($a - b \lesssim 0$) | **Yes** ($2\times 2$ skew pairs) |

---

## 3. Numerical Validation Against GPT-2 Weights

All experiments were run against `gpt2_model.safetensors` and `gpt2_W.csv` using reproducible scripts saved in `./` (`evaluate_ensembles.py`, `test_monotone_cand2.py`, `fit_and_evaluate.py`, `explore_deep.py`, `explore_gram.py`, `explore_bulk_spikes.py`).

### 3.1 Per-head parameter fitting protocol (144 heads)
To avoid tautological overfitting, we fixed $N_{\text{eff}} = 430$ globally across all 144 heads and fitted per-head parameters **exclusively to summary moments**, evaluating all remaining statistics out-of-target on fresh random draws ($n = 64, N = 768$):
- **Candidate 1 ($2\text{p}$):** $(\mu_h, \tau_h)$ fitted to $(\bar{t}_h, \mathrm{tstd}_h)$ (with global $\kappa = 20$).
- **Candidate 2 ($2\text{p}$):** $(r_{0,h}, \gamma_h)$ fitted only to the within-head $t_i$ moments $(\bar{t}_h, \bar{t}_{\text{unw},h}, \mathrm{tstd}_h)$—**never touching $\Sigma$, `PR`, `diagfrac`, `offrms`, `err1`, $a - b$, or $c - d$**. Across the 144 heads, fitted $r_0$ has median $-0.051$ ($[-0.528, +0.350]$) and fitted $\gamma$ has median $+0.250$ ($[-0.375, +0.500]$, with $55.6\%$ having $\gamma > 0$).
- **Candidate 3 ($3\text{p}$):** Activates $\nu_h > 0$ only on heads whose measured $a - b$ exceeds Candidate 2's baseline by $> 0.012$ ($55/144$ heads, mean active $\nu = 0.34$).

### 3.2 Ensemble distribution comparison (median [10th, 90th percentile] across 144 heads)
Table 1 compares the 144 trained GPT-2 heads (raw $L$) against **one single synthetic matrix draw $(Q_h, K_h) \in \mathbb{R}^{64 \times 768}$ per head** from each fitted ensemble (`evaluate_ensembles.py`), alongside the $3\text{p}$ rotary refinement from `test_monotone_cand2.py`:

| Statistic | GPT-2 Trained (raw) | Cand. 1 ($2\text{p}: \mu, \tau$) | Cand. 2 ($2\text{p}: r_0, \gamma$) | Cand. 3 ($3\text{p}: r_0, \gamma, \nu$) |
|---|---|---|---|---|
| Diagonal share $\sum t_i^2 / \|W\|_F^2$ | `0.184 [0.039, 0.552]` | `0.115 [0.023, 0.412]` | **`0.158 [0.038, 0.523]`** | **`0.150 [0.029, 0.509]`** |
| $\bar{t} = \sum w_i t_i$ | `+0.003 [-0.192, +0.243]` | `+0.012 [-0.233, +0.278]` | **`+0.021 [-0.223, +0.262]`** | **`+0.018 [-0.198, +0.255]`** |
| Within-head $\mathrm{std}(t_i)$ ($\sigma^2$-wtd) | `0.092 [0.057, 0.246]` | `0.063 [0.048, 0.120]` | **`0.089 [0.052, 0.240]`** | **`0.082 [0.050, 0.230]`** |
| Off-diagonal RMS of $W$ | `0.048 [0.042, 0.054]` | `0.047 [0.045, 0.057]` | **`0.046 [0.044, 0.048]`** | **`0.047 [0.045, 0.051]`** |
| Relative error of (1), `err1` | `0.059 [0.037, 0.156]` | `0.032 [0.016, 0.188]` | **`0.039 [0.014, 0.115]`** | **`0.045 [0.016, 0.116]`** |
| $a - b$ | `-0.012 [-0.056, +0.020]` | `-0.017 [-0.129, -0.003]` | `-0.015 [-0.066, -0.002]` | **`-0.014 [-0.051, +0.023]`** |
| $c - d$ | `+0.000 [-0.066, +0.062]` | `+0.000 [-0.051, +0.071]` | **`+0.004 [-0.049, +0.079]`** | **`+0.001 [-0.057, +0.070]`** |
| Participation ratio $\mathrm{PR}(\Sigma)$ | `45.7 [24.6, 52.5]` | `42.6 [40.5, 43.9]` | **`46.2 [35.1, 49.0]`** | **`44.9 [30.2, 48.1]`** |

### 3.3 Head-by-head predictive accuracy & secondary correlations across the 144 heads
Comparing Monte Carlo ensemble means per head against true GPT-2 values across all 144 heads (`evaluate_ensembles.py` & `test_monotone_cand2.py`):

| Statistic | Cand. 1 ($r$ / MAE) | Cand. 2 ($r$ / MAE) | Cand. 3 ($r$ / MAE) | Notes on out-of-target prediction |
|---|---|---|---|---|
| `diagfrac` | `+0.829` / `0.086` | **`+0.959` / `0.041`** | `+0.957` / `0.046` | Pure prediction from $(r_0, \gamma)$ + $N_{\text{eff}}$ |
| `offrms` | `+0.331` / `0.005` | **`+0.507` / `0.004`** | `+0.417` / `0.004` | Captures contraction damping $\sqrt{(1-\overline{t^2})/N_{\text{eff}}}$ |
| `err1` | `+0.504` / `0.052` | `+0.499` / `0.042` | **`+0.676` / `0.036`** | Skew parameter $\nu$ explains high-`err1` outliers |
| $a - b$ | `+0.191` / `0.042` | `+0.197` / `0.032` | **`+0.673` / `0.023`** | Matches negative bulk & positive rotary tail (`+0.023`) |
| $c - d$ | `+0.990` / `0.010` | `+0.979` / `0.011` | **`+0.990` / `0.010`** | Matches $c - d$ to $0.01$ MAE |
| `PR` ($\Sigma$) | `-0.042` / `8.79` | `+0.416` / `7.14` | **`+0.462` / `6.98`** | **Zero per-head parameters fitted to $\Sigma$** |

Secondary cross-head invariants in `brief.md`:
- $\operatorname{Corr}(c - d,\; \sum w_i t_i |t_i|)$: GPT-2 **`0.9972`**, Cand. 2 **`0.9974`**, Cand. 3 **`0.9979`**.
- $\operatorname{Corr}(|\bar{t}|,\; \text{diag share})$: GPT-2 **`0.852`**, Cand. 2 **`0.867`**, Cand. 3 **`0.882`**.
- $\operatorname{Corr}(\text{err1},\; \mathrm{std}(t_i))$: GPT-2 **`0.464`**, Cand. 3 **`0.464`–`0.468`**.
- Share of heads with $|\bar{t}| > 2\,\mathrm{std}(t_i)$: GPT-2 **`24.3%`**, Cand. 2 **`29.9%`–`31.2%`**, Cand. 3 **`32.6%`**.
- Median $\operatorname{Corr}(\text{index } 1\dots 64,\; t_i)$ on $|\bar{t}| > 0.05$: GPT-2 **`-0.108`**, Signed-Spike $2\text{p}$ **`-0.092`**, Signed-Spike + Skew $3\text{p}$ **`-0.107`**.

### 3.4 Named head case studies & the LayerNorm-folding (`lnfold`) mechanism
- **`L1H1` & `L5H9` (weak/moderate $\bar{t}$, huge bimodal $t_i$ range):** In GPT-2, `L1H1` has $\bar{t} = -0.138, \mathrm{std}(t_i) = 0.348, t_i \in [-0.68, +0.48], \mathrm{diagfrac} = 0.540, \mathrm{PR} = 31.4$. A single Candidate 3 draw at $(r_0 = -0.80, \gamma = +0.62, \nu = 0.38)$ gives $\bar{t} = -0.152, \mathrm{std}(t_i) = 0.303, t_i \in [-0.60, +0.43], \mathrm{diagfrac} = 0.523, \mathrm{offrms} = 0.051, \mathrm{PR} = 31.6$.
- **`L0H5` ($\bar{t} = +0.911$, $t_i \in [-0.023, +0.946]$, $\mathrm{PR} = 54.1$):** In GPT-2, modes $2\dots 64$ sit in $[+0.82, +0.95]$ while a single top outlier sits at $t_1 = -0.023$ (which rises to $+0.181$ after `lnfold` removes the residual-stream mean). Candidate 2 at $(r_0 = +0.94, \gamma = -0.35)$ places 62 bulk modes in $[+0.82, +0.95]$ with $\mathrm{PR} \approx 50$ while pulling the largest $\chi_1^2$ spike down to $r_1 \approx -0.02$ and damping `offrms` to $0.022$ (GPT-2: $0.0245$).
- **`L0H3` (positional rotary head, $a - b = +0.195, \mathrm{PR} = 17.5$):** Candidate 2 cannot produce $a - b > 0$ ($a - b = -0.020$), whereas Candidate 3 ($\nu > 0$) creates a near-degenerate top singular pair ($\sigma_2 / \sigma_1 \approx 0.98$) with $W_{12} \approx -W_{21} \approx 0.70$, driving $a - b > 0$ and lowering $\mathrm{PR}$ to $\sim 20$.
- **Why `lnfold` collapses $\mathrm{PR} \to 4$ and boosts $|a - b| > 0.1$ to $20\%$ of heads:** Inspecting `ln_1.weight` in `evaluate_ensembles.py` reveals strong residual-stream outlier coordinates (e.g., Layer 2 `ln_1.weight` has median $0.234$ but reaches $0.944$ on coordinate $745$—a $16\times$ gain in $g^2$—and `L2H2`'s key columns have norm $5.34$ vs median $1.30$ on those exact 5 coordinates!). Folding $\operatorname{diag}(g) P$ into $(Q, K)$ multiplies those aligned feature channels by $\sim 16 \times 16 = 256\times$ in energy, driving effective $|\gamma|$ and $\nu$ into the $\gg 1$ spike-dominated regime where $\mathrm{PR} \to 4\text{–}6$ and $2 \times 2$ non-normal blocks dominate $a - b$ (`L2H2` jumps from raw $a - b = +0.006, \mathrm{PR} = 31.5$ to `lnfold` $a - b = +0.489, \mathrm{PR} = 3.7$).

---

## 4. Which Candidate Is Most Natural, and What Would Falsify It?

### Most natural candidate: Candidate 2 (with Candidate 3 as its non-normal completion)
If we ask for **one natural 2-parameter random-matrix ensemble**, **Candidate 2 (Signed-Spike Correlated Gaussian)** is the clear winner:
1. **Minimal algebraic ingredients:** It uses *only* isotropic/covariant Gaussian matrices $(X_0, Y_0, F)$ and a Gaussian vector $g \sim \mathcal{N}(0, I_n)$ combined linearly:
   $$Q = X_0 + |\gamma|\,\operatorname{diag}(g)\, F, \qquad K = \left(r_0 X_0 + \sqrt{1 - r_0^2}\, Y_0\right) + \gamma\,\operatorname{diag}(g)\, F.$$
   It nests the independent Gaussian null at $(r_0, \gamma) = (0, 0)$ and the scalar-correlated Gaussian model at $\gamma = 0$.
2. **Unifies $\Sigma$ and $W$ with 2 parameters:** Without introducing an external Gamma shape parameter, the $\chi_1^2$ feature-energy hierarchy $s_i = 1 + \gamma^2 g_i^2$ simultaneously predicts GPT-2's median $\mathrm{PR}(\Sigma) \approx 46$, head-by-head $\mathrm{PR}$ correlation ($r = +0.42$), monotone alignment-vs-singular-value tilt, bimodal within-head $t_i$ spans, `diagfrac` ($r = +0.96$), and `offrms` ($0.046$).
3. **Principled boundary of validity:** The *only* qualitative feature Candidate 2 misses is $a - b > 0$ (because $1 \times 1$ real channels cannot represent antisymmetric cross-feature couplings). **Candidate 3** resolves this cleanly via the real Schur decomposition—adding $2 \times 2$ symplectic pairs $\Omega J F_{\text{rot}}$ controlled by $\nu \ge 0$—so $(r_0, \gamma, \nu)$ captures both symmetric feature matching and directed/positional shifts.

### Concrete falsification criteria
Candidate 2 (and its $\nu$-completion Candidate 3) makes sharp, quantitative predictions that would **falsify** it if violated on other models or training runs:

1. **Scaling of off-diagonal $W$ with embedding dimension $N$ (`offrms` $\propto N_{\text{eff}}^{-1/2}$, independent of $n$):** Across models of varying width $N \in [512, 5120]$ (e.g., Pythia-70M through OPT-13B and Mistral-24B), Candidate 2 predicts $\mathbb{E}[W_{ij}^2]_{i \neq j} \approx (1 - \overline{t^2}) / N_{\text{eff}}(L_{\text{res}})$, scaling as $O(1/N)$ rather than $O(1/n)$. Finding `offrms` scaling as $1/\sqrt{n}$ at large $N / n \gg 10$ would falsify channel co-diagonalizability in favor of a head-space-mixed coupling.
2. **Within-head monotonicity vs random scatter of $(s_i, t_i)$:** Candidate 2 predicts a smooth trend $t_i \approx \varepsilon + (r_0 - \varepsilon)/s_i$ (up to $O(1/\sqrt{N_{\text{eff}}})$ fluctuations and a small number of rotary pairs). If heads with large $\mathrm{std}(t_i)$ in larger models (`n = 128`) frequently exhibit alternating $+0.8$ and $-0.8$ alignments interlaced throughout the *middle* of the singular spectrum without singular-value separation, the single-parity spike law $\varepsilon = \operatorname{sign}(\gamma)$ would be falsified (requiring independent bivariate loadings $(\alpha_i, \beta_i)$ per channel).
3. **Architectural test of Candidate 3's rotary parameter $\nu$ (Learned PE vs ALiBi / RoPE):** We identified large positive $(a - b > 0)$ raw heads in GPT-2 (`L0H3, L0H4, L0H7`) with $2 \times 2$ positional-shift blocks learned because GPT-2 adds absolute positional embeddings to the residual stream. In **ALiBi** or **RoPE** models (where relative position is handled outside the base $d = 0$ content matrix $K^\top Q$), Candidate 3 predicts significantly fewer raw heads with large $a - b > +0.10$ in early layers; finding an identical early-layer surge of $2 \times 2$ rotation blocks in ALiBi's $K^\top Q$ would falsify the positional-shift explanation of $\nu$ (pointing instead to general directed semantic bigram circuits).
4. **Training-trajectory dynamics from $(0, 0)$:** Over training checkpoints $t = 0 \to T$, fitted $(r_0(t), \gamma(t), \nu(t))$ must start at $(0, 0, 0)$ ($\mathrm{PR} \approx 55$, profile $(\frac{1}{2}, \frac{1}{2}, 0, 0)$) and grow smoothly while maintaining $\mathrm{PR}(\Sigma(t))$ near the parameter-free curve $\mathrm{PR}(\gamma(t))$ in §2.3. A head whose $\mathrm{PR}(\Sigma)$ stays flat at $\approx 55$ while developing a wide bimodal $t_i \in [-0.7, +0.7]$ spread would falsify the additive spike mechanism $s_i = 1 + \gamma^2 g_i^2$, proving instead that training rotates $Q$ relative to $K$ at unit singular-value norm (as in Candidate 1 with large $\kappa$).
