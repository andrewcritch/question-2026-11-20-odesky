**Verdict:** The core finite-$n$ characterization in R13(1)–(3) and the fixed-$n$, $N\to\infty$ convergence argument in R14 are sound, **but** R14 contains a false conclusion on line 161 ("The position along $\Theta$ is set by the law of $(f-g)/(f+g)$"), an unstated iterated-limit restriction in "$c-d\to\dots$" as $n\to\infty$ (line 161), and two inaccurate special-case claims (line 165), while R13(4) overreaches at the two endpoints of $\Theta$ because line 135 restricts $t_i\in(-1,1)$.

---

## 1. Failed justifications and overbroad conclusions

### 1.1. Line 161 (R14, Theorem, final sentence): False claim that the law of $(f-g)/(f+g)$ determines the position along $\Theta$

> *"The position along $\Theta$ is set by the law of $(f-g)/(f+g)$."* (line 161)

This is **false**, both at finite $n$ (for $\pi_\infty$) and in the $n\to\infty$ limit. Write $S(\rho)=f(\rho)+g(\rho)>0$ for channel scale and $T(\rho)=\frac{f(\rho)-g(\rho)}{f(\rho)+g(\rho)}\in(-1,1)$ for channel alignment. The preceding formula on line 161 gives
$$c_\infty - d_\infty \;\xrightarrow[n\to\infty]{\text{a.s.}}\; \frac{\mathbb E[(f-g)|f-g|]}{\mathbb E[(f+g)^2]} \;=\; \frac{\mathbb E\!\left[S(\rho)^2\,T(\rho)|T(\rho)|\right]}{\mathbb E\!\left[S(\rho)^2\right]}.$$
Thus the limiting position along $\Theta$ is the **$S(\rho)^2$-size-biased expectation** of $T(\rho)|T(\rho)|$, not a functional of the marginal law of $T(\rho)=(f-g)/(f+g)$ under $\mu$. (Likewise at finite $n$, R13(3) gives $c_\infty-d_\infty=\sum_i w_i t_i|t_i|$ with weights $w_i \propto S(\rho_i)^2$.)

**Explicit counterexample.** Let $\mu=\tfrac12\delta_0+\tfrac12\delta_1$. Consider two ensembles $\mathcal E(\mu;f_1,g_1)$ and $\mathcal E(\mu;f_2,g_2)$ with continuous, positive, strictly increasing $f_k,g_k:\mathbb R\to(0,\infty)$ satisfying $f_k-g_k\ge 0$ everywhere, interpolated linearly between $\rho=0$ and $\rho=1$:

- **Ensemble 1:** $(f_1(0),g_1(0))=(1,1)$ and $(f_1(1),g_1(1))=(18,2)$, so $S_1(0)=2,\ T_1(0)=0$ and $S_1(1)=20,\ T_1(1)=0.8$.
- **Ensemble 2:** $(f_2(0),g_2(0))=(1.8,0.2)$ and $(f_2(1),g_2(1))=(10,10)$, so $S_2(0)=2,\ T_2(0)=0.8$ and $S_2(1)=20,\ T_2(1)=0$.

Under $\mu$, $(f_k(\rho)-g_k(\rho))/(f_k(\rho)+g_k(\rho))$ has the **exact same law** $\tfrac12\delta_0+\tfrac12\delta_{0.8}$ in both ensembles (and even the exact same marginal law of $f_k+g_k$, namely $\tfrac12\delta_2+\tfrac12\delta_{20}$). Yet as $N\to\infty$ followed by $n\to\infty$:
- Ensemble 1 gives $c_\infty - d_\infty \to \frac{\frac12(0)+\frac12(16^2)}{\frac12(2^2)+\frac12(20^2)} = \frac{128}{202} = \frac{64}{101} \approx 0.6337$, so $\pi_\infty \to (0.1832,\,0.1832,\,0.6337,\,0)$.
- Ensemble 2 gives $c_\infty - d_\infty \to \frac{\frac12(1.6^2)+\frac12(0)}{\frac12(2^2)+\frac12(20^2)} = \frac{1.28}{202} = \frac{0.64}{101} \approx 0.0063$, so $\pi_\infty \to (0.4968,\,0.4968,\,0.0063,\,0)$.

Numerical simulation at $n=200,\ N=20{,}000$ gives $c-d=0.6349$ vs. $0.0061$ (a $100\times$ change in $c-d$). Because coupling channel strength $S(\rho)$ to alignment $T(\rho)$ is the defining mechanism of $\mathcal E(\mu;f,g)$ (and of R9), the position along $\Theta$ is set by the **joint** law of $(f+g,\,(f-g)/(f+g))$ (equivalently, the $(f+g)^2$-tilted law of $(f-g)/(f+g)$), not the law of $(f-g)/(f+g)$ alone.

---

### 1.2. Line 161 (R14, Theorem, third sentence): "$c-d\to\dots$" holds only for the iterated limit $c_\infty - d_\infty$ (or $N/n\to\infty$), not general $n\to\infty$

> *"If moreover $f-g$ has one sign and $n\to\infty$, then $c-d\to\mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]$ almost surely (from R13(3) with $\sigma_i=\alpha_i+\beta_i$ and $\sigma_it_i=\alpha_i-\beta_i$, plus the strong law of large numbers, assuming $\mathbb E[(f+g)^2]<\infty$)."* (line 161)

In the immediately preceding sentence, $a-b$ (without subscript $\infty$) denotes the finite-$(n,N)$ profile coordinate of $L$, while $\pi_\infty$ denotes the $N\to\infty$ limit at fixed $n$. What the parenthetical argument proves is **only** convergence of $c(\pi_\infty)-d(\pi_\infty)$—that is, the **iterated** limit $\lim_{n\to\infty}\lim_{N\to\infty}(c(L)-d(L))$.

If read as a statement about $c(L)-d(L)$ when $n\to\infty$ in the proportional regime $N=\kappa n$ ($\kappa\ge 2$, matching `question.md` line 23's condition $n\le N/2$), the limit formula **fails** even for constant $f\equiv\alpha>0,\ g\equiv\beta>0$ ($\alpha\ne\beta$). Specifically, summing the $n(n-1)$ off-diagonal inner-product terms in $\|L\|^2=\sum_{i,j}(q_i\cdot q_j)(k_i\cdot k_j)$ and $\mathrm{tr}(L^2)=\sum_{i,j}(k_i\cdot q_j)(k_j\cdot q_i)$ gives, as $n\to\infty$ with $N/n\to\kappa\in[2,\infty)$,
$$\frac{1}{n}\|L\|^2 \to (\alpha+\beta)^2 + \frac{1}{\kappa}(\alpha-\beta)^2,\qquad \frac{1}{n}\mathrm{tr}(L^2) \to \left(1+\frac{1}{\kappa}\right)(\alpha-\beta)^2,$$
so
$$1-2a = \frac{\mathrm{tr}(L^2)}{\|L\|^2} \;\longrightarrow\; \frac{(1+1/\kappa)(\alpha-\beta)^2}{(\alpha+\beta)^2 + (1/\kappa)(\alpha-\beta)^2} \;\ne\; \frac{(\alpha-\beta)^2}{(\alpha+\beta)^2}.$$
At $\alpha=2,\ \beta=1,\ \kappa=2$ ($n=1024,\ N=2048$), the iterated limit predicts $1-2a_\infty = c_\infty - d_\infty = \tfrac19 \approx 0.11111$ and $a_\infty-b_\infty=0$, whereas simulation gives $1-2a=0.15830$ (matching $\tfrac{3}{19}\approx 0.15789$), $c-d=0.16540$, and $a-b=+0.00710$. Line 161 should write **$c_\infty - d_\infty \to \dots$** explicitly.

*(Side note on the same sentence: $c_\infty-d_\infty \to \mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]$ actually holds by R13(3) and SLLN even when $f-g$ changes sign; the one-sign hypothesis is needed only to conclude $c_\infty d_\infty=0$ so that $c_\infty-d_\infty$ parameterizes $\Theta$.)*

---

### 1.3. Lines 135 and 141 (R13, Setting and Theorem item 4): Endpoints of $\Theta$ are not attained under $t_i\in(-1,1)$, and $t_i\in(-1,1)$ is narrower than $W=\mathrm{diag}(t_i)$ in R1

> **Line 135:** *"… $t_i=u_i^\top v_i\in(-1,1)$, and the planes $\mathrm{span}(u_i,v_i)$ mutually orthogonal (equivalently $W=\mathrm{diag}(t_i)$ in R1)."*  
> **Line 141:** *"4. Hence, within this setting, $\pi(L)\in\Theta$ if and only if $(\alpha,\beta)$ is comonotone and all $t_i$ have one sign. Every point of $\Theta$ is attained (e.g. $t_i\equiv t$)."*

Two boundary mismatches arise from restricting $t_i$ to the open interval $(-1,1)$:

1. **Non-attainment of the two endpoints of $\Theta$ (line 141).** By `question.md` lines 46 and 61 (and `record.md` line 147), $\Theta=\{a=b,\ cd=0\}\subset\Delta$ is the union of two closed segments and contains the symmetric rank-one vertices $(0,0,1,0)$ ($t=+1$, $L=uu^\top$) and $(0,0,0,1)$ ($t=-1$, $L=-uu^\top$). Within the setting of line 135 ($\sigma_i>0$ and $t_i\in(-1,1)$ for all $i$),
   $$a = \frac{\|T\|^2}{\|L\|^2} = \frac{1}{2}\sum_{i=1}^n w_i(1-t_i^2) > 0$$
   strictly, so only $\Theta\setminus\{(0,0,1,0),(0,0,0,1)\}$ is attained. (Likewise in R14, since $f,g:\mathbb R\to(0,\infty)$ are strictly positive, $\pi_\infty$ never attains those two vertices.)
2. **Inexact equivalence with R1 at $t_i=\pm 1$ (line 135).** R1 (line 9) states that *"every contraction $W$ is realized"*, so $W=\mathrm{diag}(t_i)$ in R1 allows $t_i\in[-1,1]$ ($L$ still has rank $n$ and orthonormal SVD frames $U,V$). When $t_i=\pm 1$, $v_i=\pm u_i$ spans a $1$-dimensional line rather than a $2$-plane, and $\beta_i=0$ or $\alpha_i=0$. If line 135 is relaxed to $t_i\in[-1,1]$ with mutually orthogonal subspaces $\mathrm{span}(u_i,v_i)$ of dimension $1$ or $2$ (zero-padding $\lambda_\pm$ to length $n$, which agrees with `question.md` line 61 at $t=\pm 1$), both the equivalence with $W=\mathrm{diag}(t_i)$ (for $N\ge 2n$) and full attainment of $\Theta$ in R13(4) hold as written.

---

### 1.4. Line 165 (R14, Special cases): Two overbroad or misassigned special cases

> *"**Special cases.** $g\equiv$ const: Antigravity's signed-spike ensemble (R9) in the limit. $f/g\equiv$ const: one tilt per head, the correlated Gaussian model of the question. $f,g$ constant: the independent Gaussian model ($f=g$) and its correlated version."* (line 165)

1. **$g\equiv\text{const}$ covers R9 only for $\gamma\ge 0$, not $\gamma<0$.** In R9 (line 97), $Q=X_0+|\gamma|\,\mathrm{diag}(z)F$ and $K=r_0X_0+\sqrt{1-r_0^2}\,Y_0+\gamma\,\mathrm{diag}(z)F$ with $z\sim N(0,I_n)$. In the isotropic $N\to\infty$ limit (with $\rho_i=z_i^2$),
   $$Q+K = (1+r_0)X_0 + \sqrt{1-r_0^2}\,Y_0 + (|\gamma|+\gamma)\,\mathrm{diag}(z)F,\qquad K-Q = (r_0-1)X_0 + \sqrt{1-r_0^2}\,Y_0 + (\gamma-|\gamma|)\,\mathrm{diag}(z)F.$$
   For $\gamma\ge 0$, $\beta_i=\frac{1-r_0}{2}\equiv\text{const}$ ($g\equiv\text{const}$) and $\alpha_i=\frac{1+r_0}{2}+\gamma^2\rho_i$. For **$\gamma<0$**, however, $|\gamma|+\gamma=0$ cancels the spike in $Q+K$ instead of $K-Q$, giving **$\alpha_i=\frac{1+r_0}{2}\equiv\text{const}$ ($f\equiv\text{const}$)** and $\beta_i=\frac{1-r_0}{2}+\gamma^2\rho_i$ non-constant (verified numerically at $N=40{,}000,\ \gamma=\pm 0.6$). Moreover, whenever $r_0\gamma<0$, $f-g$ changes sign on $\mathrm{supp}(\chi^2_1)=[0,\infty)$, so R9's limit has $a_\infty=b_\infty$ and exact relation (1) but $c_\infty d_\infty>0$ ($\pi_\infty\notin\Theta$).
2. **$f/g\equiv\text{const}$ is not the correlated Gaussian model of `question.md` line 59.** The question's correlated Gaussian model $K=rQ+\sqrt{1-r^2}\,G$ with i.i.d. Gaussian $Q,G$ has **both $f$ and $g$ constant** (as the third sentence of line 165 itself states). Allowing $f/g\equiv\text{const}$ with non-constant $g(\rho)$ produces random heterogeneous row scales $\sqrt{f(\rho_i)+g(\rho_i)}$ (Candidate A of R7 at $s=0$), though its $N\to\infty$ *profile* $\pi_\infty$ agrees with the correlated Gaussian profile by R2.

---

### 1.5. Minor precision and undefined-term notes (lines 141, 161, 163)

- **Undefined "relation-(1) error" and domain of continuity (lines 161, 163).** Neither `question.md` nor `record.md` defines a scalar "relation-(1) error". Line 163 asserts that the profile and relation-(1) error *"are continuous functions of $M_N$ wherever $\|L\|\ne 0$ and $\sigma(T)\ne 0$"*. First, $M_N$ must be restricted to $\mathrm{PSD}_{2n}$ (for general $2n\times 2n$ matrices $M$, $J'M$ can have complex eigenvalues). Second, vector nonvanishing $\sigma(T)\ne 0$ suffices for `comono.py`'s $\ell_2$-normalized error $\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|_2/\|\sigma(T)\|_2$, whereas per-index relative error (line 23) or log-ratio error (R5, line 45) requires $\sigma(T)_k>0$ for *every* $k=1,\dots,n$ (equivalently $M_N\succ 0$). Because $M_\infty\succ 0$ has $\sigma(T)_k=\sqrt{f(\rho_k)g(\rho_k)}>0$ for all $k$, continuity on a neighborhood of $M_\infty$ in $\mathrm{PD}_{2n}$ holds under all of these definitions, so the $N\to\infty$ conclusion is unaffected.
- **"Have one sign" at zero (lines 141, 161).** *"all $t_i$ have one sign"* (line 141) and *"$f-g$ has one sign"* (line 161) must be read non-strictly, i.e. $(\forall i,\,t_i\ge 0)\lor(\forall i,\,t_i\le 0)$; under a strict reading ($t_i>0$ or $t_i<0$), the "only if" direction of R13(4) fails whenever some $t_i=0$ (e.g. $t_i\equiv 0$ gives $(\tfrac12,\tfrac12,0,0)\in\Theta$), and $f=g$ (line 165) would not satisfy line 161.
- **Unintroduced notation and symbol overloading (line 163).** $\Pi,\Delta$ and their rows $\pi_i,\delta_i$ (implicitly $\Pi=(Q+K)/2,\ \Delta=(K-Q)/2$) appear without definition on line 163, overloading $\pi$ with the profile map $\pi(L)$ in the same paragraph (and the permutation $\pi$ in R13).

---

## 2. Solid parts of the proofs and the step checked hardest

### Solid components verified

- **R13(1)–(3) and their proofs (lines 138–140, 143–146):** Completely solid within line 135's setting. The block spectral formulas from R2 ($\lambda_+=\alpha^\downarrow$, $\lambda_-=\beta^\downarrow$, $\sigma(T)=(\sqrt{\alpha\beta})^\downarrow$, $\|T\|^2=2\sum\alpha_i\beta_i$), the strict rearrangement step for discordant pairs, the tie-breaking construction of a common sorting permutation $\pi$ when $(\alpha,\beta)$ is comonotone, the monotonicity of $k\mapsto\sqrt{\alpha_{\pi(k)}\beta_{\pi(k)}}$, and the identity $\lambda_{+,k}-\lambda_{-,k}=\sigma_{\pi(k)}t_{\pi(k)}$ yielding $c-d=\sum_i w_i t_i|t_i|$ all hold without gaps. (In fact, the converse of R13(2) also holds here: exact relation (1) at all sorted indices implies $\sum\alpha_i\beta_i=\langle\alpha^\downarrow,\beta^\downarrow\rangle$, hence $a=b$ and comonotonicity.)
- **R13 balanced-channel form and GPT-2 check (lines 149–153):** Under $|q_i|=|k_i|>0$ and mutually orthogonal $2$-planes $\mathrm{span}(q_i,k_i)$, $|q_i+k_i|^2/4=\sigma_i(1+t_i)/2=\alpha_i$ and $|k_i-q_i|^2/4=\sigma_i(1-t_i)/2=\beta_i$ (and $(q_i+k_i)\perp(k_i-q_i)\iff|q_i|=|k_i|$). Inspection of `comono.py` confirms the script computes these exact quantities.
- **R14 scaling, fixed-$n$ limit as $N\to\infty$, and SLLN integrability (lines 157–160, 161 first two sentences, 163):** All factors of $2$ check out ($q_i=(\sqrt{f(\rho_i)}p_i-\sqrt{g(\rho_i)}m_i)/\sqrt N$, $k_i=(\sqrt{f(\rho_i)}p_i+\sqrt{g(\rho_i)}m_i)/\sqrt N$, so $|q_i|^2,|k_i|^2\to f(\rho_i)+g(\rho_i)$, $q_i\cdot k_i\to f(\rho_i)-g(\rho_i)$, and $S_\infty=\Pi^\top\Pi-\Delta^\top\Delta$ has nonzero eigenvalues $f(\rho_i)$ and $-g(\rho_i)$). Monotonicity of $f,g$ guarantees $(\alpha,\beta)=(f(\rho_i),g(\rho_i))_{i=1}^n$ is comonotone for every realization of $\rho$ (including ties in $\rho_i$ or discontinuities of $f,g$). For the iterated $n\to\infty$ limit of $c_\infty-d_\infty$, $f,g>0$ implies $|(f-g)|f-g||=(f-g)^2<(f+g)^2$ and $\mathbb E[(f+g)^2]>0$, so $\mathbb E[(f+g)^2]<\infty$ suffices for SLLN in both numerator and denominator.

### Step checked hardest

The step I checked hardest was **the dimension-reduction and spectral-continuity step in R14's proof (line 163)**: reducing the $N\times N$ spectra of $2S,2T$ and $\|L\|^2$ (whose ambient dimension $N\to\infty$ grows) to continuous functions of the fixed-size $2n\times 2n$ Gram matrix $M_N=FF^\top$ via R5. Specifically, I checked five potential failure modes:

1. **R5's surjectivity hypothesis vs. finite $N$:** R5 assumes $\operatorname{rk}F=2n$ ($M_N\succ 0$), which fails for $N<2n$. However, for fixed $n$ and $N\ge 2n$, Gaussianity and $f(\rho_i),g(\rho_i)>0$ give $M_N\in\mathrm{PD}_{2n}$ almost surely, and the SLLN limit
   $$M_\infty = \begin{pmatrix} D_f+D_g & D_f-D_g \\ D_f-D_g & D_f+D_g \end{pmatrix}$$
   is orthogonally congruent to $\mathrm{diag}(2D_g,2D_f)\succ 0$, hence lies strictly inside the open cone $\mathrm{PD}_{2n}$.
2. **Eigenvalues vs. singular values of non-normal matrices $J'M_N$ and $\Omega M_N$:** Although $\Omega M_N$ has singular values equal to the eigenvalues of $M_N$ (not $2\sigma(T)$), R5 and line 163 use the *eigenvalue* spectra: on $\mathrm{PD}_{2n}$, $J'M_N \sim M_N^{1/2}J'M_N^{1/2}$ (real symmetric, inertia $(n,n)$ by Sylvester's law) has eigenvalues $\{2\lambda_{+,k}\}\cup\{-2\lambda_{-,k}\}$, and $\Omega M_N \sim M_N^{1/2}\Omega M_N^{1/2}$ (real skew-symmetric, invertible) has purely imaginary eigenvalues $\{\pm 2i\sigma(T)_k\}$. By continuity of $M\mapsto M^{1/2}$ on $\mathrm{PD}_{2n}$ and Weyl's perturbation inequality, the sorted positive/negative lists $\lambda_+,\lambda_-$ and singular-value list $\sigma(T)$ are continuous at $M_\infty$ even when $\rho_i$ has ties (degenerate eigenvalues).
3. **Polynomiality of $\|L\|^2$ in $M_N$:** Verified directly via $\|L\|^2=\mathrm{tr}(Q^\top KK^\top Q)=\mathrm{tr}(QQ^\top KK^\top)=\mathrm{tr}((M_N)_{11}(M_N)_{22})$, with $\|L_\infty\|^2=\sum_{i=1}^n(f(\rho_i)+g(\rho_i))^2>0$.
4. **Probability coupling across $N$ for "almost surely":** Line 157 does not specify whether $(P,M)$ for increasing $N$ come from growing prefixes of infinite Gaussian arrays $P,M\in\mathbb R^{n\times\mathbb N}$ (where SLLN applies directly) or independent draws per $N$; because rows are Gaussian, sub-exponential concentration gives $\sum_{N=1}^\infty \mathbb P(\|M_N-M_\infty\|>\varepsilon)<\infty$, so Borel–Cantelli yields almost-sure convergence under *every* coupling across $N$.
5. **Tie-breaking in R13(1) (line 144):** Checked all tie configurations $(\alpha_i=\alpha_j,\ \beta_i\ne\beta_j)$ and $(\alpha_i\ne\alpha_j,\ \beta_i=\beta_j)$ under $(\alpha_i-\alpha_j)(\beta_i-\beta_j)\ge 0$; lexicographic decreasing order on $(\alpha_k,\beta_k)$ always sorts both vectors simultaneously.
