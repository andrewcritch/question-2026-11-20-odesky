**Verdict: R13 and R14 are sound in their main claims. There is one overbroad conclusion in R14 (record.md line 154, "The position along Θ is set by the law of (f−g)/(f+g)"), which a counterexample refutes. There is one small overstatement in R13 (line 141, "Every point of Θ is attained"), which fails at the two vertices of Θ. The other issues are minor and concern wording and how the argument is justified.**

Script: `/Users/andrew/maisi/questions/2026-11-20-odesky/delegations/answers/round3/claude-subagent/check.py` (run with the scratchpad venv python, `-I`).

## Findings, by severity

### F1 (substantive, overbroad conclusion): R14, line 154

The claim: "The position along $\Theta$ is set by the law of $(f-g)/(f+g)$."

The argument on line 154 itself gives the limit $c-d\to\mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]$. Write $r=(f-g)/(f+g)$. Then this limit is $\mathbb E[(f+g)^2\,r|r|]/\mathbb E[(f+g)^2]$. That is a mean of $r|r|$ weighted by $(f+g)^2$, so it depends on the joint law of $(r,f+g)$ and not on the law of $r$ alone.

Counterexample. Let $\rho$ be uniform on $\{0,1\}$; all functions below are positive and nondecreasing.
- Case A: $f=(2,3)$, $g=(1,3)$. Then $r=(1/3,0)$ and $c-d\to 1/45\approx0.022$.
- Case B: $f=(1,4)$, $g=(1,2)$. Then $r=(0,1/3)$ and $c-d\to 1/10$.

In both cases $r$ takes the values $0$ and $1/3$ with probability ½ each, but the limits differ by a factor of 4.5. A numerical check with block forms at $n=200$ gives $c-d=0.0222$ and $0.1015$, with $a-b=0$ in both.

Suggested correction: "set by the law of $r$ weighted by $\sigma^2=(f+g)^2$." With the extra condition that $r$ is independent of $f+g$, the original wording holds. One sign condition does not supply that independence.

### F2 (minor overstatement): R13 item 4, line 141

The claim: "Every point of $\Theta$ is attained (e.g. $t_i\equiv t$)."

The setting (line 135) requires $t_i\in(-1,1)$ and $\sigma_i>0$, so $\alpha_i,\beta_i>0$ and $a=2\sum\alpha_i\beta_i/\|L\|^2>0$. The two vertices $(0,0,1,0)$ and $(0,0,0,1)$ of $\Theta$ have $a=0$, so no form in the setting attains them. The example $t_i\equiv t$ reaches only $t\in(-1,1)$. Correct statement: every point of $\Theta$ with $a>0$ (equivalently, $\Theta$ minus its two vertices) is attained. The vertices are attained only by degenerate rank-one forms with $u=\pm v$, which lie outside the setting.

### F3 (minor, a hypothesis stronger than needed; no error): R13(3), line 140, and R14, line 154

R13(3) gives the formula $c-d=\sum_iw_it_i|t_i|$ only "in either case", that is, when all $t_i$ share a sign. In fact, comonotonicity alone gives $\lambda_{+,k}-\lambda_{-,k}=\sigma_{\pi(k)}t_{\pi(k)}$, and then $c-d=\sum_k x_k|x_k|/\|L\|^2$ holds for any signs. I checked this numerically on comonotone forms with mixed signs: the residual was about $10^{-17}$.

So R14's "if moreover $f-g$ has one sign" is not needed for the $c-d$ limit. It is needed only to place the limit on $\Theta$. This makes nothing false, but the stated result is weaker than what the argument proves.

### F4 (minor, mislabelled special case): R14, line 160

"$f/g\equiv$ const: one tilt per head, the correlated Gaussian model of the question."

The model in the question, $K=rQ+\sqrt{1-r^2}G$ with i.i.d. entries, has $f$ and $g$ both constant:
- $Q+K$ and $K-Q$ are uncorrelated, since $(1+r)(r-1)+(1-r^2)=0$;
- their per-entry variances are $2(1+r)$ and $2(1-r)$.

The case $f/g\equiv$ const with nonconstant $f$ is a heteroscedastic generalization of that model, not the model itself. Line 160 already lists "$f,g$ constant: … its correlated version", which is the correct match.

A separate caveat: the question's Gaussian statements concern $n\le N/2$ with $n$ comparable to $N$, where the relations hold only approximately. R14 covers only $n$ fixed with $N\to\infty$. That is fine as stated, but R14 does not explain the finite-ratio behaviour.

I could not check the claim "$g\equiv$ const: Antigravity's signed-spike ensemble (R9)", because R9 is not among the givens.

### F5 (minor, how the convergence step is justified): R14 proof, line 157

"By the strong law of large numbers, the rows … become orthonormal almost surely."

The SLLN gives almost-sure convergence only on one probability space where the size-$N$ matrices are nested, for example as the first $N$ columns of an infinite i.i.d. array. The ensemble draws $P$ and $M$ afresh for each $N$, so the coupling is unspecified.

The conclusion still holds for any coupling. Each Gram entry is a mean of $N$ i.i.d. products of Gaussians, so its deviation probabilities decay exponentially in $N$, and Borel–Cantelli then gives complete convergence. The proof should say this, or fix the nested coupling.

Two smaller points about the same proof:
- "measurable" is redundant, since monotone functions are measurable.
- "$f-g$ has one sign on the support of $\mu$" works because $\rho_i\in\mathrm{supp}\,\mu$ almost surely. "$\mu$-almost everywhere" would be the cleaner hypothesis.

### F6 (wording): R13 setting, line 135

"equivalently $W=\mathrm{diag}(t_i)$ in R1". When $\Sigma$ has repeated values, $W$ is diagonal in some SVD gauge but not in every one. The equivalence should read "in some SVD gauge". This does not affect any conclusion.

## What I checked and found solid

- **R13(1), checked hardest.** The identities:
  - $a\|L\|^2=\|T\|^2=2\sum\alpha_i\beta_i$, since block $i$ contributes two singular values $\sqrt{\alpha_i\beta_i}$;
  - $b\|L\|^2=2\langle\alpha^\downarrow,\beta^\downarrow\rangle$.

  The strict part: swapping a discordant pair changes the sum by $-(\alpha_i-\alpha_j)(\beta_i-\beta_j)>0$, so the identity pairing is not maximal and the inequality is strict.

  The equality part: sort by $\alpha$ and break ties by $\beta$; concordance then forces $\beta$ to be nonincreasing too, so one permutation sorts both lists. Both directions are correct.
- **R13(2).** A product of two nonincreasing positive sequences is nonincreasing, so $\sqrt{\alpha_{\pi(k)}\beta_{\pi(k)}}$ is the sorted list $\sigma(T)$. Correct.
- **R13(3), (4).** Correct as stated, apart from F2 and F3. $\Theta=\{a=b,\ cd=0\}$, and $cd=0$ holds if and only if $c=0$ or $d=0$.
- **Balanced-channel form.** With $|q|=|k|$, the vectors $k+q$ and $k-q$ are orthogonal. Then $kq^\top+qk^\top=\tfrac12[(k+q)(k+q)^\top-(k-q)(k-q)^\top]$, which gives $\alpha=|q+k|^2/4$ and $\beta=|k-q|^2/4$. Correct.
- **R14 limit identification.** With $A=Q+K$ and $B=K-Q$: $S=(A^\top A-B^\top B)/4$, so $\Pi=A/2$ and $\Delta=B/2$, and in the limit $|\pi_i|^2=f(\rho_i)$ and $|\delta_i|^2=g(\rho_i)$. Also $|q_i|^2\to f+g$, $q_i\cdot k_i\to f-g$, and $\sigma_i=\alpha_i+\beta_i$. All correct.

  $\|L\|^2=\mathrm{tr}(KK^\top QQ^\top)$ is a polynomial in the blocks of $M_N$, as claimed.

  Continuity holds at the limit: $M_\infty$ is positive definite and $\alpha_i,\beta_i>0$. Signature $(n,n)$, nonzero $\sigma(T)$ and sorted eigenvalues are therefore all stable.

  Comonotonicity of $(f(\rho_i),g(\rho_i))$ follows from $f$ and $g$ both being nondecreasing, ties included.
- **R14 $c-d$ limit formula.** $w_it_i|t_i|=(f-g)|f-g|/\sum(f+g)^2$. The SLLN applies to the numerator and the denominator separately. Integrability of the numerator follows from $|f-g|^2\le(f+g)^2$. This is an iterated limit: $N\to\infty$ first, then $n\to\infty$. The text implies that order, and it would help to state it.

## Numerical checks (check.py)

- **Random comonotone block forms** (n=5, N=12): $|a-b|\le 3\times10^{-16}$, relation-(1) relative error $\le 7\times10^{-16}$, and the $c-d$ formula holds to $10^{-16}$. With mixed signs, $cd>0$, as R13(4) predicts.
- **R14 ensemble** with $f=e^\rho+1$, $g=0.5+0.3\tanh\rho$ and n=5:

  | N | max relative error of relation (1) |
  |---|---|
  | 100 | 0.10 |
  | 1,000 | 0.015 |
  | 10,000 | 0.0028 |
  | 100,000 | 0.0013 |

  The error shrinks roughly like $N^{-1/2}$. The profile converges to the predicted $\pi_\infty=(0.3148,0.3148,0.3704,0)$. The gap $a-b$ is already about $10^{-5}$ at large N, and it is negative, as R4 requires for nearly diagonal $W$.
- **Counterexample to line 154:** see F1.
