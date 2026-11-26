# Draft answer (not posted; this draft needs Dev's approval before posting)

**Short answer: yes.** There is a natural class of query/key forms for which relations (1) and (2) hold exactly, and a natural Gaussian ensemble whose profiles converge to that class. The theorems below are checked in Lean, and the full project (proofs, scripts, data) is at [github.com/andrewcritch/question-2026-11-20-odesky](https://github.com/andrewcritch/question-2026-11-20-odesky).

Notation and relations (1) and (2) are as in the question: $S$, $T$, $\lambda_+$, $\lambda_-$, $\sigma(T)$, $a,b,c,d$ and $\Theta$, all computed from the form $L=K^\top Q$ of a head. The *profile* of $L$ is $\pi(L):=(a(L),b(L),c(L),d(L))$.

The solution was found by a collaboration between AI models: Claude Opus 5.5, GPT-6 Astra and GPT-6.1 Sol (both via Codex), Gemini 4 Carbon (via Antigravity), and Grok (via Grok Build). Claude Opus 5.5 coordinated the work, found the ordering condition that makes relations (1) and (2) exact, built the ensemble from the other models' ideas, and ran the measurements on trained models; GPT-6 Astra found the exact identity for $a$ and the rearrangement argument that the ordering condition sharpens; a second Claude instance proposed writing the ensemble through $Q+K$ and $K-Q$; Gemini 4 Carbon proposed tying how closely each query row aligns with its key row to how large the pair is, and found the correction at a fixed ratio $N/n$; Grok characterized the structure of trained heads outside the ensemble; and GPT-6.1 Sol and Claude Opus 5.5 subagents wrote the Lean proofs. [`attribution.md`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/attribution.md) gives the details.

## 1. Coordinates

Let $L=K^\top Q$ have rank $n$. Write $L=U\Sigma V^\top$, where $\Sigma=\mathrm{diag}(\sigma_1,\dots,\sigma_n)$ holds the $n$ nonzero singular values $\sigma_1\ge\dots\ge\sigma_n>0$, and $U,V\in\mathbb R^{N\times n}$ have orthonormal columns $u_i$, $v_i$. Let $W:=U^\top V$, the $n\times n$ matrix of cosines $W_{ij}=u_i^\top v_j$ between the left and right singular vectors of $L$.

- For $N\ge2n$, the pair $(\Sigma,W)$ determines $L$ up to the congruence $L\mapsto OLO^\top$ with $O$ orthogonal. The profile and relations (1) and (2) are invariant under this congruence, so $(\Sigma,W)$ determines them.
- Let $t_i:=W_{ii}=u_i^\top v_i$, the *tilt* of the pair $(u_i,v_i)$; let $F:=\sum_i\sigma_i^2$, $m_2:=\sum_i\sigma_i^2t_i^2/F$, and $q:=\sum_{i\ne j}\sigma_i\sigma_jW_{ij}W_{ji}/F$. Then exactly
  $$a=\tfrac12(1-m_2-q),\qquad a-b=c+d-m_2-q.$$
- Let $F\in\mathbb R^{2n\times N}$ be the matrix whose rows are the $n$ rows of $Q$ followed by the $n$ rows of $K$. For every head with $\operatorname{rank}F=2n$, $\sum_i\log\sigma(T)_i=\tfrac12\sum_i\log(\lambda_{+,i}\lambda_{-,i})$, because both sides equal $\tfrac12\log\det G-n\log2$, where $G:=FF^\top$ is the $2n\times2n$ Gram matrix of the rows of $F$. So relation (1) holds exactly for the mean over $i$ of the log-ratios $r_i:=\log\sigma(T)_i-\tfrac12\log(\lambda_{+,i}\lambda_{-,i})$. Only the spread of the $r_i$ over $i$ can show relation (1) failing.

Proofs of these three facts are in the project record, [`record.md`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/record.md), entries R1, R4 and R5.

## 2. Normal form

A *sum of rank-one forms on orthogonal planes* is $L=\sum_i\sigma_iu_iv_i^\top$ with $\sigma_i>0$, unit vectors $u_i,v_i$, and the planes $\mathrm{span}(u_i,v_i)$ mutually orthogonal (so $W$ is diagonal). The summand $\sigma_iu_iv_i^\top$ is *block* $i$; its tilt $t_i=u_i^\top v_i$ (defined in §1) lies in $(-1,1)$. Put $\alpha_i:=\sigma_i(1+t_i)/2$ and $\beta_i:=\sigma_i(1-t_i)/2$. The blocks are *similarly ordered* if $(\alpha_i-\alpha_j)(\beta_i-\beta_j)\ge0$ for all $i,j$. $L$ is in *normal form* if the blocks of $L$ are similarly ordered and the tilts of $L$ are all $\ge0$ or all $\le0$.

> **Lemma 1.** The symmetric part of block $i$ has eigenvalues $\alpha_i>0$ and $-\beta_i<0$, and the antisymmetric part of block $i$ has singular value $\sqrt{\alpha_i\beta_i}$ with multiplicity 2. (Proof: the rank-one computation in the question, applied to each block.)

> **Theorem 1.** Let $L$ be a sum of rank-one forms on orthogonal planes. Then:
> 1. $a\le b$, with equality if and only if the blocks of $L$ are similarly ordered.
> 2. If the blocks are similarly ordered, relation (1) holds with equality at every index $k=1,\dots,n$.
> 3. If the blocks are similarly ordered, then $c-d=\sum_iw_it_i|t_i|$ with $w_i:=\sigma_i^2/F$. Also $d=0$ if and only if every $t_i\ge0$, and $c=0$ if and only if every $t_i\le0$.
> 4. $\pi(L)\in\Theta$, i.e., relation (2) holds, if and only if $L$ is in normal form.
> 5. Every point of $\Theta$ other than the two endpoints of $\Theta$ is $\pi(L')$ for some $L'$ in normal form.

*Proof sketch of Theorem 1.* By Lemma 1, $\lambda_+$ is the list of the $\alpha_i$ sorted decreasingly, and $\lambda_-$ is the list of the $\beta_i$ sorted decreasingly. So $b=2\sum_k\lambda_{+,k}\lambda_{-,k}/F$ pairs the $\alpha_i$ with the $\beta_i$ in sorted order, while $a=2\sum_i\alpha_i\beta_i/F$ pairs them block by block. By the rearrangement inequality, $a\le b$, with equality exactly when one permutation sorts both lists; that permutation also gives items 2 and 3. Equal tilts $t_i=t$ give the rank-one profiles, which gives item 5. Lean checks Lemma 1 in [`Geometry.lean`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/lean/OdeskyLean/Geometry.lean) and [`Spectral.lean`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/lean/OdeskyLean/Spectral.lean), and Theorem 1(1)–(4) in [`Main.lean`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/lean/OdeskyLean/Main.lean).

By Theorem 1(4), the forms that "behave like rank-one forms", in the question's phrase, are exactly the forms in normal form. Even so, a form in normal form can have any rank $n\ge1$.

## 3. Random ensemble

Fix $n$, a law $\mu$ on $\mathbb R$, and functions $f,g:\mathbb R\to(0,\infty)$ that are both nondecreasing. Draw $\rho_1,\dots,\rho_n$ i.i.d. from $\mu$. For each $N\ge2n$, let $P,M\in\mathbb R^{n\times N}$ be the first $N$ columns of two infinite arrays of i.i.d. standard Gaussian entries, independent of each other and of the $\rho_i$. Define $Q$ and $K$ by
$$Q+K=2\,\mathrm{diag}\bigl(\sqrt{f(\rho_1)},\dots,\sqrt{f(\rho_n)}\bigr)P/\sqrt N,\qquad K-Q=2\,\mathrm{diag}\bigl(\sqrt{g(\rho_1)},\dots,\sqrt{g(\rho_n)}\bigr)M/\sqrt N.$$

> **Theorem 2.** Condition on $\rho$. As $N\to\infty$ with $n$ fixed, almost surely $\pi(L)$ converges to $\pi(L_\infty)$, where $L_\infty$ is a sum of rank-one forms on orthogonal planes with $\alpha_i=f(\rho_i)$ and $\beta_i=g(\rho_i)$. The blocks of $L_\infty$ are similarly ordered, because $f$ and $g$ are nondecreasing. Hence $a-b\to0$, and relation (1) holds with equality in the limit. If $f-g$ does not change sign on the support of $\mu$, then $L_\infty$ is in normal form, so relation (2) holds in the limit. If also $\mathbb E[(f+g)(\rho)^2]<\infty$ for $\rho\sim\mu$, then, as $n\to\infty$, almost surely
> $$c(L_\infty)-d(L_\infty)\;\to\;\frac{\mathbb E[(f-g)(\rho)\,|(f-g)(\rho)|]}{\mathbb E[(f+g)(\rho)^2]}.$$
> The right-hand side is the $(f+g)^2$-weighted mean of $t|t|$, where $t=(f-g)/(f+g)$ is the tilt of a block of $L_\infty$.

*Proof sketch of Theorem 2.* Let $x_1,\dots,x_{2n}\in\mathbb R^N$ be the $n$ rows of $P/\sqrt N$ followed by the $n$ rows of $M/\sqrt N$. As $N\to\infty$, the Gram matrix of $x_1,\dots,x_{2n}$ tends to $I$ almost surely, by the strong law of large numbers. So these rows lie within a distance $\delta\to0$ of an orthonormal family. The form whose rows are built from the orthonormal family, in place of $x_1,\dots,x_{2n}$, is exactly a sum of rank-one forms on orthogonal planes with $\alpha_i=f(\rho_i)$ and $\beta_i=g(\rho_i)$. Replacing the orthonormal family by $x_1,\dots,x_{2n}$ changes $S$ and $T^\top T$ by $O(\delta)$ in operator norm. By Weyl's inequality, every sorted eigenvalue of $S$ and of $T^\top T$ then changes by $O(\delta)$, uniformly in $N$. The Frobenius norms of $L$ and $T$ are polynomials in the Gram matrix, so they converge too. The $n\to\infty$ limit of $c-d$ follows from the strong law of large numbers applied to the formula of Theorem 1(3). Hence Theorem 2 holds. Lean checks the convergence statement as `theoremB_ae` in [`TheoremBFull.lean`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/lean/OdeskyLean/TheoremBFull.lean), and the limit of $c-d$ as `ratio_slln` in [`Probability.lean`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/lean/OdeskyLean/Probability.lean).

In words: in the ensemble, each head is a sum of $n$ independent blocks. Row $i$ of $Q+K$ has squared norm close to $4f(\rho_i)$ (a "match" strength), row $i$ of $K-Q$ has squared norm close to $4g(\rho_i)$ (a "mismatch" strength), and $f$ and $g$ are both nondecreasing in a shared latent parameter $\rho_i$. Special cases of the ensemble:
- $f=g$ constant: $Q$ and $K$ are independent Gaussian matrices. This case is the *Gaussian baseline*. By Theorem 2, its limit profile is the midpoint $(\tfrac12,\tfrac12,0,0)$ of $\Theta$.
- $f,g$ constant, $f\ne g$: up to scale, the question's correlated Gaussian ensemble $K=rQ+\sqrt{1-r^2}\,G$, with $f/g=(1+r)/(1-r)$.
- $g$ constant: a "signed spike" ensemble, in which $K$ is a correlated copy of $Q$ plus shared features with Gaussian loadings.

By the formula in Theorem 2, the position of $\pi(L_\infty)$ along $\Theta$ is determined by the joint law of $(t,f+g)$, but not by the law of $t$ alone.

## 4. Comparison with trained heads

All measurements use raw $L=K^\top Q$ (the LayerNorm gains are not multiplied into $Q$ and $K$; for RoPE, $L$ at relative position 0), in GPT-2 small (144 heads), GPT-2 medium (384 heads) and Pythia-160m (RoPE, 144 heads). Each value is the median over heads. The relation-(1) relative error is $\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|/\|\sigma(T)\|$, with entrywise products and square roots. The Gaussian baseline replaces $Q$ and $K$ by independent Gaussian matrices of the same shape. The scripts are in [`delegations/round1_brief/`](https://github.com/andrewcritch/question-2026-11-20-odesky/tree/main/delegations/round1_brief): [`gpt2_W.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/gpt2_W.py) and [`comono.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/comono.py) for GPT-2 small, [`medium.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/medium.py) for GPT-2 medium and large, [`pythia.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/pythia.py), and [`bloom.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/bloom.py); the results are entries R3, R13, R15, R16, R18 and R19 of [`record.md`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/record.md).

| quantity | GPT-2 small | GPT-2 medium | Pythia-160m | Gaussian baseline |
|---|---|---|---|---|
| Kendall $\tau(\alpha,\beta)$ from $\sigma_i$ and $t_i$ (1 = similarly ordered) | 0.76 | 0.77 | 0.85 | — |
| diagonal share of $\|W\|_F^2$ | 0.18 | 0.21 | 0.13 | 0.016 |
| off-diagonal RMS of $W$ / $N^{-1/2}$ | 1.34 | 1.35 | 1.30 | 1.00 |
| relation-(1) relative error | 0.059 | 0.051 | 0.044 | 0.011 |
| fraction of heads with $a>b$ | 0.31 | 0.22 | 0.31 | — |
| $\mathrm{corr}(q,\,a-b)$ across heads | −0.97 | −0.97 | −0.96 | — |

Reading:
- **Training raises the diagonal share of $\|W\|_F^2$.** In GPT-2 small, the diagonal share is 0.18, about 11 times its Gaussian-baseline value 0.016.
- **The off-diagonal entries of $W$ are mostly at the size that random vectors give.** Their RMS matches the off-diagonal RMS of $W$ for random frames in dimension about $0.55N$, in GPT-2 small and in GPT-2 medium.
- **Trained heads depart from the normal form in two separate ways.** *Departure 1* is imperfect similar ordering of $\alpha$ and $\beta$ (Kendall $\tau\approx0.77$). Departure 1 pushes $a$ below $b$ and accounts for most of the relation-(1) error. *Departure 2* is the reciprocal off-diagonal overlap $q$ (defined in §1), which decides the sign of $a-b$. By Theorem 1(1), every sum of rank-one forms on orthogonal planes has $a\le b$, so the roughly 30% of trained heads with $a>b$ are not sums of rank-one forms on orthogonal planes. Across heads, $a-b$ tracks $-q$ (correlation $-0.97$). The heads with the largest $a-b$ are layer-0 heads with $q\approx-0.2$, from an antisymmetric coupling among the top singular directions of $W$.
- **Relation (1) has a larger error in trained heads than under the Gaussian baseline.** The Gaussian baseline has its limit profile at the midpoint of $\Theta$, where relation (1) has a small error. Training moves the profiles of heads away from the midpoint, along $\Theta$, and adds departures 1 and 2.

## 5. Summary

Relations (1) and (2) hold exactly for the forms in normal form (Theorem 1). For the Gaussian ensemble of §3, the profile of $L$ converges to the profile of a form in normal form as the embedding dimension $N$ grows (Theorem 2), and the question's correlated Gaussian ensemble is a special case of that ensemble. Trained attention heads are close to the normal form, and §4 measured their departures from it.

## 6. Caveats

- Lean 4 with Mathlib (hereafter, Lean) checks three groups of results in [`lean/`](https://github.com/andrewcritch/question-2026-11-20-odesky/tree/main/lean), with no unproved steps. The first group is Lemma 1, Theorem 1(1), (2) and (4), and the formula for $c-d$ in Theorem 1(3); in these checks, Lean computes the profile of $L$ from the characteristic polynomials of $S$ and $T^\top T$ and from Frobenius norms. The second group is the convergence statement of Theorem 2, for any fixed values $f(\rho_i),g(\rho_i)>0$, assuming that the entries of $P$ and $M$ are i.i.d. standard Gaussian. The third group is the almost-sure convergence, as $n\to\infty$, of the ratio $R_n:=\sum_{i\le n}[(f-g)|f-g|](\rho_i)/\sum_{i\le n}[(f+g)^2](\rho_i)$ to the right-hand side of the formula in Theorem 2. Lean checks the clause of Theorem 1(3) on $d=0$ and $c=0$ as a statement about the lists $\alpha$ and $\beta$, not as a statement about $L$. Lean does not check the identities of §1, Theorem 1(5), the equality $c(L_\infty)-d(L_\infty)=R_n$, the special cases of §3, or anything in §4.
- The table in §4 covers GPT-2 small, GPT-2 medium and Pythia-160m (RoPE) only. BLOOM-560m (ALiBi, 384 heads) and GPT-2 large (720 heads) give values close to those of the table, as medians over heads: diagonal share of $\|W\|_F^2$: 0.18 and 0.24; Kendall $\tau$: 0.76 and 0.78; relation-(1) relative error: 0.044 and 0.050; fraction of heads with $a>b$: 0.19 and 0.21; $\mathrm{corr}(q,a-b)$: $-0.97$ and $-0.98$.
- Whether the LayerNorm gains are multiplied into $L$ matters for how close heads are to $\Theta$: with the gains and centering multiplied in, 20% of GPT-2-small heads have $|a-b|>0.1$, against 7.6% for raw $L$ ([`gpt2_more.py`](https://github.com/andrewcritch/question-2026-11-20-odesky/blob/main/delegations/round1_brief/gpt2_more.py)).
- Some finite-$N$ ensembles reproduce departures 1 and 2 of §4. One example, in [`delegations/answers/round2/`](https://github.com/andrewcritch/question-2026-11-20-odesky/tree/main/delegations/answers/round2), uses eight parameters per head, and its median relation-(1) relative error over heads equals the measured median. But these ensembles are descriptive fits, not natural ensembles, and none of them reproduces the layer-0 heads with the largest $a-b$.
- Theorem 2 states convergence as $N\to\infty$ with $n$ fixed. At a fixed ratio $N=\kappa n$, as $n\to\infty$, the limit differs from the iterated limit by $O(1/\kappa)$. For example, with constant $f,g$, $1-2a\to(1+1/\kappa)(f-g)^2/\bigl((f+g)^2+(f-g)^2/\kappa\bigr)$, against $(f-g)^2/(f+g)^2$ for the iterated limit; the relative difference is at most $1/\kappa$. The measured models have $\kappa=12$–$20$, so the relative difference is at most 5–8%.
