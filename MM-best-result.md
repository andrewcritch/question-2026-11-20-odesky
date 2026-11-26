<!--
Let FILE_SIZE_LIMIT = $0 if a valid file size, else 10kb.

MAINTENANCE INSTRUCTIONS — keep this file in the form of a short mathematical note, with size at most FILE_SIZE_LIMIT: a setting of numbered
definitions, then the theorem statements, then a proof sketch, then the limits.

Update Step 1: Determine if a stronger result supercedes the result in this file.  If not, skip to Report Step 1.

Update Step 2: Move a timestamped copy of this file into `MM-best-result-archive/` rather than simply deleting it, and add a header saying what replaced it and on what grounds.

Update Step 3: Replace the content with the stronger result.  
a) Keep the note self-contained, for a reader who knows mathematics and machine learning and who has never seen this repository is the audience. Define every quantity used. 
b) Name no file, no internal numbering, no section, and no term of art private to this project. 
c) Use no jargon that would be unfamiliar to ambiguous.
d) Use terms consistently. If the not introduced a term, use that term and only that term for its referent. Avoid using synonyms for technical terms, favoring repetition of the same word for the same idea every time.
e) Make the punch line of each theorem easy to tell. The conclusion of the theorem should be at the end, not buried in the middle with caveats and definitions on either side.
f) For the proof sketch, see also Skill(mm:8--proof-sketch) for proof sketch guidelines.
g) Use `$...$` for inline math and `$$...$$` for display math so the note renders in VS Code's built-in Markdown preview. Put each display delimiter on its own line, with a blank line before and after the display block. Keep inline delimiters adjacent to the math, with no space immediately inside them. Do not use `\(...\)` or `\[...\]` as math delimiters. Keep math outside code spans and code fences.

Update Step 4: Review the content produced in Step 3, for the criteria listed in Step 3.  Make changes to improve adherence to the Step 3 instructions.

Update Step 5: Check the file size and ensure it's at most the FILE_SIZE_LIMIT.  If more, look for ways to make it more concise or cut down on the content, without making it less legible.  Repeat from Update Step 4 onward.

Report Step 1: Write a message to the user that says 

"""
The best result file has been updated.  Here is its content, excluding the maintenance instructions:

(reproduce the content)
"""

Report Step 2: Write "(end of best result report)" at the end of your message to the user. Do not write any suggestions for next steps beyond what was already included in this file.  Wait for the next instruction from the user or automated reminder(s) to continue working.  If you find yourself compelled to add additional remarks, declare the summary deprecated and go back to Update Step 3, and revise the content so that you don't feel a need to add trailing comments after reporting it.

Thanks!
-->

# A normal form and a random ensemble for attention profiles

## Setting

**Definition 1 (form).** Let $n,N$ be integers, $1\le n\le N/2$. A *head* is a pair $Q,K\in\mathbb R^{n\times N}$; its *form* is $L:=K^\top Q$, with $S:=(L+L^\top)/2$ and $T:=(L-L^\top)/2$.

**Definition 2 (spectral lists).** If $S$ has $n$ positive and $n$ negative eigenvalues, $\lambda_+\in\mathbb R^n$ lists the positive eigenvalues of $S$, $\lambda_-\in\mathbb R^n$ the absolute values of its negative eigenvalues, and $\sigma(T)\in\mathbb R^n$ the nonzero singular values of $T$, each pair counted once; each list is sorted decreasingly. *Relation (1)* is $\sigma(T)_k=\sqrt{\lambda_{+,k}\lambda_{-,k}}$ for $k=1,\dots,n$.

**Definition 3 (profile).** The *profile* of $L\neq0$ is $\pi(L):=(a,b,c,d)$, i.e.,

$$
a:=\frac{\|T\|^2}{\|L\|^2},\quad b:=\frac{2\langle\lambda_+,\lambda_-\rangle}{\|L\|^2},\quad c:=\frac{\|(\lambda_+-\lambda_-)_+\|^2}{\|L\|^2},\quad d:=\frac{\|(\lambda_+-\lambda_-)_-\|^2}{\|L\|^2},
$$

with $(x)_\pm:=\max(\pm x,0)$ entrywise; $a+b+c+d=1$. Let $\Theta:=\{a=b,\ cd=0\}$. *Relation (2)* is $\pi(L)\in\Theta$. A rank-one form $uv^\top$ with unit $u,v$ and $t:=u^\top v$ has $S$-eigenvalues $\tfrac{1+t}2,-\tfrac{1-t}2$, profile $\bigl(\tfrac{1-t^2}2,\tfrac{1-t^2}2,(t)_+^2,(t)_-^2\bigr)\in\Theta$, and satisfies relation (1).

**Definition 4 (sum of rank-one forms on orthogonal planes).** This is $L=\sum_{i=1}^n\sigma_iu_iv_i^\top$ with $\sigma_i>0$, unit $u_i,v_i\in\mathbb R^N$, *tilts* $t_i:=u_i^\top v_i\in(-1,1)$, and mutually orthogonal planes $\mathrm{span}(u_i,v_i)$. Let $\alpha_i:=\sigma_i(1+t_i)/2$, $\beta_i:=\sigma_i(1-t_i)/2$, and $w_i:=\sigma_i^2/\sum_j\sigma_j^2$.

**Definition 5 (similarly ordered).** $\alpha,\beta\in\mathbb R^n$ are *similarly ordered* if $(\alpha_i-\alpha_j)(\beta_i-\beta_j)\ge0$ for all $i,j$, i.e., one permutation sorts both lists decreasingly. For example, $\alpha=(3,1)$, $\beta=(1,3)$ is not similarly ordered: then $\sigma(T)=(\sqrt3,\sqrt3)$, while $\sqrt{\lambda_+\lambda_-}=(3,1)$.

**Definition 6 (ensemble).** Fix $n$, a probability law $\mu$ on $\mathbb R$, and $f,g:\mathbb R\to(0,\infty)$, both measurable and nondecreasing. Draw $\rho_1,\dots,\rho_n$ i.i.d. from $\mu$ and, independently, $P,M\in\mathbb R^{n\times N}$ with i.i.d. standard Gaussian entries. To put all $N$ on one probability space, take $P,M$ to be the first $N$ columns of two fixed infinite Gaussian arrays, so that raising $N$ adds columns. With $D_f:=\mathrm{diag}(\sqrt{f(\rho_i)})$ and $D_g:=\mathrm{diag}(\sqrt{g(\rho_i)})$, let

$$
Q:=(D_fP-D_gM)/\sqrt N,\qquad K:=(D_fP+D_gM)/\sqrt N,\qquad L_N:=K^\top Q .
$$

So $Q+K$ and $K-Q$ have row strengths $f(\rho_i)$ and $g(\rho_i)$, both increasing in $\rho_i$.

## Theorems

**Theorem A (normal form).** Let $L$ be a sum of rank-one forms on orthogonal planes. Then $a\le b$, with equality if and only if $(\alpha,\beta)$ is similarly ordered; in that case relation (1) holds exactly and $c-d=\sum_iw_it_i|t_i|$. Consequently, $\pi(L)\in\Theta$ if and only if $(\alpha,\beta)$ is similarly ordered and the tilts are all $\ge0$ or all $\le0$.

**Remark.** Equal tilts $t_i=t\in(-1,1)$ give the rank-one profiles, so every point of $\Theta$ except $(0,0,1,0)$ and $(0,0,0,1)$ is the profile of a sum of rank-one forms on orthogonal planes.

**Theorem B (ensemble).** Condition on $\rho$, so that $f_i:=f(\rho_i)>0$ and $g_i:=g(\rho_i)>0$ are fixed, and let $L_\infty$ be a sum of rank-one forms on orthogonal planes with $\alpha_i=f_i$, $\beta_i=g_i$. For the profile of $L_N$, use at every $N$ the decreasingly sorted eigenvalues $e_1\ge\dots\ge e_N$ of $S$ and $e'_1\ge\dots\ge e'_N$ of $T^\top T$, i.e., $\lambda_{+,k}:=\max(e_k,0)$, $\lambda_{-,k}:=\max(-e_{N+1-k},0)$, $\sigma(T)_k:=\sqrt{\max(e'_{2k-1},0)}$ (as in Definition 2 when $S$ has $n$ eigenvalues of each sign). As $N\to\infty$ with $n$ fixed, almost surely $\pi(L_N)\to\pi(L_\infty)$, and, if $(f_i)$ and $(g_i)$ are similarly ordered, $\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|/\|\sigma(T)\|\to0$. They are, since $f,g$ are nondecreasing. Consequently, relation (1) holds in the limit, and, if $f-g$ has one sign on the support of $\mu$, $\pi(L_\infty)\in\Theta$: the ensemble satisfies relations (1) and (2).

**Theorem C (position on $\Theta$).** If moreover $\mathbb E[(f+g)^2(\rho_1)]<\infty$, then, almost surely, as $n\to\infty$, $c(L_\infty)-d(L_\infty)\to\mathbb E[(f-g)|f-g|]/\mathbb E[(f+g)^2]$.

**Special cases.** Constant $f=g$: independent Gaussian $Q,K$, limit profile $(\tfrac12,\tfrac12,0,0)$. Constant $f=1+r$, $g=1-r$: up to scale, $K=rQ+\sqrt{1-r^2}\,G$ with $Q,G$ independent Gaussian, limit $c-d=r|r|$.

## Proof sketch

1. *Block spectra.* $S,T$ preserve each plane $\mathrm{span}(u_i,v_i)$ and vanish off their sum. On plane $i$, by Definition 3, $S$ has eigenvalues $\alpha_i,-\beta_i$ and $T$ has singular value $\sqrt{\alpha_i\beta_i}$, twice. So $\lambda_+=\alpha^\downarrow$, $\lambda_-=\beta^\downarrow$, $a\|L\|^2=2\sum_i\alpha_i\beta_i$, and $b\|L\|^2=2\langle\alpha^\downarrow,\beta^\downarrow\rangle$.
2. *$a\le b$.* By rearrangement, $\langle\alpha^\downarrow,\beta^\downarrow\rangle\ge\sum\alpha_i\beta_i$. If $(\alpha_i-\alpha_j)(\beta_i-\beta_j)<0$, exchanging $\beta_i,\beta_j$ raises $\sum\alpha_k\beta_k$, so the inequality is strict. If $(\alpha,\beta)$ is similarly ordered, one permutation $s$ sorts both, and equality holds.
3. *Relation (1) and $c-d$.* Then $\lambda_{\pm,k}=\alpha_{s(k)},\beta_{s(k)}$, and $\sqrt{\alpha_{s(k)}\beta_{s(k)}}$ is nonincreasing in $k$, so it equals $\sigma(T)_k$. Also $\lambda_{+,k}-\lambda_{-,k}=\sigma_{s(k)}t_{s(k)}$, so $c-d=\sum w_it_i|t_i|$, and $d=0$ (resp. $c=0$) iff all $t_i\ge0$ (resp. $\le0$). This proves Theorem A.
4. *Nearby orthonormal family.* Let $x_1,\dots,x_{2n}\in\mathbb R^N$ be the rows of $P/\sqrt N$, then of $M/\sqrt N$. By the strong law, their Gram matrix $G_N$ tends to $I$ almost surely. If $|c^\top(G_N-I)c|\le\delta|c|^2$ for all $c$, with $\delta<1$, then the family $e:=G_N^{-1/2}x$ is orthonormal and $\|\sum_ac_a(x_a-e_a)\|\le\delta|c|$, since every eigenvalue $\gamma$ of $G_N$ has $|\sqrt\gamma-1|\le|\gamma-1|$.
5. *Perturbation.* The rows $\tilde q_i:=\sqrt{f_i}\,e_i-\sqrt{g_i}\,e_{n+i}$ and $\tilde k_i:=\sqrt{f_i}\,e_i+\sqrt{g_i}\,e_{n+i}$ are orthogonal across $i$, with $|\tilde q_i|^2=|\tilde k_i|^2=f_i+g_i$ and $\langle\tilde q_i,\tilde k_i\rangle=f_i-g_i$, so $\tilde L_N:=\tilde K^\top\tilde Q$ is a sum of rank-one forms on orthogonal planes with $\alpha=f$, $\beta=g$, and $\pi(\tilde L_N)=\pi(L_\infty)$ by Theorem A. Replacing $e$ by $x$ moves $L$, $L^\top$ by at most $\delta(2+\delta)\sum_i|\tilde q_i||\tilde k_i|$ in operator norm, so $S$, $T^\top T$ move by order $\delta$ as quadratic forms. By Weyl's inequality, $|e_k(A)-e_k(B)|\le\sup_{|y|=1}|y^\top(A-B)y|$ for symmetric $A,B$, so every sorted eigenvalue moves by order $\delta$, uniformly in $N$. The Frobenius norms are polynomials in the Gram matrix. So $\pi(L_N)\to\pi(L_\infty)$ and the relation-(1) error tends to that of $\tilde L_N$, which is $0$ when $(f,g)$ is similarly ordered. This proves Theorem B.
6. *Position on $\Theta$.* By step 3 with $\sigma_i=\alpha_i+\beta_i$, $\sigma_it_i=\alpha_i-\beta_i$: $c(L_\infty)-d(L_\infty)=\sum_i[(f-g)|f-g|](\rho_i)/\sum_i[(f+g)^2](\rho_i)$. Divide both sums by $n$ and apply the strong law. This proves Theorem C.

## Limits

- **Machine-checked.** Lean 4 with Mathlib checks, with no unproved steps: Theorem A, with the profile from the spectra of $S$, $T^\top T$ and Frobenius norms; Theorem B's limit for any fixed $f_i,g_i>0$ and i.i.d. Gaussian entries of $P,M$; and the strong law for a ratio of sample sums used in Theorem C. Not machine-checked: proof step 6's identification of $c(L_\infty)-d(L_\infty)$ with that ratio, the last sentence of Theorem B, the Remark, and the special cases.
- **Order of limits.** Theorem B takes $N\to\infty$ first. At $N=\kappa n$, $n\to\infty$, the limit moves by order $1/\kappa$: for constant $f=A$, $g=B$, $1-2a\to(1+1/\kappa)(A-B)^2/\bigl((A+B)^2+(A-B)^2/\kappa\bigr)$ rather than $(A-B)^2/(A+B)^2$. Measured models have $\kappa=12$–$20$.
- **Trained heads are near the normal form.** Raw $L=K^\top Q$ (LayerNorm gains not multiplied in) in GPT-2 small (144 heads), GPT-2 medium (384) and Pythia-160m (144). Write $L=U\,\mathrm{diag}(\sigma)V^\top$ with $\sigma\in\mathbb R^n$ the nonzero singular values and $U^\top U=V^\top V=I_n$; with $W:=U^\top V$, $L$ is a sum of rank-one forms on orthogonal planes iff $W$ is diagonal (for some $U,V$), with $t_i=W_{ii}$. Medians:
  - share of $\|W\|^2$ on the diagonal: 0.18, 0.21, 0.13 (independent Gaussian: 0.016);
  - Kendall $\tau$ of $\alpha,\beta$ (1: similarly ordered): 0.76, 0.77, 0.85;
  - relation-(1) error $\|\sigma(T)-\sqrt{\lambda_+\lambda_-}\|/\|\sigma(T)\|$: 0.059, 0.051, 0.044 (independent Gaussian: 0.011);
  - fraction of heads with $a>b$, which Theorem A excludes: 0.31, 0.22, 0.31. Across heads, $a-b$ has correlation $-0.97$, $-0.97$, $-0.96$ with $q:=\sum_{i\neq j}\sigma_i\sigma_jW_{ij}W_{ji}/\sum\sigma_i^2$.
- **Other models.** BLOOM-560m (ALiBi, 384 heads): 0.18, 0.76, 0.044, 0.19, $-0.97$. GPT-2 large (720 heads): 0.24, 0.78, 0.050, 0.21, $-0.98$. With LayerNorm gains multiplied into $L$, about 20% of GPT-2 small heads have $|a-b|>0.1$.
