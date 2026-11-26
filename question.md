Copied from MaisiOverflow. Each section starts with a line of = signs around its name; a longer line starts a larger section. Facts about a section follow its name, up to a plain line of = signs; then comes the section's text, in Markdown, as its author wrote it. Avoid using lines of = signs to delimit your own content when posting; use normal Markdown headers instead.

======================== QUESTION PAGE ========================
Title: Is there a normal form / random matrix model for trained transformers?
Source: https://maisioverflow.net/questions/cmwpdb4m2000v01s61il48sj5/is-there-a-normal-form-random-matrix-model-for-trained-transformers
Tags: interpretability, probability
Answers: 0
========================

================ QUESTION ================
Asked by: Andrew O'Desky
Date: 2026-11-20
Scores (sums over its parts): Overall Quality 40, Safety Benefit 0, Precision & Clarity 2, Correctness 0
================

======== BACKGROUND FACTS ========
Scores: Overall Quality 10, Safety Benefit 0, Precision & Clarity 0, Correctness 0
========
This question is about the structure of attention heads in trained transformers.  

*TL;DR: Why do trained bilinear forms behave similarly to rank-one forms?*

An attention head computes interactions between tokens $x,y$ using its bilinear form $x^T K^T Q y$, where $Q$ and $K$ are $n \times N$ matrices and $n \leq N/2$. Write $L = K^TQ = S + T$ for symmetric $S$ and antisymmetric $T$.

The following facts hold away from a subset of $Q,K$ of measure zero:

- $S$ has signature $(n,n,N-2n)$,
- $T$ has rank $2n$, with $n$ nonzero singular values each of multiplicity two,

So every head has three lists of $n$ positive numbers, each sorted in decreasing order: the positive eigenvalues $\lambda_+$ of $S$, the absolute values $\lambda_-$ of its negative eigenvalues, and the singular values $\sigma(T)$ of $T$ counted once.

In 21,080 trained heads from 18 open-source language models trained on natural language, two additional relations approximately hold for their spectral data. The first is that the antisymmetric spectrum is approximately determined by the symmetric spectrum. 

*(1) The singular values of $T$ are geometric means of the eigenvalues of $S$:*
$$\sigma(T)_i\approx\sqrt{(\lambda_+)_i(\lambda_-)_i},\qquad i=1,\dots,n.$$

For a real vector $x$ write $(x)_+=\max(x,0)$ and $(x)_-=\max(-x,0)$ entrywise. The squared Frobenius norm of $L$ splits into four nonnegative terms:
$$\begin{aligned}
\|L\|^2&=\|T\|^2+\|S\|^2\\
&=\|T\|^2+\|\lambda_+\|^2+\|\lambda_-\|^2\\
&=\|T\|^2+2\langle\lambda_+,\lambda_-\rangle+\|\lambda_+-\lambda_-\|^2\\
&=\|T\|^2+2\langle\lambda_+,\lambda_-\rangle+\|(\lambda_+-\lambda_-)_+\|^2+\|(\lambda_+-\lambda_-)_-\|^2.
\end{aligned}$$
Dividing by $\|L\|^2$ gives four nonnegative numbers summing to one:
$$a=\frac{\|T\|^2}{\|L\|^2},\quad b=\frac{2\langle\lambda_+,\lambda_-\rangle}{\|L\|^2},\quad c=\frac{\|(\lambda_+-\lambda_-)_+\|^2}{\|L\|^2},\quad d=\frac{\|(\lambda_+-\lambda_-)_-\|^2}{\|L\|^2}.$$
So to each nonzero bilinear form we get a point $(a,b,c,d)$ in the tetrahedron $\Delta$. Let $\Theta=\{a=b,\ cd=0\} \subset \Delta$. 
The second observation is that trained heads accumulate along $\Theta$. 

*(2) Trained heads lie close to $\Theta$ and spread along it.*

======== QUESTION STATEMENT ========
Scores: Overall Quality 30, Safety Benefit 0, Precision & Clarity 2
========
**Question.** Is there a natural class of pairs $(Q,K)$ given by either a normal form or a random matrix ensemble for which (1) and (2) hold?

======== FURTHER REMARKS ========
Scores: Overall Quality 0, Safety Benefit 0, Precision & Clarity 0, Correctness 0
========
*Random models.* If $Q,K$ have independent Gaussian entries, both relations hold approximately, but with $\lambda_+\approx\lambda_-$, so all profiles sit at the single point $(\tfrac12,\tfrac12,0,0)$ of $\Theta$. If $K=rQ+\sqrt{1-r^2}\,G$ with $Q,G$ independent Gaussian, the profile moves along $\Theta$ to $c-d\approx r|r|$. So the observed spread along $\Theta$ seems likely to be due to a correlation between $Q$ and $K$ that remains to be described.

*Rank one matrices.* Rank one matrices satisfy the first observation exactly. Let $L=uv^T$ with $u,v$ unit and $t=u^Tv$. Then $S=\tfrac12(uv^T+vu^T)$ has eigenvectors $u+v$ and $u-v$ with eigenvalues $\tfrac{1+t}2$ and $-\tfrac{1-t}2$, so $\lambda_+=\tfrac{1+t}2$ and $\lambda_-=\tfrac{1-t}2$. The antisymmetric part $T=\tfrac12(uv^T-vu^T)$ has two equal singular values $\sigma$ with $2\sigma^2=\|T\|^2=\tfrac{1-t^2}2$, so $$\sigma(T)=\tfrac12\sqrt{1-t^2}=\sqrt{\lambda_+\lambda_-}.$$ Consequently $L$ has $(a,b,c,d)=\bigl(\tfrac{1-t^2}2,\tfrac{1-t^2}2,(t)_+^2,(t)_-^2\bigr)$, so $$\Theta = \{(a_L,b_L,c_L,d_L) : \mathrm{rk}\,L = 1\}.$$ 
So in some sense, bilinear forms in trained attention heads are behaving like rank-one forms even though their effective rank is far from one. 

Details and data: [arXiv:2609.22990](https://arxiv.org/pdf/2609.22990)

![abcd_simplex_all](/uploads/229fb05125d6eedec9ef270efea10735.png)
