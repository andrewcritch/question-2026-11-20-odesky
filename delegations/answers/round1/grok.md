# A two-parameter ensemble for GPT-2 attention heads

The ensemble that matches the GPT-2 table is a **singular-mode alignment model**. Each head is an orthogonal sum of \(n\) rank-one forms whose parities differ, plus the incoherent overlap that two \(n\)-frames in a high-dimensional residual stream always have. Two numbers per head set the parities. One global scale sets the overlap. The singular-value shape of \(L\) is a separate, optional, global curve.

Scripts that produced the numbers below are `diagnose.py`, `diagnose2.py`, `diagnose3.py`, `diagnose4.py`, `diagnose6.py`, `fit_ensemble.py`, and `symmetrize_check.py`. Every fit uses the 144 GPT-2 small heads, raw \(L=K^\top Q\), \(n=64\), \(N=768\).

## Notation

Write the thin SVD \(L=U\Sigma V^\top\) with singular values \(\sigma_1\ge\cdots\ge\sigma_n>0\), and write \(W=U^\top V\). The diagonal entries \(t_i=W_{ii}\) are invariants: a sign flip of singular vector \(i\) multiplies row \(i\) and column \(i\) of \(W\) by the same sign, so \(t_i\) is unchanged. Weights \(w_i=\sigma_i^2/\sum_j\sigma_j^2\). The weighted mean and standard deviation are \(\bar t=\sum w_i t_i\) and \(s=\bigl(\sum w_i(t_i-\bar t)^2\bigr)^{1/2}\). Diagonal share is \(\sum_i t_i^2/\|W\|_F^2\). Off-diagonal RMS is the root mean square of the off-diagonal entries of \(W\).

For \(N\ge 2n\), the pair \((\Sigma,W)\) determines \(L\) up to orthogonal congruence, and the profile is invariant under that congruence. Sampling \((\Sigma,W)\) is therefore a complete sampling recipe for the statistics in the brief.

## Candidate 1, recommended: singular-mode alignment

### Sampling recipe

Global constant, fit once: overlap scale \(\sigma_E=0.0483\) (the median off-diagonal RMS of the 144 heads). Per head, two parameters \((\mu,s_\star)\).

1. Draw \(g_i\) i.i.d. standard normal and set \(t_i=\mathrm{clip}(\mu+s_\star g_i,-1,1)\).
2. Draw \(Z\in\mathbb R^{n\times n}\) with i.i.d. \(N(0,\sigma_E^2)\) entries and set the diagonal of \(Z\) to zero.
3. Set \(W_0=\mathrm{diag}(t)+Z\). If \(\|W_0\|_{\mathrm{op}}>1\), replace the singular values of \(W_0\) by their minimum with \(1\). Call the result \(W\).
4. Singular values: either take the head's own \(\Sigma\), or draw a global shape. The profile statistics below use the head's own \(\Sigma\). A global shape is discussed at the end and is not required for \((a,b,c,d)\).
5. Realize frames. Let \(R\) be the positive square root of \(I-W^\top W\). In \(\mathbb R^{2n}\subset\mathbb R^N\),
   \[
   U_0=\begin{pmatrix}I_n\\0\end{pmatrix},\qquad
   V_0=\begin{pmatrix}W\\R\end{pmatrix},\qquad
   L=U_0\,\Sigma\,V_0^\top.
   \]
   Factor as \(Q=\Sigma^{1/2}V_0^\top\) and \(K=\Sigma^{1/2}U_0^\top\). Then \(K^\top Q=L\) and the overlap of this SVD is \(W\). Padding by zero from \(\mathbb R^{2n}\) to \(\mathbb R^N\), or conjugating by a fixed orthogonal matrix of \(\mathbb R^N\), does not change the profile. A common invertible remix \((Q,K)\mapsto(RQ,R^{-\top}K)\) does not change \(L\) at all.

Parameter count: two per head \((\mu,s_\star)\), plus one global \(\sigma_E\). Replacing \(\sigma_E\) by the architectural value \(N^{-1/2}\approx 0.0361\) removes the global fit and undershoots the off-diagonal RMS by about 25 percent. The value \(0.0483\) is the one that matches GPT-2 small.

On a head, \((\mu,s_\star)\) are the unweighted mean and standard deviation of that head's \(t_i\). The weighted \((\bar t,s)\) come out close because \(t_i\) is nearly uncorrelated with \(\sigma_i\) (median correlation of \(|t_i|\) with \(\sigma_i\) is \(-0.11\); median correlation of \(t_i\) with \(\sigma_i\) is \(+0.11\)).

### Why this is the orthogonal sum of rank-one forms

A single rank-one form \(L=\sigma uv^\top\) with unit vectors and \(t=u^\top v\) has
\[
\lambda_+=\sigma\frac{1+t}{2},\qquad
\lambda_-=\sigma\frac{1-t}{2},\qquad
\sigma(T)=\sigma\frac{\sqrt{1-t^2}}{2}=\sqrt{\lambda_+\lambda_-},
\]
and profile
\[
\bigl(a,b,c,d\bigr)=\Bigl(\tfrac{1-t^2}{2},\tfrac{1-t^2}{2},(t)_+^2,(t)_-^2\Bigr).
\]
So \(a=b\), \(cd=0\), and \(c-d=t|t|\). This is the set \(\Theta\).

If \(W=\mathrm{diag}(t_i)\) exactly, then \(L\) is an orthogonal sum of \(n\) such forms, in orthogonal planes, with singular values \(\sigma_i\). Before sorting,
\[
\lambda_{\pm,i}=\sigma_i\frac{1\pm t_i}{2},\qquad
\sigma_i(T)=\sigma_i\frac{\sqrt{1-t_i^2}}{2},
\]
so relation (1) holds mode by mode. Also
\[
a=\frac{1-\sum_i w_i t_i^2}{2}.
\]
The number \(b\) pairs the sorted lists \(\lambda_+\) and \(\lambda_-\), not the modes. The rearrangement inequality gives \(\langle\lambda_+^{\mathrm{sorted}},\lambda_-^{\mathrm{sorted}}\rangle\ge\sum_i\lambda_{+,i}\lambda_{-,i}\), so \(b\ge a\), with equality when every \(t_i\) is equal. A spread in \(t_i\) moves \(a-b\) down from \(0\) and is the sorting error in relation (1). The signed imbalance adds:
\[
c-d\;\approx\;\sum_i w_i\,t_i|t_i|,
\]
with equality for the mode pairing, and empirically for the sorted pairing as well (correlation \(0.997\) on the 144 heads, as in the brief). Heads therefore spread along \(\Theta\) by the value of \(\mathbb E_w[t|t|]\) and leave \(\Theta\) only through sorting, which is small when \(s\) is moderate.

The Ginibre term is the overlap of two random \(n\)-frames. For random semi-orthogonal \(U,V\in\mathbb R^{N\times n}\), the entries of \(U^\top V\) have variance \(1/N\) and RMS \(N^{-1/2}=0.0361\). The Gaussian null in `gpt2_W.py` sits on this value (off-diagonal RMS \(0.036\), diagonal share \(1/n=0.0156\), \(t_i\) of RMS \(0.036\)). Trained heads use the same incoherent matrix and add a genuine diagonal.

### What the ensemble reproduces

Fit on each head: plant that head's measured \((t_i)\) and \(\Sigma\), redraw only \(Z\), and compare. Two draws per head, \(\sigma_E=0.0483\). "Bias" is the mean of predicted minus measured.

| statistic | data median | model median | bias | mean abs. error |
|---|---:|---:|---:|---:|
| \(\bar t\) | \(+0.003\) | \(+0.003\) | \(-0.001\) | \(0.002\) |
| \(s\) (weighted) | \(0.092\) | \(0.093\) | \(-0.001\) | \(0.001\) |
| off-diagonal RMS | \(0.048\) | \(0.048\) | \(+0.000\) | \(0.004\) |
| diagonal share | \(0.184\) | \(0.181\) | \(-0.007\) | \(0.029\) |
| \(\|W\|_F^2\) | \(11.8\) | \(11.5\) | \(-0.3\) | \(1.7\) |
| symmetric fraction of \(\|W\|_F^2\) | \(0.588\) | \(0.587\) | \(+0.014\) | \(0.071\) |
| \(c-d\) | \(0.000\) | \(0.000\) | \(-0.001\) | \(0.005\) |
| \(a-b\) | \(-0.012\) | \(-0.007\) | \(+0.004\) | \(0.027\) |
| err(1) | \(0.059\) | \(0.026\) | \(-0.049\) | \(0.049\) |
| kurtosis of off-diagonal entries (Gaussian \(=3\)) | \(20.6\) | \(3.0\) | \(-23\) | \(23\) |

Reading the table:

- The diagonal of \(W\) carries \(\bar t\), \(s\), \(c-d\), and the diagonal share. Across heads, \(|\bar t|\) correlates with diagonal share at \(0.85\), and only 24 percent of heads have \(|\bar t|>2s\). Both \(\mu\) and \(s_\star\) are active. L0H5 has \(\bar t=0.91\) and a narrow range; L5H9 has \(t_i\in[-0.60,+0.58]\). A single correlation \(r\), the ruled-out model \(K=rQ+\sqrt{1-r^2}G\), cannot make both.
- \(c-d\) follows \(\sum w_i t_i|t_i|\) whether or not \(Z\) is present (mean absolute error \(0.005\)).
- \(a-b\) has the sign the rearrangement argument gives, and the right magnitude up to about \(0.01\).
- Off-diagonal RMS, \(\|W\|_F^2\), and the symmetric fraction are the Ginibre bulk. The symmetric fraction matches because a diagonal (fully symmetric) plus an unstructured off-diagonal (half symmetric, half skew) has symmetric fraction \(\tfrac12+\tfrac12\cdot(\text{diagonal share})\). At the median diagonal share \(0.18\) this is \(0.59\), and the measured median is \(0.588\). The correlation of the two across heads is \(0.85\).
- Relation (1) is only half right. The model produces median err(1) \(0.026\) against measured \(0.059\) and against the Gaussian null \(0.011\). The sorting contribution from the spread of \(t_i\) is real (pure \(W=\mathrm{diag}(t)\) already gives median err(1) \(0.026\), and err(1) correlates with \(s\) at \(0.46\)), but it is not the whole measured error. The missing half is described under "What this leaves unexplained".
- Off-diagonal entries in the model are Gaussian. In the weights they are not: median kurtosis \(20.6\), median of \(\max|W_{ij}|/\mathrm{RMS}=12.8\) against about \(4\) for a Gaussian sample of this size, and the largest 5 percent of entries hold 41 percent of the off-diagonal Frobenius mass.

Replacing the measured \(t_i\) by a fresh \(N(\mu,s_\star^2)\) draw, with \((\mu,s_\star)\) the head's unweighted mean and standard deviation, changes \(c-d\) by mean absolute error \(0.014\) and \(s\) by \(0.03\). The Gaussian law is a slightly thin-tailed approximation: the within-head kurtosis of \(t_i\) has median \(4.1\), against \(3\) for a normal. A Laplace draw with the same mean and variance does not improve the profile errors.

Strongly aligned heads are the same ensemble at large \(\mu\) and small \(s_\star\). Planting \(t_i\sim N(0.85,0.08^2)\) in the row model of Candidate 2, which is this ensemble when the bulk is generated by random frames rather than by hand, gives diagonal share \(0.97\), off-diagonal RMS \(0.017\), \(\bar t=0.86\), \(a-b=-0.011\), err(1) \(=0.059\). L0H5 measures diagonal share \(0.955\), off-diagonal RMS \(0.024\), \(\bar t=0.91\), \(a-b=-0.023\), err(1) \(=0.199\). The contraction clip is what pulls the off-diagonal RMS down on these heads: off-diagonal RMS correlates with diagonal share at \(-0.49\).

### Singular values are not part of the two parameters

The participation ratio of \(\Sigma\) has median \(45.7\) against \(54.8\) for the Gaussian null, and it correlates with diagonal share at \(-0.10\). Alignment does not set the spectrum. \(Q\) and \(K\) separately have participation ratios \(55.5\) and \(56.0\) against \(59.0\) for a Gaussian \(64\times 768\) matrix, and the correlation of their sorted singular values has median \(0.97\). A mild global decay is enough to move the null: in the row model, row scales \(\alpha_i\propto i^{-0.08}\) give participation ratio about \(49.5\). I do not have a mechanism that derives the exponent. Using one global normalized curve for \(\sigma_i\), for example the coordinate-wise median of \(\sigma_i/(\sum_j\sigma_j^2)^{1/2}\) over the 144 heads, is consistent with everything above and adds no per-head parameter. Heads with participation ratio near \(25\) will not match that curve; they need their own scale concentration if the spectrum itself is the target.

### What this leaves unexplained: the other half of err(1)

Zeroing the off-diagonal of the measured \(W\) drops median err(1) from \(0.059\) to \(0.026\). Putting an i.i.d. Gaussian matrix of the same RMS back in its place leaves err(1) at \(0.026\). The bulk scale is not what creates the extra error. Shuffling the off-diagonal entries, which keeps every magnitude and destroys positions, also drops err(1) to \(0.025\).

The positions matter through the pairing \((W_{ij},W_{ji})\):

- Flipping the sign of \(W_{ij}\) and \(W_{ji}\) together, for every pair, leaves median err(1) at \(0.057\).
- Assigning independent random signs to the magnitudes \(|W_{ij}|\) drops median err(1) to \(0.034\).
- The correlation of \(W_{ij}\) with \(W_{ji}\) over all pairs has median \(-0.05\), so the bulk is incoherent. The largest 5 percent of pairs have symmetry score \(\mathbb E\bigl[|W_{ij}+W_{ji}|/(|W_{ij}|+|W_{ji}|)\bigr]=0.73\), where \(1\) is symmetric and \(0\) is skew.

So the extra err(1) lives in a preferentially symmetric set of large entries, in their original positions. A rank-one update, a heavy-tailed i.i.d. matrix, and a banded matrix with random signs do not reproduce it. Two phenomenological patches do move err(1) onto the measured value, and both damage something else:

- Eight symmetric pair-defects of amplitude \(0.45\), on top of a skew bulk of scale \(N^{-1/2}\), give median err(1) \(0.060\) and median \(a-b=-0.016\), with \(c-d\) unchanged. Off-diagonal RMS falls to \(0.038\), \(\|W\|_F^2\) to \(7.9\), and off-diagonal kurtosis rises to about \(80\).
- Copying the larger entry onto its transpose for the 50 largest pairs of a \(\sigma_E=0.0483\) Ginibre matrix gives median err(1) \(0.054\), but median \(a-b\) moves to \(-0.033\) and the entries stay Gaussian.

I do not promote either patch to the ensemble. Both are extra global parameters with no derivation, and neither matches the entry law and the profile at once. The coherent symmetric couplings are a real residual of about \(0.03\) in err(1).

### Why training would produce this

A head of width \(n\) has room for \(n\) features. Feature \(i\) is a rank-one form of strength \(\sigma_i\) and parity \(t_i=u_i^\top v_i\). Parity \(t\approx +1\) is a symmetric feature (the same direction is used for query and key). Parity \(t\approx 0\) is a rotation inside its plane, a purely antisymmetric feature. The sign of \(t\) selects the branch \(\Theta_+\) or \(\Theta_-\). The head is a mixture of parities, and \((\mu,s_\star)\) are the mean parity and the parity spread. The ruled-out ensembles are the boundaries: independent Gaussian query and key is \((\mu,s_\star)=(0,0)\); a single correlation \(r\) is \(s_\star=0\), \(\mu=r\); a scalar matrix \(tI\) plus incoherent noise is the same one-parameter slice. GPT-2 sits off that slice because \(s\) is typically as large as \(|\bar t|\).

The incoherent piece requires no training. Any two \(n\)-frames in \(\mathbb R^N\) overlap at scale \(N^{-1/2}\). GPT-2's overlap is a bit larger, \(\sigma_E=0.0483\) rather than \(0.0361\), which is the overlap law of frames in dimension \(N_{\mathrm{eff}}=1/\sigma_E^2\approx 430\) rather than \(768\). The pooled row-covariance of every \(Q\) and \(K\) in the model has participation ratio about \(500\) and a smooth spectrum (the top 10 eigenvalues hold 6 percent of the trace), so the residual stream that these weights occupy is not isotropic in all \(768\) coordinates. I treat \(\sigma_E\) as one measured global constant, not as a per-head parameter.

The factorization through \(Q\) and \(K\) is less rigid than \(L\). The relative rotation between the left singular bases of \(Q\) and \(K\) is an orthogonal matrix with diagonal share \(0.037\), against \(0.016\) for Haar, and its best assignment score is \(0.37\) against \(0.31\) for one Haar draw. Head space does not contain a shared feature basis that both \(Q\) and \(K\) are diagonal in. That is why the recipe samples \((\Sigma,W)\) and only then factors, instead of correlating named rows of \(Q\) and \(K\).

## Candidate 2, rejected: row-wise heterogeneous correlation

This is the natural sampler in weight space, and it is the same story as Candidate 1 whenever the feature basis coincides with the singular basis. It does not, so the sampler fails.

Draw row scales \(\alpha_i>0\) and parities \(t_i\in[-1,1]\). Draw \(q_i,g_i\) as independent Gaussian vectors in \(\mathbb R^N\), normalize them, and set
\[
Q_{i\cdot}=\alpha_i\,\hat q_i,\qquad
K_{i\cdot}=\alpha_i\bigl(t_i\hat q_i+\sqrt{1-t_i^2}\,\hat g_i\bigr).
\]
If the \(\hat q_i\) and \(\hat g_i\) were exactly orthogonal, \(W\) would be exactly \(\mathrm{diag}(t)\) and Candidate 1's block formulae would be exact. At \(N=768\) they are only approximately orthogonal, and the singular basis of \(L\) only lines up with the row basis when the \(\alpha_i\) or the \(t_i\) are very nonuniform.

Measured on 6 trials, flat \(\alpha_i=1\):

| planted \(t\) | out \(s\) | err(1) | \(a-b\) | diagonal share | off-diagonal RMS | participation ratio |
|---|---:|---:|---:|---:|---:|---:|
| \(N(0,0.15^2)\) | \(0.044\) | \(0.043\) | \(-0.023\) | \(0.024\) | \(0.040\) | \(55.0\) |
| \(N(0,0.40^2)\) | \(0.091\) | \(0.234\) | \(-0.160\) | \(0.047\) | \(0.058\) | \(54.8\) |
| \(N(0.80,0.10^2)\) | \(0.045\) | \(0.070\) | \(-0.016\) | \(0.960\) | \(0.021\) | \(50.7\) |
| data median | \(0.092\) | \(0.059\) | \(-0.012\) | \(0.184\) | \(0.048\) | \(45.7\) |

To keep a visible diagonal at a flat spectrum, the planted spread has to be about \(0.4\), and then relation (1) and \(a-b\) break by several times the measured amount. The output \(s\) is much smaller than the planted spread: a near-degenerate spectrum rotates the singular basis and smears \(\mathrm{diag}(t)\). A power-law scale \(\alpha_i\propto i^{-0.3}\) pins the basis somewhat (diagonal share rises) and collapses the participation ratio to about \(8\), far below \(45.7\). The mild exponent \(0.08\) gives participation ratio \(49.5\) and still a diagonal share near \(0.04\).

Regenerating each head from its own \(\alpha_i=\sigma_i(L)^{1/2}\) and its own measured \(t_i\) tells the same story. For a mid-share head the regenerated \(\|W\|_F^2\) is about half the measured value, because the model has no off-diagonal mass beyond \(1/N\). For L0H5 the regeneration matches (diagonal share \(0.99\) against \(0.96\), \(c-d\) \(0.83\) against \(0.82\)).

Candidate 2 is the right weight-space mechanism for heads with one dominant parity. It is the wrong sampler for a typical GPT-2 head. Candidate 1 is what Candidate 2 is trying to produce, written directly on the invariant \((\Sigma,W)\).

## Which ensemble, and what would falsify it

Candidate 1 is the one I would use. It has a one-line description (independent mode parities, plus the frame overlap of the residual stream), the parameters are the mean and spread of those parities, and the profile identities are the rank-one calculation plus rearrangement. Candidate 2 is the same idea pushed through a basis that GPT-2 does not use.

Four observations would falsify Candidate 1.

1. On a new model, \(c-d\) stops tracking \(\sum w_i t_i|t_i|\). On GPT-2 the correlation is \(0.997\) and the additive model keeps mean absolute error \(0.005\). A real failure of that identity means the diagonal of \(W\) is not the parity of the modes.
2. The symmetric fraction of \(\|W\|_F^2\) stops equalling \(\tfrac12+\tfrac12\cdot(\text{diagonal share})\). That equality is the statement that the off-diagonal part is incoherent. A structured off-diagonal large in Frobenius norm would break it. The present residual is visible in err(1) and in kurtosis, and it is small in Frobenius norm: the equality already holds to bias \(0.014\).
3. Off-diagonal RMS scales as \(N^{-1/2}\) on larger models, or it does not. GPT-2 medium has \(N=1024\), so \(N^{-1/2}=0.031\). If trained off-diagonal RMS stays near \(0.048\), the global scale is a property of training rather than of the ambient dimension, and \(N_{\mathrm{eff}}\approx 430\) has to be explained some other way. If it tracks \(N^{-1/2}\) with the same ratio \(0.048/0.036\approx 1.34\), the effective-dimension reading survives.
4. A model whose singular values are well separated, so that Candidate 2's row basis is forced to agree with the singular basis, still shows diagonal share near \(0.2\) at parity spread \(0.1\). Under Candidate 1 that head would show diagonal share near \(1\), as L0H5 already does. A counterexample would mean the diagonal in the singular basis is not the mode parity.

The open quantitative gap inside Candidate 1 is err(1): median \(0.026\) in the ensemble against \(0.059\) in the weights, caused by preferentially symmetric large entries of \(W\). A derivation of those entries that does not inflate \(a-b\) or the kurtosis would complete the model. It is not needed to explain why the heads lie along \(\Theta\).
