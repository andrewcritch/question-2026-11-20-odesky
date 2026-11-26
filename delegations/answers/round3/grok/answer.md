R13’s characterization holds, and R14’s limit holds, but the last sentence of line 161 does not: the law of \((f-g)/(f+g)\) does not determine the point on \(\Theta\).

## Where the conclusion is broader than the argument

Line 161, last sentence: “The position along \(\Theta\) is set by the law of \((f-g)/(f+g)\).”

The sentence before it is the correct one. Under the one-sign hypothesis, R13(3) gives
\[
c-d=\frac{\sum_i(f_i-g_i)|f_i-g_i|}{\sum_j(f_j+g_j)^2}=\frac{\sum_i\sigma_i^2\,t_i|t_i|}{\sum_j\sigma_j^2},
\]
with \(\sigma_i=f_i+g_i\) and \(t_i=(f_i-g_i)/(f_i+g_i)\), and the strong law turns the ratio of sums into
\[
\frac{\mathbb E[(f-g)|f-g|]}{\mathbb E[(f+g)^2]}=\frac{\mathbb E[\sigma^2\,t|t|]}{\mathbb E[\sigma^2]}.
\]
That is a \(\sigma^2\)-weighted average of \(t|t|\). The marginal law of \(t=(f-g)/(f+g)\) does not determine the weights.

Counterexample, both inside the hypotheses of R14 (\(f,g>0\), both nondecreasing, \(f-g\ge0\)). Let \(\mu=\tfrac12(\delta_0+\delta_1)\).

- Ensemble A: \(f(0)=g(0)=1\), \(f(1)=2\), \(g(1)=1\). Then \(t\in\{0,1/3\}\) with equal probability, and \(c-d=1/13\). The limiting profile is \((6/13,\,6/13,\,1/13,\,0)\).
- Ensemble B: \(f(0)=g(0)=1\), \(f(1)=20\), \(g(1)=10\). The law of \(t\) is the same, and \(c-d=25/226\approx0.1106\). The limiting profile is \((201/452,\,201/452,\,25/226,\,0)\).

Both points lie on the edge \(d=0\), \(a=b\). The unweighted mean \(\mathbb E[t|t|]=1/18\approx0.0556\) equals neither value, so the sentence is also not repaired by reading it as \(c-d\to\mathbb E[t|t|]\). The same split already appears at \(n=2\) with one draw of each atom: the two block forms have the same multiset of \(t_i\) and different profiles. A direct diagonalization of those two block forms reproduces both profiles to machine precision.

What the argument does establish, and what a replacement sentence can say: on the one-sign edge, the limiting position is the number \(\mathbb E[\sigma^2\,t|t|]/\mathbb E[\sigma^2]\). Choosing the joint law of \((\sigma,t)\), or equivalently of \((f+g,\,(f-g)/(f+g))\), sets that number.

## Boundary clause in R13

Line 141, second sentence: “Every point of \(\Theta\) is attained (e.g. \(t_i\equiv t\)).”

The iff in the first sentence of line 141 is right. The attainment sentence is not, inside the setting as written. Line 135 requires \(t_i\in(-1,1)\), so
\[
a=\sum_i w_i(1-t_i^2)/2>0.
\]
Varying a common \(t\in(-1,1)\) fills both edges of \(\Theta\) except the corners \((0,0,1,0)\) and \((0,0,0,1)\). Those corners are the profiles of the rank-one forms with \(t=\pm1\), and they are limits of the family the proof does construct. Extending the setting to \(t_i\in[-1,1]\) makes the sentence true. The open constraint makes it false.

## What holds

The step checked hardest is R13(2), line 145, and its reuse on line 163. Comonotonicity supplies one permutation that sorts \(\alpha\) and \(\beta\) decreasing together: order by \(\alpha\) and break ties by \(\beta\). For positive nonincreasing sequences the product is nonincreasing, because \(x_1\ge x_2>0\) and \(y_1\ge y_2>0\) give \(x_1 y_1\ge x_2 y_1\ge x_2 y_2\). So \(\sqrt{\alpha_{\pi(k)}\beta_{\pi(k)}}\) is already the sorted list \(\sigma(T)\), and relation (1) holds at every sorted index. This is stronger than the log-mean identity in R5, which fixes only \(\sum\log\sigma(T)_i\). A tie example \(\alpha=(2,2,1)\), \(\beta=(0.4,1.5,0.3)\) has relative error \(0\) after that tie break. Dropping monotonicity leaves an \(O(1)\) gap: with \(f\) increasing and \(g\) decreasing, at \(N=2000\) and \(n=4\) the median relation-(1) error on 10 draws was about \(0.62\), and \(a-b\) stayed negative.

R13(1), line 144, matches the rearrangement inequality, including the strict case. A discordant pair \((i,j)\) raises \(\sum\alpha_k\beta_k\) by \(-(\alpha_i-\alpha_j)(\beta_i-\beta_j)>0\), so the identity pairing is not maximal. On \(\alpha=(1,1.001)\), \(\beta=(1,0.999)\) this predicts \(a-b=-2.5\times10^{-7}\), and the block form returns that value. Equality when there is no discordant pair is the common sorting just described. Two hundred random block forms, half of them comonotone, produced no failure of (1)–(3): \(a\le b\), equality and relation (1) exactly on the comonotone ones, and \(c-d=\sum w_i t_i|t_i|\) there.

R13(3), line 146, is the same common order: \(\lambda_{+,k}-\lambda_{-,k}=\sigma_{\pi(k)}t_{\pi(k)}\). So \(d=0\) if and only if every \(t_i\ge0\), and \(c=0\) if and only if every \(t_i\le0\). One sign alone does not put the profile on \(\Theta\). For \((\sigma,t)=((3,2),(0.8,0))\) one has \(d=0\) but the pairs are discordant, \(a-b\approx-0.183\), and the relation-(1) error is about \(0.64\).

The first sentence of line 141 follows: \(a=b\) if and only if \((\alpha,\beta)\) is comonotone, and then \(cd=0\) if and only if the \(t_i\) are all nonnegative or all nonpositive.

R14’s limit, line 163, also holds for fixed \(n\) as \(N\to\infty\). Conditional on \(\rho\), the strong law makes the rows of \(P/\sqrt N\) and \(M/\sqrt N\) orthonormal, so \(M_N=FF^\top\) converges to the Gram matrix of orthogonal channels with \(|\pi_i|^2=f(\rho_i)\) and \(|\delta_i|^2=g(\rho_i)\). In that geometry \(S=\Pi^\top\Pi-\Delta^\top\Delta\) has eigenvalue \(+f(\rho_i)\) on \(\pi_i\) and \(-g(\rho_i)\) on \(\delta_i\), and those two eigenvectors span the \(i\)-th rank-one block. Thus the block parameters are \(\alpha_i=f(\rho_i)\) and \(\beta_i=g(\rho_i)\), not merely the two spectra separately. Both functions nondecreasing makes every realization comonotone, so R13(2) gives exact relation (1) and \(a=b\) in the limit. Membership in \(\Theta\) needs a sign condition in addition; comonotonicity does not force it. With both functions nondecreasing and \(f-g\) changing sign, draws at \(N=2000\) had \(a-b\) of size a few thousandths and a small relation-(1) error, while \(c>0\) and \(d>0\).

The passage through \(M_N\) is legitimate at the limit points this ensemble actually produces. Ordered eigenvalues of \(J'M_N\) and \(\Omega M_N\) are continuous, and \(f,g>0\) keeps the limit in the open set where \(S\) has signature \((n,n)\) and every \(\lambda_\pm\) and \(\sigma(T)\) is positive, so the profile and a relative relation-(1) error are continuous there. The “wherever \(\|L\|\ne0\) and \(\sigma(T)\ne0\)” clause on line 163 names a larger set than that open set. Convergence for this ensemble only uses continuity at these limit points.

The \(c-d\) limit on line 161 is an iterated limit: \(N\to\infty\) first, with \(n\) fixed, then \(n\to\infty\) for the block-form profiles. Read that way, the ratio of expectations is correct; a Monte Carlo check with \(\rho\sim N(0,1)\), \(f=e^{\rho}+2\), \(g=\tfrac12 e^{\rho}+\tfrac12\) gave expectation about \(0.1857\), and the finite-\(n\) block-form values moved from about \(0.214\) at \(n=10\) to about \(0.1875\) at \(n=5000\). A joint limit \(n,N\to\infty\) for the Gaussian ensemble is not proved. Finite-\(N\) runs with \(n=4\) and this same \((f,g)\) are consistent with the \(N\to\infty\) claim: the median \(|a-b|\) fell from about \(1.3\times10^{-2}\) at \(N=20\) to about \(4\times10^{-4}\) at \(N=1500\), and the median relation-(1) error fell from about \(0.12\) to about \(0.009\).

Line 165’s pointer from \(g\equiv\mathrm{const}\) to the signed-spike ensemble R9 matches the \(N\to\infty\) profile when the spike coefficient is positive: the channel calculation gives \(\beta\) constant and \(\alpha\) increasing in the squared Gaussian coordinate. A negative coefficient swaps the roles and is the case \(f\equiv\mathrm{const}\) instead. That is a loose label in the special-cases line, not a gap in the limit theorem.
