VERDICT: R13’s characterization and R14’s fixed-n convergence survive this challenge, but the endpoint-attainment claim in line 141 and the unweighted-law claim in line 161 are false as written.

I read R13–R14, the specified givens R1, R2, and R5, and the definitions in `question.md`. All line references below refer to `record.md`. I worked independently and did not modify the project files.

**1. Line 141: “Every point of Θ is attained” exceeds the stated setting.**

Line 135 requires every σᵢ > 0 and every tᵢ ∈ (−1,1). Consequently

\[
a=\frac{\sum_i\sigma_i^2(1-t_i^2)}{2\sum_i\sigma_i^2}>0.
\]

The points (0,0,1,0) and (0,0,0,1) belong to Θ, but neither is attainable under these hypotheses. Taking every tᵢ equal to t attains all the other points of Θ; the excluded endpoints require t = 1 or t = −1.

This is a boundary error in the final sentence, not an error in the preceding “if and only if” characterization. A minimal correction is: “Every point of Θ except its two endpoints is attained; the endpoints belong to the closure.” Allowing tᵢ = ±1 is another correction, but then the spectral lists require zero padding and the nondegeneracy statements require adjustment.

**2. Line 161, final sentence: the ordinary law of (f−g)/(f+g) does not determine the position along Θ.**

The displayed expectation formula earlier in the same line is correct for the limiting block profiles under its moment assumption. It depends on channel strength as well as channel cosine. Write

\[
s=f(\rho)+g(\rho),\qquad t=\frac{f(\rho)-g(\rho)}{f(\rho)+g(\rho)}.
\]

Then the asserted limit is

\[
\frac{\mathbb E[s^2t|t|]}{\mathbb E[s^2]},
\]

which is not determined by the marginal law of t.

Here is an exact counterexample satisfying all the monotonicity, positivity, sign, and moment assumptions. Let μ put probability 1/2 at each of 0 and 1. Define two ensembles by the following values:

| Ensemble | (f(0), g(0)) | (f(1), g(1)) |
|---|---|---|
| A | (1,1) | (3,1) |
| B | (1,1) | (6,2) |

Extend each function to all of ℝ by using its value at 0 for x < 1 and its value at 1 for x ≥ 1. The functions are positive, measurable, nondecreasing, and satisfy f−g ≥ 0 everywhere. In both ensembles, t has law

\[
\tfrac12\delta_0+\tfrac12\delta_{1/2}.
\]

Nevertheless, after the fixed-n block limit and then n → ∞,

\[
(c-d)_A=\frac{0+4}{4+16}=\frac15,
\qquad
(c-d)_B=\frac{0+16}{4+64}=\frac4{17}.
\]

Their limiting profiles are respectively (2/5,2/5,1/5,0) and (13/34,13/34,4/17,0). Thus they occupy different points of Θ despite identical laws of t. The same discrepancy already occurs for the two-channel block realizations with latent values 0 and 1.

A precise replacement for the final sentence is: “The position along Θ is set by the law of t weighted by (f+g)².” Equivalently, define

\[
\nu(B)=\frac{\mathbb E[s^2\mathbf1_{\{t\in B\}}]}{\mathbb E[s^2]}.
\]

Then c−d = ∫t|t| dν in the large-n block limit. No independence between s and t is assumed in R14, and the monotonicity assumptions do not provide it.

**3. Line 161: state the order of limits explicitly.**

The proof establishes the limit N → ∞ for each fixed n. Its subsequent strong-law argument establishes

\[
\lim_{n\to\infty}\left[\lim_{N\to\infty}(c_{n,N}-d_{n,N})\right]
=\frac{\mathbb E[(f-g)|f-g|]}{\mathbb E[(f+g)^2]}.
\]

Equivalently, it establishes the n → ∞ limit of the block profiles π∞,n. This is a valid iterated-limit statement. The argument supplies no uniform control in n and therefore does not establish an arbitrary simultaneous limit with n = n(N) → ∞. I treat this as a clarification of scope, rather than a counterexample to the natural iterated-limit reading.

**Steps that withstand the challenge.**

- **Lines 143–144, including ties:** the Frobenius identities and the equality characterization in the rearrangement inequality are correct. A discordant pair permits a strictly improving swap. In the absence of a discordant pair, sorting by α and breaking ties by β sorts both lists. This establishes the exact equivalence a = b ⇔ comonotonicity.
- **Line 145:** a common decreasing order of two positive lists also orders their products. Thus the geometric means are already sorted, and relation (1) follows at every sorted index.
- **Lines 146–147:** under the common ordering, each sorted difference is σᵢtᵢ. Positivity of σᵢ makes d = 0 equivalent to all tᵢ ≥ 0 and c = 0 equivalent to all tᵢ ≤ 0. This proves the claimed preimage of Θ. The formula for c−d actually holds for every comonotone pair, including mixed signs.
- **Line 161, expectation formula:** for the block profiles, c−d is the ratio of the sums of (f−g)|f−g| and (f+g)². The stated finite second-moment assumption makes both integrable, since |(f−g)|f−g|| ≤ (f+g)². The denominator expectation is strictly positive. The strong law therefore proves the ratio limit.

**The step I checked hardest was line 163: passage from the Gram-matrix limit to the ordered spectral data.**

Set Π = (Q+K)/2 and Δ = (K−Q)/2. Conditional on the finitely many latent values, independence and the strong law give

\[
\Pi\Pi^\top\to D_f,\qquad
\Delta\Delta^\top\to D_g,\qquad
\Pi\Delta^\top\to0,
\]

where D_f = diag(f(ρᵢ)) and D_g = diag(g(ρᵢ)). The cross-Gram convergence is essential; it follows from independence of P and M. Since Q = Π−Δ and K = Π+Δ,

\[
M_N\to M_\infty=
\begin{pmatrix}D_f+D_g&D_f-D_g\\D_f-D_g&D_f+D_g\end{pmatrix}.
\]

This limit is positive definite, with eigenvalues 2f(ρᵢ) and 2g(ρᵢ). The nonzero spectral lists of S and T can be read from the symmetric matrix $\tfrac12 M_N^{1/2}J'M_N^{1/2}$ and the skew-symmetric matrix $\tfrac12 M_N^{1/2}\Omega M_N^{1/2}$. Multiplication of the latter by i gives a Hermitian matrix. Ordered eigenvalues of these matrices vary continuously, including at repeated eigenvalues. The limiting positive and negative magnitudes are f(ρᵢ), g(ρᵢ), and the limiting antisymmetric singular values are √(f(ρᵢ)g(ρᵢ)). All are positive.

Also,

\[
\|L\|_F^2=\operatorname{tr}((QQ^\top)(KK^\top))
\longrightarrow\sum_i(f(\rho_i)+g(\rho_i))^2>0.
\]

Thus normalization, sorting, and any usual continuous relative or logarithmic error in relation (1) are legitimate near the limit. For fixed n, no moment assumption on μ is needed: conditioning fixes finitely many finite positive values of f and g. Both functions being nondecreasing gives the required comonotonicity. I found no failure in this convergence argument.

**Numerical checks.** I ran `check_r13_r14.py` with the supplied Python and `-I`. All 729 choices of α,β ∈ {1,2,3}³ passed the equality/comonotonicity test; the comonotone cases also passed the sorted relation-(1) and sign tests. A fixed four-channel Gaussian sample, coupled by prefixes, gave maximum profile error 0.02524 at N = 128 and 0.0006060 at N = 131072; the maximum relative error in relation (1) decreased from 0.1414 to 0.002076. These checks support the algebra but do not replace the arguments above. The two counterexample profiles were also checked numerically; their rational values above are exact.
