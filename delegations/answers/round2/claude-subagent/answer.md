# Round 2, Claude subagent: one ensemble for all 144 GPT-2 heads ("split-pair spike" ensemble)

**Verdict: partial success; not ready to propose as the final answer.** One recipe with 5 parameters per head and 2 global constants covers heads with a<b and heads with a>b. A single parameter, the spike symmetry probability π, moves a head across a=b. Fitted on 5 statistics per head, it predicts the relation-(1) error at 0.91 of the measured median level (Gaussian off-diagonals reach 0.68), with cross-head correlation 0.81 (0.91 without layer 0). It **fails** in three places:
(a) it predicts only 35 of the 44 heads with a>b, and it misses the extreme layer-0 heads L0H3, L0H4, L0H7 and L0H10 badly;
(b) its large off-diagonal pairs are not symmetric enough (symmetry score 0.67 against 0.80 measured);
(c) it does not predict the per-head kurtosis (correlation 0.14).
The failures point to one missing ingredient, stated under "Falsifiers": the negative reciprocal overlap q in a>b heads sits on the **top singular pairs**, not on spikes spread at random.

All numbers below come from one run each, at 4 simulations per head (seed 11). Convention: **raw L = KᵀQ**, with no LayerNorm folding. All statistics use the `common.stats` definitions from round 1, plus Grok's kurtosis and top-5% symmetry score.

## 1. The ensemble (sampling recipe)

The ensemble works in the SVD gauge of R1, because (Σ, W) is a complete invariant up to O(N) congruence.

Per-head parameters (5): v, τ, ω, o² (off-diagonal variance of W), κ (reciprocal covariance of the off-diagonal pairs).
Global constants (2, plus a cap): spike fraction ρ = 0.05, spike energy share f = 0.6, and a singular-value cap of 0.999 on W.
Derived quantities: γ = max(f·o², |κ|) (spike variance per entry), β = o² − γ (bulk variance), π = ½(1 + κ/γ) ∈ [0,1].

1. Singular values: σ_i = exp(√v ξ_i), with ξ_i i.i.d. N(0,1), for i = 1..n.
2. Diagonal tilts: t_i = clip(τ + ω η_i, ±0.999), with η_i i.i.d. N(0,1).
3. Bulk: B_ij i.i.d. N(0, β) for i ≠ j. The bulk has no reciprocal correlation.
4. Spikes: for each unordered pair i<j, independently with probability ρ, draw z ~ N(0, γ/ρ). Add z to E_ij and ε_ij·z to E_ji, where ε_ij = +1 (symmetric spike) with probability π and −1 (antisymmetric spike) otherwise.
5. W = diag(t) + B + spikes. Clip the singular values of W at 0.999, so that W is a contraction. This step changed W in 65 of 144 heads in at least one simulation; it barely moves the error ratio (0.91 for heads it changed, 0.90 for the rest).
6. Realization: take U = [I_n; 0] and V = [W; (I − WᵀW)^{1/2}], padded with zeros to N rows. Then K = Σ^{1/2}Uᵀ O and Q = Σ^{1/2}Vᵀ O with O Haar in O(N), so that L = KᵀQ = Oᵀ U Σ Vᵀ O. Any GL(n) change K→AK, Q→A^{-T}Q leaves L unchanged.

Without the spikes (ρ=1, f=0), this reduces to the diagonal-plus-Gaussian-noise family of round 1. With ε_ij ≡ +1, all spikes are symmetric.

## 2. Mechanisms

**(i) a>b, derived.** R4 gives a = ½(1 − m₂ − q) and a − b = c + d − m₂ − q exactly. In the ensemble the bulk and the diagonal do not contribute to q in expectation, so

  E[q] ≈ (2π−1)·γ·E[Σ_{i≠j}σ_iσ_j]/E[F] ≈ (2π−1)·γ·(n−1)e^{−v} = κ(n−1)e^{−v}.

So π < ½ (mostly antisymmetric spikes) gives q < 0, and a head moves to a > b once −q > m₂ − (c+d). In the fit, the correlation between π and the measured a−b is −0.88. The bulk/spike split does not affect this mechanism; only the reciprocal sign of the off-diagonal pairs does.

**(ii) The full level of the relation-(1) error: numerical, with only a heuristic explanation.** Hold the off-diagonal RMS and q fixed. Moving the off-diagonal energy from Gaussian entries into sparse spikes raises the predicted median error from 0.68× to 0.91× of the measured level (table in §3). Heuristic: relation (1) holds exactly for diagonal W (R2). Off-diagonal pairs break it at second order, through the products E_ijE_ji and E_ij², weighted by σ. Concentrating a fixed energy into a few large pairs makes those few 2×2 blocks depart strongly from rank one, which spreads the log-ratios log(σ(T)_i/√(λ₊λ₋)). By R5 the log-ratios have mean zero, so spread is the only way relation (1) can fail. I have not derived this.

**(iii) Heavy tails and symmetric-leaning large pairs.** The heavy tails are built in. For Bernoulli-Gaussian spikes, the off-diagonal kurtosis is ≈ 3(1 − f² + f²/ρ) = 23.5 for f=0.6 and ρ=0.05; the simulated median is 22.9 and the measured median 20.6. The symmetric lean of the large pairs is **not** built in independently: it equals π, and π is fixed by q. This is where the model fails (§4).

## 3. Fit and predictions (all 144 raw heads)

**Fitted statistics (5 per head), each matched by a moment formula:**
- v = log(n/PR)/4
- τ = measured σ²-weighted mean of t_i
- ω = measured σ²-weighted std of t_i
- o² = measured off-diagonal RMS²
- κ = q_measured·e^{v}/(n−1), clipped to ±o²

The global constants ρ and f were picked from a small grid (below) to bring the median relation-(1) error and median kurtosis to the right level. Those two medians are therefore partly tuned, not purely predicted. Their per-head variation is still predicted.

Median [10th, 90th percentile]; correlation is across heads, measured versus simulated mean (`log_final_mix_0.05_0.6.txt`):

| | statistic | measured | model | corr |
|---|---|---|---|---|
| FIT | PR | 45.7 [24.6, 52.5] | 46.9 [29.5, 53.0] | 0.987 |
| FIT | t̄ | 0.003 [−0.192, 0.243] | 0.003 [−0.200, 0.251] | 0.998 |
| FIT | std t | 0.092 [0.057, 0.246] | 0.092 [0.056, 0.233] | 0.992 |
| FIT | off-diag RMS | 0.048 [0.042, 0.054] | 0.048 [0.041, 0.054] | 0.971 |
| FIT | q | 0.007 [−0.029, 0.034] | 0.006 [−0.036, 0.038] | 0.942 |
| pred | **relation-(1) error** | 0.059 [0.037, 0.156] | 0.052 [0.035, 0.130] | **0.806** (0.909 excl. layer 0) |
| pred | **a − b** | −0.012 [−0.056, 0.020] | −0.018 [−0.085, 0.015] | 0.867 (0.910 excl. L0) |
| pred | c − d | 0.000 [−0.066, 0.062] | 0.000 [−0.041, 0.061] | 0.986 |
| pred | c + d | 0.024 [0.003, 0.129] | 0.014 [0.002, 0.088] | 0.979 |
| pred | min(c,d) | 0.000 [0.000, 0.004] | 0.000 [0.000, 0.000] | 0.27 |
| pred | diagonal share of W | 0.184 [0.039, 0.552] | 0.181 [0.037, 0.520] | 0.961 |
| pred | off-diag kurtosis | 20.6 [4.4, 54.4] | 22.9 [20.6, 25.7] | 0.14 |
| pred | top-5% symmetry score | 0.804 [0.676, 0.907] | 0.666 [0.510, 0.786] | 0.72 |
| pred | a | 0.481 [0.412, 0.504] | 0.480 [0.418, 0.504] | 0.986 (a = ½(1−m₂−q) is nearly fitted) |
| pred | b | 0.494 [0.439, 0.512] | 0.498 [0.460, 0.529] | 0.929 |

Further results:
- **Sign of a−b:** agrees in 85% of heads. The model gives a>b in 35 heads; 44 heads have a>b.
- **Relation-(1) error by group:** for heads with a>b, measured 0.046 [0.035, 0.161] against model 0.048 [0.035, 0.120]. For heads with a<b, measured 0.063 [0.039, 0.147] against model 0.056 [0.035, 0.134]. The same recipe gives the right level in both groups.
- **Which statistics are true predictions:**
  - The diagonal share is nearly arithmetic, given t̄, std t and the off-diagonal RMS, so its 0.96 is weak evidence.
  - c−d follows from t̄ and t-spread (R3: c−d ≈ Σσ²t|t|/F), so its 0.986 is also weak evidence.
  - The informative predictions are the relation-(1) error, b (hence a−b), c+d, kurtosis and symmetry.

**Variant grid** (2 simulations per head; files `log_2_*.txt`). "spike-sym" puts all spikes in the symmetric component; "mix" lets the spike type vary:

| variant | err1 median ratio model/measured | err1 corr | kurtosis median (measured 20.6) | symmetry median (measured 0.80) | sign(a−b) agreement |
|---|---|---|---|---|---|
| Gaussian off-diagonal, q fitted | 0.68 | 0.81 | 3.0 | 0.82 | 0.91 |
| Student-t(3) symmetric part | 0.74 | 0.80 | 7.8 | 0.83 | 0.90 |
| spike-sym ρ=0.05 | 0.90 | 0.76 | 17.3 | 0.71 | 0.88 |
| spike-sym ρ=0.1 | 0.81 | 0.78 | 10.0 | 0.96 | 0.88 |
| mix ρ=0.05, f=0.5 | 0.87 | 0.80 | 17.2 | 0.69 | 0.85 |
| **mix ρ=0.05, f=0.6 (headline, 4 sims)** | **0.91** | **0.81** | **22.9** | **0.67** | **0.85** |
| mix ρ=0.05, f=0.7 | 0.99 | 0.77 | 30.1 | 0.65 | 0.85 |
| mix ρ=0.02, f=0.5 | 0.91 | 0.78 | 36.4 | 0.73 | 0.81 |

The grid shows a trade-off. Concentrating the off-diagonal energy into spikes raises the level of the relation-(1) error to the measured one. It lowers the across-head correlation slightly, from 0.81 to 0.77, and it lowers the sign agreement of a−b, from 0.91 to 0.81–0.85. No setting matches the level, the symmetry and the per-head kurtosis at once.

## 4. Falsifiers and worst heads

**Worst heads, by |log(model/measured)| of the relation-(1) error:**

| head | err1 measured / model | a−b measured / model | kurtosis measured / model |
|---|---|---|---|
| L0H7 | 0.362 / 0.090 | +0.141 / −0.021 | 69.6 / 59.4 |
| L0H3 | 0.381 / 0.129 | +0.195 / +0.079 | 42.6 / 59.8 |
| L0H4 | 0.330 / 0.138 | +0.161 / +0.094 | 28.7 / 53.2 |
| L0H10 | 0.190 / 0.089 | +0.044 / −0.002 | 111.7 / 54.7 |
| L1H3 | 0.140 / 0.061 | | |
| L0H5 | 0.199 / 0.105 | | |

L1H9 and L6H8 are also among the worst eight. These are the positional layer-0 heads of R6.

**Diagnosis of the layer-0 failures (derived from the fit, not a heuristic):**
- In L0H3, L0H4, L0H7 and L0H10, the measured q (−0.20, −0.17, −0.17, −0.05) exceeds what any ensemble with σ-independent off-diagonal entries can produce. The bound is |E q| ≤ o²(n−1)e^{−v} ≈ 0.07–0.1 for these heads.
- The fit hits the clip: π = 0 and β = 0, so the model's q stays too small.
- So the negative reciprocal overlap in a>b heads must be **concentrated on pairs (i,j) with large σ_iσ_j**: antisymmetric coupling between the top singular directions. This is a rotation-type 2-plane, which matches R6's finding that complex-eigenvalue mass ι tracks a−b.
- 10 of 144 heads hit the clip (6 at π=0, 4 at π=1).

**The symmetry failure points the same way.** In heads with a>b, the measured top-5% pairs are still symmetric-leaning (0.72 median), yet q < 0. So the large pairs, symmetric, and the negative-q pairs, antisymmetric and weighted toward the top σ, are different pairs. In my ensemble one coin π sets both, so the model cannot be symmetric in its large pairs and negative in q at once.

**Concrete falsifiers for this ensemble (some are already met):**
1. **Already met, so this ensemble is falsified as stated.** For some head, |q| > o²(n−1)e^{−v}; this holds in at least 4 layer-0 heads.
2. The per-head kurtosis is uncorrelated with anything the model fits (corr 0.14). A model with global ρ and f cannot explain why some heads have kurtosis 4 and others 135.
3. In the data, the symmetry score of large pairs and π are distinct quantities, whereas the ensemble ties the symmetry of large pairs to sign(q).

**Suggested repair (untested, a heuristic):** split the off-diagonal part into two independent pieces:
- (A) sparse **symmetric** spikes, spread uniformly over pairs, which carry the heavy tail and the extra relation-(1) error;
- (B) an **antisymmetric** coupling whose size scales with σ_iσ_j, or which is restricted to the top-k singular directions. One signed amplitude per head sets q, and its sign moves the head across a=b.

This keeps the same parameter count (replace π by the amplitude of B) and decouples (iii) from (i). I ran out of time before testing it.

## Not checked
- The repair above.
- LayerNorm-folded heads.
- Simulation noise beyond 4 draws per head; the across-head correlations of the simulated means may rise somewhat with more draws.
- An analytic formula for the relation-(1) error under spikes.
- Any model other than GPT-2 small.

## Files
All in `/Users/andrew/maisi/questions/2026-11-20-odesky/delegations/answers/round2/claude-subagent/`:
- `ens.py`: ensemble, fit and comparison. Usage: `python -I ens.py NSIM NU VARIANT RHO F`. The headline run is `4 3 mix 0.05 0.6`.
- `fit_*.csv`: per-head fitted parameters, measured statistics and simulated statistics.
- `log_*.txt`: run outputs. The headline output is `log_final_mix_0.05_0.6.txt`.
- `probe.py`: checks whether the large W pairs sit at near-degenerate σ. They do not: the median log-σ gap is 0.22 for the top 5% of pairs against 0.27 for all pairs, and the correlation is −0.13. The top 5% of pairs carry a median 35% of the off-diagonal energy.
