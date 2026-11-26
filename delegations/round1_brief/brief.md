# Brief: find one random-matrix ensemble for trained attention heads

## Goal

Propose one natural random ensemble of query/key pairs $(Q,K)$, $Q,K\in\mathbb R^{n\times N}$, with few parameters (ideally one or two per head), whose samples $L=K^\top Q$ reproduce the statistics that trained GPT-2 heads show (listed below). "Natural" means the ensemble has a short description and, ideally, a plausible reason why training would produce it. Ideas that also explain the singular-value spectrum $\Sigma$ of $L$ are a bonus, not a requirement.

## Files in this folder

- `question.md`: the MaisiOverflow question (relations (1) and (2), the profile $(a,b,c,d)$, the set $\Theta$).
- `paper.txt`: text of the source paper, arXiv:2609.22990 (O'Desky, "On attention heads and bilinear forms").
- `gpt2_W.py`: the script that produced `gpt2_W.csv`. Read it for exact definitions of every statistic.
- `gpt2_W.csv`: per-head statistics for all 144 GPT-2-small heads. `var` is `raw` ($L=K^\top Q$), `lnfold` (LayerNorm gain and centering folded in), or `gauss` (independent Gaussian null of the same shape).
- `sim.py`: earlier synthetic experiments.
- `gpt2_model.safetensors`: GPT-2 small weights. In `h.{l}.attn.c_attn.weight` (768×2304), head $h$ has $Q=W[:,64h:64h+64]^\top$ and $K=W[:,768+64h:768+64h+64]^\top$.
- A Python with numpy, scipy, and safetensors is at `/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/venv/bin/python`. Run it with `-I`.

## Established facts

1. **Complete invariant.** Write the SVD $L=U\Sigma V^\top$ (rank $n$) and $W=U^\top V$ ($n\times n$, a contraction). For $N\ge 2n$, the pair $(\Sigma,W)$ determines $L$ up to orthogonal congruence $L\mapsto OLO^\top$, modulo the SVD's signed-permutation ambiguity. The profile and relations (1) and (2) are functions of $(\Sigma,W)$.
2. **Block model.** If $W=\mathrm{diag}(t_i)$, then $L$ is an orthogonal sum of rank-one forms, with $\lambda_{\pm,i}=\sigma_i(1\pm t_i)/2$ and $\sigma_i(T)=\sigma_i\sqrt{1-t_i^2}/2$, before sorting. Relation (1) is exact per block. Separate sorting of $\lambda_+$, $\lambda_-$, $\sigma(T)$ breaks it when the $t_i$ vary.
3. **Synthetic results** (`sim.py`). Off-diagonal entries of $W$ affect (1) only weakly (second order). Variation of the diagonal $t_i$ within a head breaks (1) and moves $a-b$ away from 0.

## GPT-2 small measurements (raw $L$; median [10th, 90th percentile] over 144 heads)

| statistic | trained | Gaussian null |
|---|---|---|
| diagonal share $\sum t_i^2/\|W\|_F^2$ | 0.18 [0.04, 0.55] | 0.016 |
| $\bar t=\sum\sigma_i^2t_i/\sum\sigma_i^2$ | 0.003 [−0.19, +0.24] | 0.000 |
| within-head std of $t_i$ (σ²-weighted) | 0.09 [0.06, 0.25] | 0.036 |
| off-diagonal RMS of $W$ | 0.048 [0.042, 0.054] | 0.036 |
| relative error of (1), per sorted index | 0.059 [0.04, 0.16] | 0.011 |
| $a-b$ | −0.012 [−0.06, +0.02] | −0.001 |
| $c-d$ | 0.000 [−0.07, +0.06] | 0.000 |
| participation ratio of $\Sigma$ | 45.7 [24.6, 52.5] | 54.8 |

More observations:

- $c-d$ is predicted by $\sum\sigma_i^2t_i|t_i|/\sum\sigma_i^2$ with correlation 0.997.
- Across heads, $|\bar t|$ correlates with the diagonal share at 0.85. The (1)-error correlates with the within-head std of $t_i$ at 0.46.
- Only 24% of heads have $|\bar t|>2\,\mathrm{std}(t_i)$. Strongly aligned heads can still have wide $t_i$ ranges. For example, L5H9 has $t_i\in[-0.60,+0.58]$, and L0H5 has $\bar t=0.91$ with $t_i\in[-0.02,0.95]$.
- Across heads with $|\bar t|>0.05$, the median correlation between singular-value index and signed $t_i$ is −0.11. The top singular directions are slightly more aligned.
- With LayerNorm folded in, 20% of heads have $|a-b|>0.1$ (7.6% raw), and some heads collapse to participation ratio about 4.

## Ruled out

- **Independent Gaussian $Q,K$.** Every head sits at the single point $(\tfrac12,\tfrac12,0,0)$.
- **Correlated Gaussian, $K=rQ+\sqrt{1-r^2}\,G$.** Moves along $\Theta$, but gives near-constant $t_i\approx r$ and a Marchenko–Pastur $\Sigma$.
- **$W=tI+$ small incoherent noise, one $t$ per head.** Within-head spread of $t_i$ in GPT-2 is far too large for this.

## What I'd like back

Write `./answer.md` in your working directory containing:

1. One to three candidate ensembles, each given precisely (a sampling recipe for $Q,K$ or for $(\Sigma,W)$), with parameter counts.
2. For each candidate, which measured statistics it reproduces and why, with a derivation or heuristic.
3. Any check you ran against `gpt2_W.csv` or the weights, with numbers. Fitting a candidate's parameters per head and comparing the predicted and measured statistics would be ideal. Put any scripts you write in your working directory.
4. Your view of which candidate is most natural, and what would falsify it.

Your own judgement on what counts as natural is welcome. If you think the target is mis-posed, say so and say why.
