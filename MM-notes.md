# MM notes: settled facts about the subject matter

- **Do not propose a diagonal-$W$ ensemble as the final answer.** Every diagonal-$W$ ensemble has $a-b\le0$ (record R4), and 44 of 144 raw GPT-2 heads have $a-b>0$. Any candidate needs off-diagonal reciprocal overlap $q=\sum_{i\ne j}\sigma_i\sigma_jE_{ij}E_{ji}/F$.
- **Do not describe off-diagonal entries of $W$ as negligible.** Each entry acts at second order, but the $n(n-1)$ reciprocal products sum to $q$, which controls $a-b$ (correlation −0.97 on GPT-2).
- **Do not propose $W=tI$ plus small incoherent noise with one $t$ per head.** GPT-2's within-head spread of $t_i$ is 0.09 at the median, against 0.036 for the null (record R3).
- **State which LayerNorm convention a measurement uses.** Raw $L$ and LayerNorm-folded $L$ give different fractions of heads off $\Theta$ (record R3).
- **Do not cite the top-5% symmetry score as evidence of symmetric pairs.** Its Gaussian-baseline value is 0.79, equal to the trained value (record R8 correction).
- **Do not model the off-diagonal heavy tail of $W$ as symmetric spikes.** The tail is skew and sits in the bottom singular block (record R11); it carries little weight in $q$ and in the profile.
- **Every mathematical claim of the answer is checked in Lean (R20).** Keep it that way: a new mathematical claim in the answer needs a Lean theorem before it ships; empirical claims must be labelled as measurements.
