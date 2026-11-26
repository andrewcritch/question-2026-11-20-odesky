# Attribution: which agents contributed which ideas

Written 2026-11-24. Sources: the project record (it names a source for most results), the node launch commands, and the node configs.

## Agents and models

| Agent | Model | Delegation rounds |
|---|---|---|
| Supervising agent | Claude Opus 5.5 | all |
| Codex node | gpt-6-astra (high effort, per the node configs) | 1, 2, 3 |
| Claude node | Claude Opus 5.5 (from its transcript; not recorded in the launch) | 1 only; Python was blocked in it, so the supervising agent ran its scripts |
| Claude subagents | opus | 2, 3 |
| Grok node | Grok 4.7 (Grok Build's default; from the node logs, `grok-4.7` / `grok-4.7-build`) | 1, 2, 3 |
| Antigravity node | gemini-4-carbon in round 1 (from the Antigravity log), gemini-4-carbon-high in rounds 2 and 3 | 1, 3; in round 2 its turn ended twice without an answer |

## Ideas, by source

| Idea | Source | Outcome |
|---|---|---|
| Framing: the SVD of $L$, the cosine matrix $W:=U^\top V$, and the "sum of rank-one forms on orthogonal planes" block model with exact relation (1) per block | Supervising agent, before any delegation | The basic language of every later result |
| Exact identity $a=\tfrac12(1-m_2-q)$, $a-b=c+d-m_2-q$; every diagonal-$W$ model has $a\le b$, by the rearrangement inequality | Codex, round 1 | The inequality half of Theorem A(i); also shows that heads with $a>b$ need $q<0$ |
| Determinant identity: relation (1) holds exactly on average in log scale, for every head | Claude node, round 1 | In the answer draft; not in the best-result note |
| Ensemble shape $Q+K=\mathrm{diag}(\cdot)P$, $K-Q=\mathrm{diag}(\cdot)M$ with Gaussian $P,M$ ("candidate A") | Claude node, round 1 | Exactly the form of Definition 6 in the best-result note. Candidate A drew tilt and strength independently, so it is not similarly ordered and gives $a<b$ |
| Tilt coupled monotonically to channel strength ("signed spike") | Antigravity, round 1 | The special case of Definition 6 with $g$ constant; it suggested that monotone coupling matters |
| The off-diagonal part of $W$ is heavy-tailed | Grok, round 1 | Grok read the large pairs as mostly symmetric; the supervising agent found that a random baseline gives the same score, and dropped that reading |
| The heavy tail lies in the weakest singular directions and is antisymmetric | Grok and Codex, round 2 | Recorded; it barely affects the profile |
| Bound on how much $q$ uncorrelated off-diagonal noise can produce | Claude subagent, round 2 | Shows that the extreme layer-0 heads need structured coupling of their top singular directions |
| Finite-$N$ fits that cover both signs of $a-b$ | Codex, Grok, Claude subagent, round 2 | They work, with 3–8 parameters per head; recorded as descriptive fits, not the answer |
| **Theorem A**: $a=b$ exactly when $(\alpha,\beta)$ is similarly ordered; then relation (1) is exact and $c-d$ has a closed form | Supervising agent, after round 2 | Core of the answer; it extends Codex's inequality to an "if and only if", with these consequences |
| **Theorem B**: the ensemble with nondecreasing $f,g$ | Supervising agent, after round 2 | Core of the answer; the Claude node's shape plus Antigravity's monotone coupling, made similarly ordered |
| Two over-broad claims in Theorems A and B (the endpoints of $\Theta$; the position along $\Theta$ depends on the joint law, not on the law of the tilts alone) | Codex, Grok, and the Claude subagent independently, round 3; Antigravity found the same two | Corrected |
| At a fixed ratio $N=\kappa n$, the limit shifts by order $1/\kappa$ | Antigravity, round 3 | The "Order of limits" item of the best-result note |
| Measurements on GPT-2 small, GPT-2 medium and Pythia-160m; the Kendall statistic for similar ordering | Supervising agent | The "Trained heads" item of the best-result note |

## Summary

- Codex gave the most load-bearing algebra: the identity and the sign obstruction.
- The Claude node gave the shape of the ensemble.
- Antigravity gave the monotone-coupling idea and the sharpest round-3 finding, though it sent no answer in round 2.
- Grok led on the off-diagonal structure, which is outside the final answer.
- The Claude subagents gave a useful bound and careful checking.
- The supervising agent did the framing, the synthesis into Theorems A and B, all checking, and the measurements on trained models.

## Caveats

- The record names a source for each result. It does not trace each idea's origin within the delegation round that produced it.
- Delegates in later rounds had read the record, so their findings are not independent of earlier ones.
- The supervising agent's synthesis drew on answers it had read. The Theorem A/B line can fairly be credited jointly to Codex, the Claude node, Antigravity, and the supervising agent.
