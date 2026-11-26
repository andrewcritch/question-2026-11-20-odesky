# Round 2 role prompt: construct one ensemble

Hi! Thanks for helping with this. Other delegate agents work on this same problem in parallel. Answer by yourself; do not wait for them or coordinate with them.

A clear negative report has value; an overstated positive report has none.

## Goal

The project goal is to give an affirmative answer to a MaisiOverflow question: find one natural random-matrix ensemble of query/key pairs $(Q,K)$, $Q,K\in\mathbb R^{n\times N}$, for which relations (1) and (2) of the question hold in the way trained attention heads show them. Your role in this delegation round: **construct one ensemble, with few parameters per head, that covers all trained GPT-2 heads, and test it against the weights.**

## Files (absolute paths)

- Question: `/Users/andrew/maisi/questions/2026-11-20-odesky/question.md`
- Project record, with every checked result so far (R1–R8): `/Users/andrew/maisi/questions/2026-11-20-odesky/record.md`. Read it in full. Treat R1, R2, R4, and R5 as givens; they have proofs there.
- Settled constraints: `/Users/andrew/maisi/questions/2026-11-20-odesky/MM-notes.md`
- Round-1 answers from four delegate agents, with their scripts: `/Users/andrew/maisi/questions/2026-11-20-odesky/delegations/answers/round1/` (`codex.md`, `claude.md`, `grok.md`, and the `*_scripts/` folders). Reuse their code where it helps.
- Round-1 brief, statistics script, and per-head CSV: `/Users/andrew/maisi/questions/2026-11-20-odesky/delegations/round1_brief/`
- GPT-2 small weights: `/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors`. In `h.{l}.attn.c_attn.weight` (768×2304), head $h$ has $Q=W[:,64h:64h+64]^\top$ and $K=W[:,768+64h:768+64h+64]^\top$; $L=K^\top Q$.
- Python with numpy, scipy, and safetensors: `/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/venv/bin/python`. Run it with `-I`.

## What round 1 established (details and checks are in the record)

- Every diagonal-$W$ model has $a\le b$ (R4), and the Claude node's candidate A (R7) also has $a\le b$. 44 of 144 raw heads have $a>b$, and $a-b$ tracks the complex-eigenvalue mass of $L$ (R6).
- Candidate A, fitted on the 100 heads with $a<b$, predicts the relation-(1) error with correlation 0.96 across heads, but at about two thirds of the measured level. Diagonal-plus-Gaussian-noise models (Codex candidate 2, Grok candidate 1) show the same shortfall.
- The missing part of the relation-(1) error sits in a few large, preferentially symmetric off-diagonal pairs of $W$; off-diagonal kurtosis is about 20 (R8).
- The structure lives in the head-space pairing of query and key rows (R7, "headrot" null).

## What to do

1. Construct one ensemble that covers heads with $a<b$ and heads with $a>b$ with the same recipe, for example by a parameter whose sign or size moves a head across $a=b$. Give it precisely, as a sampling recipe for $Q,K$, with its parameter count per head and any global constants.
2. Say which mechanism in your ensemble produces (i) $a>b$, (ii) the full level of the relation-(1) error, and (iii) the heavy-tailed, symmetric-leaning large off-diagonal pairs of $W$. Derive what you can; label heuristics as heuristics.
3. Fit it per head on all 144 raw GPT-2 heads, using only some statistics, and predict the others. Report fitted versus predicted statistics separately: medians, 10th/90th percentiles, and correlations across heads. Include at least: relation-(1) error, $a-b$, $c-d$, $\min(c,d)$, diagonal share of $W$, off-diagonal RMS and kurtosis of $W$, and the participation ratio.
4. State what would falsify the ensemble, and which heads it fits worst.

## Bounds

You have **40 minutes**. At that point, stop work and write whatever you have, with `INTERRUPTED PARTIAL` as the first line and a note on what you had not yet checked. Keep the answer under roughly 2,000 lines.

Run every command that may take more than a few minutes, or that starts several worker processes, through `heavy-run`: `heavy-run --workers 8 --label <short name> -- <command>`. It runs one heavy job on this machine at a time, and it sets `HEAVY_MAX_WORKERS` to 8. Size every process pool from `HEAVY_MAX_WORKERS`, and replace each worker after each task (`multiprocessing.Pool(processes=n, maxtasksperchild=1)`), so that memory does not accumulate across tasks. The machine's memory guard halts any job that grows too large; `mem-guard log` names the job and the reason.

Do not modify any file under `/Users/andrew/maisi/questions/2026-11-20-odesky/`. Write your answer to `./answer.md` in your working directory, and put your scripts there too, unless this prompt gives you a different answer path.
