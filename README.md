# A random-matrix ensemble for trained attention heads

This repository answers the MaisiOverflow question "Is there a normal form / random matrix model for trained transformers?" (copied in [`question.md`](question.md)), about the paper [arXiv:2609.22990](https://arxiv.org/abs/2609.22990).

## Contents

| Path | Content |
|---|---|
| [`answer_draft.md`](answer_draft.md) | The answer: definitions, Theorem 1 (normal form), Theorem 2 (random ensemble), measurements on trained models, caveats. |
| [`MM-best-result.md`](MM-best-result.md) | A short mathematical note with the same theorems and proof sketches. |
| [`lean/`](lean/) | Lean 4 + Mathlib proofs of Theorems 1 and 2, with no `sorry`. |
| [`record.md`](record.md) | The project record: every result, with where its proof or numerical evidence was checked. |
| [`delegations/round1_brief/`](delegations/round1_brief/) | Python scripts for the measurements on GPT-2, Pythia and BLOOM. |
| [`delegations/answers/`](delegations/answers/) | Reports from the AI delegate agents that worked on the question. |
| [`attribution.md`](attribution.md) | Which agent contributed which idea. |

## Building the Lean proofs

Install [elan](https://github.com/leanprover/elan), then:

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
```

The headline theorems are `Odesky.OrthoBlocks.main_mem_Theta_iff` and its companions in [`lean/OdeskyLean/Main.lean`](lean/OdeskyLean/Main.lean) (Theorem 1), and `Odesky.theoremB_ae` in [`lean/OdeskyLean/TheoremBFull.lean`](lean/OdeskyLean/TheoremBFull.lean) (Theorem 2). `#print axioms` on each gives only `propext`, `Classical.choice` and `Quot.sound`.

## Running the measurements

The scripts take a `model.safetensors` file from Hugging Face as their argument and need `numpy`, `scipy` and `safetensors`. For example, `python delegations/round1_brief/medium.py <path to gpt2-medium model.safetensors>`.
