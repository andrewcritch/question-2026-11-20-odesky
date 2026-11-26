# Role prompt: check that the Lean formalization faithfully represents the answer

Hi! Thanks for helping. Other delegate agents check this same material in parallel. Answer by yourself; do not wait for them or coordinate with them.

A clear negative report has value; an overstated positive report has none.

## Files (absolute paths)

- The answer: `/Users/andrew/maisi/questions/2026-11-20-odesky/answer_draft.md`. Its §6 table names, for each mathematical claim, the Lean theorems that check it.
- The question the answer responds to: `/Users/andrew/maisi/questions/2026-11-20-odesky/question.md` (defines $S$, $T$, $\lambda_\pm$, $\sigma(T)$, the profile $(a,b,c,d)$, $\Theta$, and relations (1) and (2)).
- The Lean project: `/Users/andrew/maisi/questions/2026-11-20-odesky/lean/OdeskyLean/*.lean` (Lean 4, Mathlib). Every file builds with no `sorry`.

## Task

Lean checks proofs, not statements. Your job is to check the statements. For each mathematical claim in §1, §2, §3 and §7 of the answer:

1. Find the Lean theorem or theorems that the answer says check it.
2. Read each Lean statement, and every definition it uses, beside the claim in the answer. Check:
   - that each Lean definition (profile, spectral lists, Frobenius norms, tilts, similar ordering, normal form, the ensemble, the limits) means what the answer means by the same word;
   - the quantifiers and their order, and what is fixed or random;
   - every hypothesis: a Lean hypothesis that the answer does not state narrows the claim, and a claim stronger than its Lean theorem is unchecked;
   - that the Lean theorems together reach the claim as the answer states it, with no unformalized step between them.
3. Also report any mathematical claim in the answer that no Lean theorem covers, and any statement in §6 about what Lean checks that is inaccurate.

Do not edit any file. For each finding, give: the claim (answer line or quoted text), the Lean theorem (file and name), what differs, and how serious it is (the claim is wrong; the claim is unchecked as stated; a harmless difference). Where a claim and its Lean theorem match, say so briefly, and name the claim you checked hardest.

You have **30 minutes**. At that point, stop and write what you have, with `INTERRUPTED PARTIAL` as the first line.

Write your answer to `./answer.md` in your working directory, and lead with a one-line verdict.
