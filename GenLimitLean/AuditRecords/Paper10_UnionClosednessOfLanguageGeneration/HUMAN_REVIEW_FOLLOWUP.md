# P10 Theorem 3.3: clarification after human review

Reported by Peng Zhang on 12 November 2026, after human review of the LLM
audit finding, against the `work/non-p38` formalization.

> This should not be classified as a missing condition in the formalization.
> The infinite-language requirement is proved separately immediately below
> `theorem_3_3`, for the same named witness used in that theorem. This is a
> writing and presentation issue. The property should nevertheless be
> included directly in the statement of `theorem_3_3`.

The declaration `GenLimit.UnionClosedness.theorem_3_3` uses
`finiteNegativeInfinitePositiveClass` as its witness. Immediately afterward,
`GenLimit.UnionClosedness.theorem_3_3_witness_uus` proves
`UUS finiteNegativeInfinitePositiveClass`, establishing that every member
of that same class is infinite. Both declarations are in
`GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean`.

The infinitude requirement comes from the paper's standing convention in
the preliminaries and Remark 2.2; it is not repeated explicitly in the
displayed Theorem 3.3. The formalization already establishes this property
for its actual witness. The standalone existential statement does not yet
bundle it with the other conclusions, so a reader using only that statement
does not obtain the full specification at one entry point.

After human review, the classification is therefore **a presentation issue,
not a missing mathematical condition or proof in the formalization**. The
recommended writing improvement is to include `UUS H` in the existential
conclusion of `theorem_3_3`, using the already proved property of the same
witness. This note does not claim that the statement has already been changed.

This is an English rendering of the maintainer's human-review clarification,
not a new LLM audit or a proof-body audit. It qualifies the earlier LLM
description of this item as a missing condition. The original two-stage
reports, adjudication, and checksum manifests are retained unchanged as
historical evidence. This follow-up is a separate local, non-Git-tracked file.
