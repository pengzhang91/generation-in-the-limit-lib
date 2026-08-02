# Language Generation in the Limit: A Lean Library and Paper Map

This repository develops a Lean 4 library and a paper-centered research map for
**language generation in the limit**. This framework was introduced
by Jon Kleinberg and Sendhil Mullainathan [KM24]. In this model, an adversary
chooses an unknown infinite target language from a countable indexed family of
infinite languages and presents its elements in an arbitrary stream.
A generator observes this growing stream and must, after some finite time,
output only elements of the target language that have not yet appeared in the
stream.

The project focuses on this one active research direction and studies it in
depth. It aligns definitions and assumptions across papers, records
relationships and proof dependencies among results, identifies reusable proof
ideas, and documents open questions and gaps.

The long-term goal is to support an open-source research community in this
area by helping researchers learn and extend the theory. The repository also
aims to provide focused infrastructure for AI4Math research on
paper understanding, conjecture generation, theorem proving, and paper-to-Lean translation.

## Current scope

| Development | Formalized | Outside the current scope |
|---|---|---|
| **Gold [Gold67]** | The semantic identification model; all three clauses of Theorem 7.1; finite-language learning from arbitrary positive text; locking and finite tell-tales; the Section 8 finite/superfinite boundary; complete-informant enumeration | Turing-machine tester and generator names, effective learners, recursive and primitive-recursive texts, and the effectiveness-specific Appendix I results including I.8 and I.9 |
| **KM [KM24]** | The round-indexed and literal finite-set Section 4 constructions, plus Theorem 2.1 via both the NeurIPS proceedings and arXiv-v1 finite-query algorithms | Finite-family Theorem 2.2, prompted generation, arbitrary-countable-universe transport, and pairwise-distinct generated outputs |
| **DenseGeneration [Dense26]** | The semantic patient-scope construction for exact presentation (Lemma 3.11 through Theorem 3.14), the counterexample in Example 3.15, and partial enumeration (Lemma 3.16 and Theorem 3.17) | The randomized and multi-order developments, a finite-query implementation, and the separate optimality upper bound |

Kleinberg and Wei introduced density measures for language generation [KW25]
and later proved that `1 / 2` is the tight deterministic lower-density bound
[KW26]. DenseGeneration gives a simpler patient-scope construction achieving
the same guarantee. In the partial-enumeration setting, Kleinberg and Wei were
also the first to establish the optimal guarantee: if the enumerated subset
has relative lower density `α` in the target, the optimal guarantee is
`α / 2` [KW26].

The [KM paper map](GenLimitLean/PaperMaps/KM.md) and
[DenseGeneration paper map](GenLimitLean/PaperMaps/DenseGeneration.md) record
the intended paper-to-Lean correspondence, current audit status, and
formalization boundaries.

The [Gold paper map](GenLimitLean/PaperMaps/Gold.md) records the corresponding
semantic/effective boundary and the current Gold audit scope.

The formalization is deliberately modular. The KM development separates
whole-language semantics, the observed-set interface, shared finite-critical
selection, and the two source-version-specific finite-query machines.
The current deterministic and partial-enumeration DenseGeneration development
occupies 4,588 lines. The Gold semantic development
occupies 1,574 lines. The shared `GenLimit.Core` occupies 259 lines. These
figures exclude blank lines and comments.

## Repository guide

- `GenLimitLean/GenLimit/Core/` contains paper-independent definitions and
  semantic lemmas.
- `GenLimitLean/GenLimit/Gold/` contains Gold's abstract, arbitrary-text, and
  informant semantic developments.
- `GenLimitLean/GenLimit/KM/` and
  `GenLimitLean/GenLimit/DenseGeneration/` contain the two paper developments.
- `GenLimitLean/GenLimit/DenseGeneration/Partial/` contains the Section 3.3
  counterexample and partial-enumeration proof.
- `GenLimitLean/GenLimit/Bridges/` contains explicit cross-paper comparisons.
- [`GenLimitLean/PAPER_MAP.md`](GenLimitLean/PAPER_MAP.md) is the paper
  registry; detailed maps are under
  [`GenLimitLean/PaperMaps/`](GenLimitLean/PaperMaps/).
- [`GenLimitLean/AuditRecords/`](GenLimitLean/AuditRecords/) preserves
  checksum-verified external review evidence one paper at a time, separately
  from named human audits.

## Verification and audit

The current Lean formalizations combine AI-assisted code generation with
human audit. `GPT-5.6-sol ultra` generated the code under human direction.
Lean's kernel checks that the formal proofs establish their stated results.
Where performed, human reviewers assess selected paper-to-Lean translations;
each audit records its scope, interpretation choices, and exclusions.

We distinguish three cumulative levels of human paper-to-Lean audit:

| Level | Human check |
|---|---|
| **1. Theorem specification** | The main theorem's assumptions, inputs, outputs, and mathematical conclusion match the paper. |
| **2. Algorithm correspondence** | Level 1, plus the paper-facing definitions and the full formal construction or state machine match the paper's algorithm. |
| **3. Proof correspondence** | Level 2, plus the intermediate lemmas, proof dependencies, and manuscript proof steps are checked against their Lean counterparts. |

Lean's kernel verifies the formal proof at every level; these levels describe
only the extent of human verification of the paper-to-Lean translation. A
Level 2 audit, together with kernel verification, establishes that the audited
paper algorithm satisfies the audited main theorem without asserting that the
paper's intermediate proof is correct.

The KM semantic development currently reaches Level 3. The observed-set and
both finite-query paths have an AI-assisted statement comparison and still
await human correspondence review. The DenseGeneration exact-presentation
result and the Section 3.3 Lemma 3.16--Theorem 3.17 path reach Level 2.
Those KM paths and Example 3.15 have not yet received a human paper-to-Lean
audit. See
[`GenLimitLean/AUDIT.md`](GenLimitLean/AUDIT.md) and
[`GenLimitLean/HUMAN_AUDIT.md`](GenLimitLean/HUMAN_AUDIT.md).

For Gold, the shared Core prerequisites and Text have received a human audit
at Level 2, covering the concrete arbitrary-text semantic chain from
the model and finite learner through locking and the superfinite obstruction. Gold's
Abstract Theorem 7.1, text-enumeration, informant, and bridge paths remain
outside that audit.

## Build and reading path

The project pins Lean 4.24.0 and Mathlib 4.24.0.

```bash
cd GenLimitLean
lake exe cache get
lake build
lake env lean Audit.lean
```

GitHub Actions builds the library, runs the axiom audit, and checks for
unfinished proofs. The [Lean package README](GenLimitLean/README.md) provides
the main theorem entry points and module-level reading order.

## Roadmap and contributions

Next steps include adding papers to the map, formalizing new results,
extracting reusable foundations into `GenLimit.Core`, adding comparison
theorems to `GenLimit.Bridges`, improving educational notes, and performing
human correspondence audits.

For Gold, the next audit step is the Abstract Theorem 7.1 path, followed by
the abstract/text specialization, informant, and bridge paths.

Each development should record its source and version, formalized results,
assumptions, Lean entry points, dependencies, audit status, and known gaps.
AI-assisted contributions should remain reviewable, with clear human
responsibility for their mathematical meaning.

## References

- **[Gold67]** E. Mark Gold. "Language Identification in the Limit."
  *Information and Control* 10(5), pp. 447–474, 1967.
  [DOI](https://doi.org/10.1016/S0019-9958(67)91165-5).

- **[KM24]** Jon Kleinberg and Sendhil Mullainathan. "Language Generation in
  the Limit." *Advances in Neural Information Processing Systems 37 (NeurIPS
  2024)*, 2024. [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) ·
  [arXiv](https://arxiv.org/abs/2404.06757) ·
  [DOI](https://doi.org/10.52202/079017-2111).

- **[KW25]** Jon Kleinberg and Fan Wei. "Density Measures for Language
  Generation." *Proceedings of the 66th IEEE Symposium on Foundations of
  Computer Science (FOCS 2025)*, pp. 620-658, 2025.
  [arXiv](https://arxiv.org/abs/2504.14370) ·
  [DOI](https://doi.org/10.1109/FOCS63196.2025.00034).

- **[KW26]** Jon Kleinberg and Fan Wei. "Language Generation and
  Identification From Partial Enumeration: Tight Density Bounds and
  Topological Characterizations." *Proceedings of the 58th Annual ACM
  Symposium on Theory of Computing (STOC 2026)*, 2026.
  [arXiv](https://arxiv.org/abs/2511.05295) ·
  [STOC accepted paper](https://acm-stoc.org/stoc2026/accepted-papers.html).

- **[Dense26]** Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng
  Zhang. "Dense Language Generation Made Simple: Deterministic, Randomized,
  and Multi-Order Algorithms." Manuscript, 2026. See the
  [DenseGeneration paper map](GenLimitLean/PaperMaps/DenseGeneration.md).

Bibliographic entries for the source papers are collected in
[`GenLimitLean/CITATION.bib`](GenLimitLean/CITATION.bib).

## License

The repository is licensed under the [Apache License 2.0](LICENSE).
