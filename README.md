# Language Generation in the Limit: A Lean Library and Paper Map

This repository develops a Lean 4 library and a paper-centered research map for
**language generation in the limit**, a framework first introduced by Jon
Kleinberg and Sendhil Mullainathan [KM24]. In this model, an adversary chooses
an unknown target language from a countable family and enumerates its elements
in an arbitrary order. A generator observes this growing stream and must,
after some finite time, output only elements of the target language that have
not yet appeared in the stream.

The project focuses on this one active research direction and studies it in
depth. It aligns definitions and assumptions across papers, records
relationships and proof dependencies among results, identifies reusable proof
ideas, and documents open questions and gaps.

The long-term goal is to support an open-source research community in this
area by helping researchers learn and extend the theory. The repository also
aims to provide focused infrastructure for AI-for-mathematics research on
paper understanding, conjecture generation, theorem proving, paper-to-Lean
translation, and human–AI auditing.

## Current scope

| Development | Formalized | Outside the current scope |
|---|---|---|
| **KM [KM24]** | Theorem 2.1 via a short semantic construction based on Section 4 and the finite-query algorithm from Section 5 of the NeurIPS proceedings | The later arXiv finite-query variant |
| **DenseGeneration [Dense26]** | The semantic patient-scope construction proving target-relative lower density at least `1 / 2`, including Lemma 3.11, Fact 3.12, Lemma 3.13, and Theorem 3.14 | A finite-query implementation and the separate optimality upper bound |

Kleinberg and Wei introduced density measures for language generation [KW25]
and later proved that `1 / 2` is the tight deterministic lower-density bound
[KW26]. DenseGeneration gives a simpler patient-scope construction achieving
the same guarantee.

The [KM paper map](GenLimitLean/PaperMaps/KM.md) and
[DenseGeneration paper map](GenLimitLean/PaperMaps/DenseGeneration.md) record
the intended paper-to-Lean correspondence, current audit status, and
formalization boundaries.

## Repository guide

- `GenLimitLean/GenLimit/Core/` contains paper-independent definitions and
  semantic lemmas.
- `GenLimitLean/GenLimit/KM/` and
  `GenLimitLean/GenLimit/DenseGeneration/` contain the two paper developments.
- `GenLimitLean/GenLimit/Bridges/` contains explicit cross-paper comparisons.
- [`GenLimitLean/PAPER_MAP.md`](GenLimitLean/PAPER_MAP.md) is the paper
  registry; detailed maps are under
  [`GenLimitLean/PaperMaps/`](GenLimitLean/PaperMaps/).

## Verification and audit

The current Lean formalizations combine AI-assisted code generation with
human audit. `GPT-5.6-sol ultra` generated the code under human direction.
Lean's kernel checks that the formal proofs establish their stated results.
Where performed, human audits check that the formalized statements,
definitions, and algorithms faithfully represent the source papers; the scope
of each audit is documented.

The KM semantic theorem and construction correspondence have been
human-audited, excluding line-by-line proof correspondence and the finite-query
path. The DenseGeneration audit currently covers its black-box input/output
specification. See
[`GenLimitLean/AUDIT.md`](GenLimitLean/AUDIT.md) and
[`GenLimitLean/HUMAN_AUDIT.md`](GenLimitLean/HUMAN_AUDIT.md).

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

Each development should record its source and version, formalized results,
assumptions, Lean entry points, dependencies, audit status, and known gaps.
AI-assisted contributions should remain reviewable, with clear human
responsibility for their mathematical meaning.

## References and citation

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

Bibliographic entries are collected in
[`GenLimitLean/CITATION.bib`](GenLimitLean/CITATION.bib).

## License

The repository is licensed under the [Apache License 2.0](LICENSE).
