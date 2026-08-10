# Language Generation in the Limit: A Lean Library and Paper Map

This repository develops a Lean 4 library and a paper-centered research map for
**language generation in the limit**. This framework was introduced
by Jon Kleinberg and Sendhil Mullainathan [KM 24]. In this model, an adversary
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

The modern identifiers follow stable first-appearance order in the
[Language Generation reading list](https://languagegeneration.github.io/):
`#01`--`#36` retain the repository's working-inventory numbers, and later
additions continue the sequence. Gold's foundational paper is listed as `#0`.

| Paper or dependency | Formalized in Lean |
|---|---|
| **#0 — [Language Identification](https://doi.org/10.1016/S0019-9958(67)91165-5) [G 67]** | [Semantic identification model](GenLimitLean/GenLimit/Gold/Text/Model.lean#L33); [Theorem 7.1](GenLimitLean/GenLimit/Gold/Abstract/Enumeration.lean#L290); [finite-language learning](GenLimitLean/GenLimit/Gold/Text/Finite.lean#L120); [locking](GenLimitLean/GenLimit/Gold/Text/Locking.lean#L373) and [finite tell-tales](GenLimitLean/GenLimit/Gold/Text/Superfinite.lean#L123); the [Section 8 finite/superfinite boundary](GenLimitLean/GenLimit/Gold/Text/Superfinite.lean#L229); and [complete-informant enumeration](GenLimitLean/GenLimit/Gold/Informant/Enumeration.lean#L180). |
| **#01 — [Language Generation](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) [KM 24]** | [Section 4 semantic construction](GenLimitLean/GenLimit/KM/Semantic.lean#L113); [literal finite-set interface](GenLimitLean/GenLimit/KM/SetInterface.lean#L217); and [Theorem 2.1 (NeurIPS proceedings)](GenLimitLean/GenLimit/KM/FiniteQuery/Main.lean#L60) and [Theorem 2.1 (arXiv v1)](GenLimitLean/GenLimit/KM/FiniteQuery/ArxivV1.lean#L307). |
| **#02 — [Learning Theory](https://arxiv.org/abs/2410.13714v5) [LRT 25]** | [Theorem 2.4](GenLimitLean/GenLimit/LiRamanTewari.lean#L34); [Theorem 3.3](GenLimitLean/GenLimit/LiRamanTewari/Closure.lean#L258) and its [sample-complexity bounds](GenLimitLean/GenLimit/LiRamanTewari/UniformSampleComplexity.lean#L281); [Theorem 3.5](GenLimitLean/GenLimit/LiRamanTewari/NonuniformCharacterization.lean#L160); [Theorem 3.10](GenLimitLean/GenLimit/LiRamanTewari/GenerationInLimitCharacterization.lean#L518); prompted [Theorem 5.1](GenLimitLean/GenLimit/LiRamanTewari/PromptedClosure.lean#L486) and [Theorem 5.2](GenLimitLean/GenLimit/LiRamanTewari/PromptedNonuniform.lean#L183); hierarchy-separation [Lemmas 3.4](GenLimitLean/GenLimit/LiRamanTewari/EarlierSectionThreeExamples.lean#L93), [3.9](GenLimitLean/GenLimit/LiRamanTewari/EarlierSectionThreeExamples.lean#L184), [3.12](GenLimitLean/GenLimit/LiRamanTewari/LimitVsNonuniformSeparation.lean#L452), [4.2](GenLimitLean/GenLimit/LiRamanTewari/LimitVsNonuniformSeparation.lean#L469), and [4.3](GenLimitLean/GenLimit/LiRamanTewari/CountableUnionSeparation.lean#L607); [Theorem 4.1's VC/Littlestone combinatorial core](GenLimitLean/GenLimit/LiRamanTewari/Prediction.lean#L1248); and Appendix [Theorem C.2](GenLimitLean/GenLimit/LiRamanTewari/FiniteEUCUnion.lean#L637) and [Theorem C.4](GenLimitLean/GenLimit/LiRamanTewari/EventuallyUnboundedClosure.lean#L275). |
| **#06 — [Noisy Examples](https://proceedings.mlr.press/v267/raman25a.html) [RR 25]** | Every paper-owned numbered definition and valid qualitative result, including [Theorem 3.1](GenLimitLean/GenLimit/NoisyExamples/UniformIndependent.lean#L306), [Theorem 3.3](GenLimitLean/GenLimit/NoisyExamples/NoisyClosure.lean#L625), [Theorem 3.9](GenLimitLean/GenLimit/NoisyExamples/NoiselessRobustification.lean#L740), [Theorem 3.10](GenLimitLean/GenLimit/NoisyExamples/FiniteUnionLimit.lean#L218), Appendix [Lemma C.2](GenLimitLean/GenLimit/NoisyExamples/AlternatePositive.lean#L343), [Theorem C.3](GenLimitLean/GenLimit/NoisyExamples/AlternatePositive.lean#L327), and [Lemma D.2](GenLimitLean/GenLimit/NoisyExamples/NonuniformIndependent.lean#L245). |
| **#08 — [Hallucination Detection](https://arxiv.org/abs/2504.17004v2) [KMSV 25]** | [Theorem 2.1](GenLimitLean/GenLimit/HallucinationDetection/Reductions.lean#L229), [Corollary 2.2](GenLimitLean/GenLimit/HallucinationDetection/AngluinCondition.lean#L193), [Theorem 2.3](GenLimitLean/GenLimit/HallucinationDetection/NegativeExamples.lean#L58), [Theorem A.1](GenLimitLean/GenLimit/HallucinationDetection/Appendix.lean#L99), and [Theorem A.2](GenLimitLean/GenLimit/Bridges/LiRamanTewariToHallucinationDetection.lean#L19); Lean also [corrects the false Example 1 inference](GenLimitLean/GenLimit/HallucinationDetection/ExampleOne.lean). |
| **#28 — [Contrastive Generation](https://arxiv.org/abs/2605.06211v1) [LHJG 26]** | [Theorem 4.7](GenLimitLean/GenLimit/ContrastiveGeneration/IdentifierCharacterization.lean#L641); [Theorem 5.4](GenLimitLean/GenLimit/ContrastiveGeneration/ClosureDimension.lean#L432); [Theorem 5.5](GenLimitLean/GenLimit/ContrastiveGeneration/NonuniformClosure.lean#L265); [core criteria](GenLimitLean/GenLimit/ContrastiveGeneration/GenerationCores.lean) and [Theorems 5.13–5.14 punctured](GenLimitLean/GenLimit/ContrastiveGeneration/Hierarchy.lean#L329) and [disjoint witnesses](GenLimitLean/GenLimit/ContrastiveGeneration/DisjointHierarchy.lean#L174); [Theorem 6.5](GenLimitLean/GenLimit/ContrastiveGeneration/CorruptedPresentations.lean#L111); [Theorem 6.6](GenLimitLean/GenLimit/ContrastiveGeneration/AbsenceCount.lean#L477); [Theorem 6.8](GenLimitLean/GenLimit/ContrastiveGeneration/CorruptedIncomparability.lean#L505); and [Proposition 6.3](GenLimitLean/GenLimit/ContrastiveGeneration/DefectInfimum.lean#L467). |
| **#31 — [Bounded Memory](https://arxiv.org/abs/2605.30324v1) [KMSV 26]** | [Theorem 1.1](GenLimitLean/GenLimit/BoundedMemory/FinitelyRepeating.lean#L273); [Theorem 3.1](GenLimitLean/GenLimit/BoundedMemory/ArbitraryRepetitions.lean#L149); [Theorem 3.2](GenLimitLean/GenLimit/BoundedMemory/OutputSeparations.lean#L584); order-robust [Theorem 4.1](GenLimitLean/GenLimit/BoundedMemory/MinimaxClosure.lean#L233), [Theorem 4.2](GenLimitLean/GenLimit/BoundedMemory/MinimaxClosure.lean#L416), [Theorem 4.10](GenLimitLean/GenLimit/BoundedMemory/WindowHardInstance.lean#L1137), and [Theorem 4.15](GenLimitLean/GenLimit/BoundedMemory/AdaptiveBuffer.lean#L1102); [Proposition 5.1](GenLimitLean/GenLimit/BoundedMemory/ExactIdentificationObstruction.lean#L347) and [Theorem 5.2](GenLimitLean/GenLimit/BoundedMemory/IncrementalIdentification.lean#L546); Appendix [Theorem A.1](GenLimitLean/GenLimit/BoundedMemory/IncrementalIndexObstruction.lean#L659), [Proposition A.2](GenLimitLean/GenLimit/BoundedMemory/IncrementalIndexObstruction.lean#L292), and [Lemma A.3 plus element coding](GenLimitLean/GenLimit/BoundedMemory/IncrementalElementCoding.lean#L313). |
| **#39 — [Dense Generation](https://arxiv.org/abs/2608.01320v1) [CLSWZ 26]** | **Earlier manuscript only; arXiv v1 is not yet formalized.** The Lean files use [recursive criticality](GenLimitLean/GenLimit/DenseGeneration/Critical.lean#L19), whereas public v1 Definition 3.2 compares against every earlier consistent language. For the earlier manuscript, Lean covers the [patient-scope construction](GenLimitLean/GenLimit/DenseGeneration/Patient/Machine.lean), [Lemma 3.11](GenLimitLean/GenLimit/DenseGeneration/Patient/Validity.lean#L233), [Theorem 3.14](GenLimitLean/GenLimit/DenseGeneration/Patient/Main.lean#L36), [Example 3.15](GenLimitLean/GenLimit/DenseGeneration/Partial/Counterexample.lean#L248), [Lemma 3.16](GenLimitLean/GenLimit/DenseGeneration/Partial/Validity.lean#L47), and [Theorem 3.17](GenLimitLean/GenLimit/DenseGeneration/Partial/Main.lean#L63). The last three are numbered Example 3.17, Lemma 3.18, and Theorem 3.19 in arXiv v1. |

Kleinberg and Wei introduced density measures for language generation [KW 25]
and later proved that `1 / 2` is the tight deterministic lower-density bound
[KW 26]. DenseGeneration gives a simpler patient-scope construction achieving
the same guarantee. In the partial-enumeration setting, Kleinberg and Wei were
also the first to establish the optimal guarantee: if the enumerated subset
has relative lower density `α` in the target, the optimal guarantee is
`α / 2` [KW 26].

The [KM paper map](GenLimitLean/PaperMaps/KM.md),
[Li--Raman--Tewari paper map](GenLimitLean/PaperMaps/LiRamanTewari.md),
[Raman--Raman paper map](GenLimitLean/PaperMaps/NoisyExamples.md),
[hallucination-detection paper map](GenLimitLean/PaperMaps/HallucinationDetection.md),
[contrastive-generation paper map](GenLimitLean/PaperMaps/ContrastiveGeneration.md),
[bounded-memory paper map](GenLimitLean/PaperMaps/BoundedMemory.md), and
[DenseGeneration paper map](GenLimitLean/PaperMaps/DenseGeneration.md) record
the intended paper-to-Lean correspondence, current audit status, and
formalization boundaries.

The [Gold paper map](GenLimitLean/PaperMaps/Gold.md) records the corresponding
semantic/effective boundary and the current Gold audit scope.

The formalization is deliberately modular. The KM development separates
whole-language semantics, the observed-set interface, shared finite-critical
selection, and the two source-version-specific finite-query machines.
The Li--Raman--Tewari path is split into ordinary generation, prediction,
prompted generation, examples, and Appendix C modules so each boundary remains
reviewable. The Raman--Raman noisy-generation development depends only on
neutral generic Core vocabulary, not on the substantive LRT theorem layer.
The hallucination-detection development imports the sibling
[`GenLimit.Angluin`](GenLimitLean/PaperMaps/Angluin.md) identification layer.
Its native results remain independent of substantive LRT theorems; the one
LRT-dependent Appendix A.2 result is isolated in an explicit bridge.
The contrastive-generation development likewise uses the neutral generic Core
and the semantic necessity theorem in the Angluin sibling. It imports neither
the LRT paper development nor the hallucination-detection development. The
paper-independent identification-to-fresh-generation argument is owned by
`GenLimit.Core.IdentificationGeneration` and reused through a thin Paper 28
wrapper.
The bounded-memory development imports only neutral Core and Mathlib modules:
generic presentation vocabulary comes from `GenLimit.Core.GenericGeneration`,
and the Kleinberg--Wei ordered-density interface is housed in
`GenLimit.Core.OrderedDensity`. It imports no sibling paper or bridge.

## Repository guide

- `GenLimitLean/GenLimit/Core/` contains paper-independent definitions and
  semantic lemmas.
- `GenLimitLean/GenLimit/Gold/` contains Gold's abstract, arbitrary-text, and
  informant semantic developments.
- `GenLimitLean/GenLimit/LiRamanTewari/` contains ordinary and prompted
  generation theory, prediction-dimension proxies, and Appendix C EUC results.
- `GenLimitLean/GenLimit/NoisyExamples/` contains the uniform, non-uniform,
  robustification, separation, and appendix results for noisy examples.
- `GenLimitLean/GenLimit/Angluin/` contains semantic identification,
  finite-tell-tale, and separately marked effective interfaces.
- `GenLimitLean/GenLimit/HallucinationDetection/` contains Paper 08's native
  detector, reduction, Example 1, negative-example, and appendix results.
- `GenLimitLean/GenLimit/ContrastiveGeneration/` contains Paper 28's geometry,
  identification, closure, hierarchy, corruption, and defect developments.
- `GenLimitLean/GenLimit/BoundedMemory/` contains Paper 31's memoryless,
  density, sliding-window, adaptive-buffer, incremental-identification, and
  appendix developments.
- `GenLimitLean/GenLimit/KM/` contains the KM semantic and finite-query paths.
- `GenLimitLean/GenLimit/DenseGeneration/` contains the patient-scope and
  partial-enumeration developments.
- `GenLimitLean/GenLimit/DenseGeneration/Partial/` contains the Section 3.3
  counterexample and partial-enumeration proof.
- `GenLimitLean/GenLimit/Bridges/` contains explicit cross-paper comparisons.
- [`GenLimitLean/PAPER_MAP.md`](GenLimitLean/PAPER_MAP.md) is the paper
  registry; detailed maps are under
  [`GenLimitLean/PaperMaps/`](GenLimitLean/PaperMaps/).
- [`GenLimitLean/AuditRecords/`](GenLimitLean/AuditRecords/) preserves
  checksum-verified ChatGPT Pro statement-faithfulness evidence one paper at a
  time, separately from named human audits.

## Verification and audit

The current Lean formalizations combine AI-assisted code generation, Lean
kernel checking, AI-assisted source comparison, and named human audit. These
are separate forms of evidence. `GPT-5.6-sol ultra` generated the code under
human direction, while Lean's kernel checks that the formal proofs establish
their stated results. Where performed, human reviewers assess selected
paper-to-Lean translations; each audit records its scope, interpretation
choices, and exclusions.

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
paper's intermediate proof is correct. Peng Zhang's recorded human checks
cover the KM semantic development at Level 3, the stated Dense Generation
exact- and partial-enumeration paths against the earlier supplied manuscript at
Level 2, and the shared Core plus Gold Text path at Level 2.

At the maintainer's direction, ChatGPT Pro performed six two-stage,
source-pinned statement-faithfulness checks. Stage 1 reconstructed the
mathematical interface from Lean declaration signatures and
statement-relevant definition bodies while withholding the papers and
excluding comments and proof bodies as mathematical evidence. Stage 2 compared
that reconstruction with the pinned author sources, checking objects and
types, binder and quantifier order, hypotheses,
representation and indexing, presentation/access/output interfaces, theorem
coverage and witness-link assembly, strength or weakening, vacuity and edge
cases, and omitted claims.

| Development | ChatGPT Pro check | Human status |
|---|---|---|
| #01 added paths | Observed-set interface and both finite-query Theorem 2.1 paths, against the NeurIPS proceedings and arXiv v1 | Peng's Level 3 record covers only the semantic path; human review of the added paths is pending |
| #02 Learning Theory | Ordinary and prompted generation, sample-complexity interfaces, hierarchy results, Appendix C, and the Theorem 4.1 combinatorial boundary, against arXiv v5 | Pending |
| #06 Noisy Examples | All paper-owned qualitative statements, exposed assumptions and source repairs, and quantitative exclusions, against arXiv v2 | Pending |
| #08 Hallucination Detection | Detection/identification reductions, tell-tale and negative-example results, Appendix results, Example 1, and oracle/effectivity boundaries, against arXiv v2 | Pending |
| #28 Contrastive Generation | Deterministic statements, hierarchy and robustness coverage, and the Theorem 6.6 witness interface, against the arXiv-v1 pre-repair baseline | Pending; the named-witness repair is kernel-checked separately |
| #31 Bounded Memory | Deterministic statements, universe/order/output/indexing boundaries, and Appendix Lemma A.3, against the arXiv-v1 pre-repair baseline | Pending; the Lemma A.3 wrapper repair is kernel-checked separately |

These ChatGPT Pro checks did not audit theorem proof-body correctness,
establish proof correspondence, rerun Lean, certify the papers' mathematics,
or constitute a human audit. The uniform records, evidence links, and remaining human-review
slots are in [`GenLimitLean/HUMAN_AUDIT.md`](GenLimitLean/HUMAN_AUDIT.md) and
[`GenLimitLean/AuditRecords/`](GenLimitLean/AuditRecords/); kernel and axiom
checks are in [`GenLimitLean/AUDIT.md`](GenLimitLean/AUDIT.md).

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

- **#0 — [Language Identification in the Limit](https://doi.org/10.1016/S0019-9958(67)91165-5) [G 67].**
  E. Mark Gold. *Information and Control* 10(5), pp. 447–474, 1967.

- **#01 — [Language Generation in the Limit](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) [KM 24].**
  Jon Kleinberg and Sendhil Mullainathan. *Advances in Neural Information
  Processing Systems 37 (NeurIPS 2024)*, 2024.
  [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) ·
  [arXiv](https://arxiv.org/abs/2404.06757) ·
  [DOI](https://doi.org/10.52202/079017-2111).

- **#02 — [Generation through the Lens of Learning Theory](https://arxiv.org/abs/2410.13714v5) [LRT 25].**
  Jiaxun Li, Vinod Raman, and Ambuj Tewari. *Proceedings of the 38th Conference
  on Learning Theory (COLT 2025)*, PMLR 291, pp. 4740--4776, 2025.
  [arXiv v5](https://arxiv.org/abs/2410.13714v5).

- **#06 — [Generation from Noisy Examples](https://proceedings.mlr.press/v267/raman25a.html) [RR 25].**
  Ananth Raman and Vinod Raman. *Proceedings of the 42nd International
  Conference on Machine Learning (ICML 2025)*, PMLR 267, pp. 51079--51093,
  2025.
  [Proceedings](https://proceedings.mlr.press/v267/raman25a.html) ·
  [arXiv v2](https://arxiv.org/abs/2501.04179v2).

- **#08 — [(Im)possibility of Automated Hallucination Detection in Large Language Models](https://arxiv.org/abs/2504.17004v2) [KMSV 25].**
  Amin Karbasi, Omar Montasser, John Sous, and Grigoris Velegkas.
  arXiv:2504.17004v2, 2025.
  [arXiv v2](https://arxiv.org/abs/2504.17004v2).

- **#28 — [Contrastive Identification and Generation in the Limit](https://arxiv.org/abs/2605.06211v1) [LHJG 26].**
  Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao.
  arXiv:2605.06211v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.06211v1).

- **#31 — [On Language Generation in the Limit with Bounded Memory](https://arxiv.org/abs/2605.30324v1) [KMSV 26].**
  Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas.
  arXiv:2605.30324v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.30324v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.30324).

- **Classical — [Inductive Inference from Positive Data](https://doi.org/10.1016/S0019-9958(80)90285-5) [A 80].**
  Dana Angluin. *Information and Control* 45(2), pp. 117--135, 1980.

- **#07 — [Density Measures for Language Generation](https://arxiv.org/abs/2504.14370) [KW 25].**
  Jon Kleinberg and Fan Wei. *Proceedings of the 66th IEEE Symposium on
  Foundations of Computer Science (FOCS 2025)*, pp. 620--658, 2025.
  [arXiv](https://arxiv.org/abs/2504.14370) ·
  [DOI](https://doi.org/10.1109/FOCS63196.2025.00034).

- **#15 — [Partial Enumeration](https://arxiv.org/abs/2511.05295) [KW 26].**
  Jon Kleinberg and Fan Wei. "Language Generation and Identification From
  Partial Enumeration: Tight Density Bounds and Topological
  Characterizations." *Proceedings of the 58th Annual ACM Symposium on Theory
  of Computing (STOC 2026)*, 2026.
  [arXiv](https://arxiv.org/abs/2511.05295) ·
  [STOC accepted paper](https://acm-stoc.org/stoc2026/accepted-papers.html).

- **#39 — [Dense Language Generation Made Simple](https://arxiv.org/abs/2608.01320v1) [CLSWZ 26].**
  Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng Zhang.
  "Dense Language Generation Made Simple: Deterministic, Randomized, and
  Multi-Order Algorithms." arXiv:2608.01320v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2608.01320v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2608.01320).

Bibliographic entries for the source papers are collected in
[`GenLimitLean/CITATION.bib`](GenLimitLean/CITATION.bib).

## License

The repository is licensed under the [Apache License 2.0](LICENSE).
