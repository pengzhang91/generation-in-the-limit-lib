# Language Generation in the Limit: A Lean Library and Paper Map

This repository develops a Lean 4 library and a paper-centered research map for
**language generation in the limit**, a theoretical framework introduced
by Jon Kleinberg and Sendhil Mullainathan [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html).
Motivated by the success of large language models, this framework studies
a fundamental mathematical question about language generation:
when can an algorithm, after observing enough positive examples from an unknown language,
eventually generate new strings that are guaranteed to belong to that language?

The project focuses on this one active research direction and studies it in
depth. It aligns definitions and assumptions across papers, records
relationships and proof dependencies among results, identifies reusable proof
ideas, and documents open questions and gaps.

The long-term goal is to support an open-source research community in this
area by helping researchers learn and extend the theory. The repository also
aims to provide focused infrastructure for AI4Math research on
paper understanding, conjecture generation, theorem proving, and paper-to-Lean translation.

Lean formalization developed and maintained by
[Shuangping Li](https://fifalsp.github.io/) and [Peng Zhang](https://sites.google.com/site/pengzhang27182/).

**Related paper:** Shuangping Li and Peng Zhang.
[GenLimitLib: A Formal Library for Language Generation in the Limit and
AI-Assisted Mathematical Research](https://arxiv.org/abs/2609.36663), arXiv:2609.36663, 2026.

## Current scope

We follow the order in the
[Language Generation reading list](https://languagegeneration.github.io/):
`#01`--`#45`. In addition, we number the two foundational language identification papers:
`#0` for Gold (1967) and `#0A` for Angluin (1980).

| Paper | Formalized in Lean |
|---|---|
| **#0&nbsp;—&nbsp;Language&nbsp;Identification** [\[G 67\]](https://doi.org/10.1016/S0019-9958(67)91165-5) | Theorem 7.1, the three §8 language results, learning time, index translations, and Appendix I.1–I.9. Lean refutes the direction printed in the p. 464 corollary and proves the reverse obstruction. [Results and conventions](GenLimitLean/PaperMaps/Paper00_LanguageIdentification.md) |
| **#0A&nbsp;—&nbsp;Inductive&nbsp;Inference&nbsp;from&nbsp;Positive&nbsp;Data** [\[A 80\]](https://doi.org/10.1016/S0019-9958(80)90285-5) | [Theorems 1–5 and Corollaries 1–3](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Results/Overview.lean), plus the separate [semantic characterization](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Characterization.lean). |
| **#01&nbsp;—&nbsp;Language&nbsp;Generation** [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) | NeurIPS 2024 [Theorems 2.1, 2.2, and 7.1](GenLimitLean/GenLimit/Paper01_LanguageGeneration/Results/Overview.lean). See the [P01 map](GenLimitLean/PaperMaps/Paper01_LanguageGeneration.md). |
| **#02&nbsp;—&nbsp;Learning&nbsp;Theory** [\[LRT 25\]](https://arxiv.org/abs/2410.13714v5) | The [new main-results facade](GenLimitLean/GenLimit/Paper02_LearningTheory/Results/Overview.lean) exposes Proposition 2.1; Theorems 3.3, 3.5, 3.10, 5.1, 5.2, C.2, and C.4; sample-complexity bounds; the EUC-without-uniform separation; and Theorem 4.1’s six distribution-free PAC, online learning, and generation regions. [Background restatements 2.2--2.5](GenLimitLean/GenLimit/Paper02_LearningTheory/Results/Background.lean) separately credit Gold, Angluin, and KM. |
| **#03&nbsp;—&nbsp;Limits&nbsp;of&nbsp;Language&nbsp;Generation** [\[KMV 25\]](https://arxiv.org/abs/2411.09642v3) | [Theorems 3.1–3.9 and 3.13; Propositions 3.10–3.12](GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean) cover statistical and online generation, breadth, identification rates, and computability in the documented oracle models. The derived oracle-based exponential identification guarantee is exposed separately in [Additional.lean](GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Additional.lean). Appendices A.1 and B.1–B.2 cover support undecidability and subset-oracle learning. See the [detailed P03 map](GenLimitLean/PaperMaps/Paper03_HallucinationAndModeCollapse.md) for assumptions and proof repairs. |
| **#04&nbsp;—&nbsp;Exploring&nbsp;Facets&nbsp;of&nbsp;Language&nbsp;Generation** [\[CP 24\]](https://arxiv.org/abs/2411.15364v2) | [Theorems 1--5](GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean), [original detailed Theorems 6--7](GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Detailed.lean), Propositions 6.1--6.3 and 7.1, Claim 5.2, and Examples 9–11, the randomized lower bound, and the effective oracle implementations. |
| **#05&nbsp;—&nbsp;Hallucinations,&nbsp;Breadth,&nbsp;and&nbsp;Stability** [\[KMV 24\]](https://arxiv.org/abs/2412.18530v2) | The numbered main results in Sections 3–8 include the breadth characterizations, IID rates, oracle constructions, and infinite coverage. The map identifies seven literal counterexamples and the two open characterizations in Figure 4. See the [P05 theorem map](GenLimitLean/PaperMaps/Paper05_HallucinationsBreadthAndStability.md). |
| **#06&nbsp;—&nbsp;Noisy&nbsp;Examples** [\[RR 25\]](https://proceedings.mlr.press/v267/raman25a.html) | [Theorems 3.1, 3.3, 3.9–3.10, Corollaries 3.4 and 3.7, and Appendix results C.2, C.3, and D.2](GenLimitLean/GenLimit/Paper06_NoisyExamples/Results/Overview.lean). [Numerical noisy closure dimension and optimal uniform thresholds](GenLimitLean/GenLimit/Paper06_NoisyExamples/Quantitative.lean). |
| **#07&nbsp;—&nbsp;Density&nbsp;Measures** [\[KW 25\]](https://arxiv.org/abs/2504.14370v1) | [All Section 2 and detailed main theorem statements](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean). Chronological histories give the index-accuracy and element-density guarantees. With an unordered sample alone, the tower and minimax theorems hold, while valid rules can be forced to have density zero on an injective text. [P07 theorem map](GenLimitLean/PaperMaps/Paper07_DensityMeasuresForLanguageGeneration.md). |
| **#08&nbsp;—&nbsp;Hallucination&nbsp;Detection** [\[KMSV 25\]](https://arxiv.org/abs/2504.17004v2) | [Theorems 2.1, 2.3, A.1, and A.2, and Corollary 2.2](GenLimitLean/GenLimit/Paper08_HallucinationDetection/Results/Overview.lean); Lean also [corrects the false Example 1 inference](GenLimitLean/GenLimit/Paper08_HallucinationDetection/ExampleOne.lean). The [iid extension](GenLimitLean/GenLimit/Bridges/Paper03ToPaper08IID.lean) characterizes almost-sure detection by finite tell-tales. |
| **#09&nbsp;—&nbsp;Representative&nbsp;Language&nbsp;Generation** [\[PRR 25\]](https://proceedings.mlr.press/v267/peale25a.html) | The [published-result surface](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L29) covers Theorem 3.3, Corollaries 3.4--3.6, Theorem 3.7, Corollary 3.8, and Lemmas 4.3, 4.6, and 4.9; [Corollary 3.6 admits a separation precisely on infinite countable domains](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/SeparationDomain.lean). Lean also [kernel-checks direct counterexamples to printed Lemma 4.8 and Theorem 4.4](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L134) and gives [separately named exact-profile repairs](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L156) for those claims; neither refutations nor repairs are counted as positive coverage of the printed claims. |
| **#10&nbsp;—&nbsp;Union-Closedness&nbsp;of&nbsp;Language&nbsp;Generation** [\[HKMV 25\]](https://arxiv.org/abs/2506.18642v1) | [Overview and detailed nonclosure theorems](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean), [identification Remark 4.2](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/IdentificationUnion.lean), [deterministic and randomized appendix bounds, and the concrete column construction](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Appendix.lean). |
| **#11&nbsp;—&nbsp;Learning&nbsp;Algorithms&nbsp;in&nbsp;the&nbsp;Limit** [\[PF 25\]](https://proceedings.mlr.press/v291/papazov25a.html) | Theorems 12 and 14 under quantitative ECTT and Corollaries 13 and 15 have finite-table learners. Lemma 9 has a counterexample on teacher-relative domains. Theorem 16 gives a tape-geometric reduction to rational learning. Theorem 17 excludes computable mass bounds and characteristic-set selectors, Corollary 18 excludes IPTD in all three observation modes, and Theorem 21 proves MSM convergence with a fixed tie rule. See the [P11 theorem map](GenLimitLean/PaperMaps/Paper11_LearningAlgorithmsInTheLimit.md). |
| **#12&nbsp;—&nbsp;Noise,&nbsp;Loss,&nbsp;and&nbsp;Feedback** [\[BPZ 25\]](https://arxiv.org/abs/2507.15319v2) | [Theorems 1.1–1.8](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean); [Algorithm 4](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/InfiniteFeedback.lean#L624) and [Theorem 6.3](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/InfiniteFeedback.lean#L1707) in the mandatory-query interface; [finite-feedback elimination / Theorem 6.7](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/FiniteFeedback.lean#L578); and [Algorithm 6 / Theorem 1.8 for feedback identification](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/FeedbackIdentification.lean#L327). See the [detailed P12 map](GenLimitLean/PaperMaps/Paper12_NoiseLossAndFeedback.md). |
| **#13&nbsp;—&nbsp;Pareto-optimal&nbsp;Non-uniform&nbsp;Generation** [\[CP 25\]](https://arxiv.org/abs/2510.02795v1) | The clean and noisy theorems cover repeated presentations. Representative Theorem 7 holds at positive tolerance and has a zero-tolerance counterexample. Theorem 9 proves Pareto optimality for defined Procedure 3 scores with finite sublevels. See the [P13 theorem map](GenLimitLean/PaperMaps/Paper13_ParetoOptimalNonuniformGeneration.md). |
| **#14&nbsp;—&nbsp;List&nbsp;Language&nbsp;Identification** [\[CPT 25\]](https://arxiv.org/abs/2511.04103v1) | [Theorems 1–3](GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean) characterize list identification, stratification, and sharp statistical rates. |
| **#15&nbsp;—&nbsp;Partial&nbsp;Enumeration** [\[KW 26\]](https://arxiv.org/abs/2511.05295v1) | [Theorems 1.3, 1.5–1.9 and 1.11](GenLimitLean/GenLimit/Paper15_PartialEnumeration/Results/Overview.lean) include ordered density and finite-deletion invariance. The displayed partial topology in 1.10 and the partial-text reading of Corollary 4.10 have counterexamples. |
| **#16&nbsp;—&nbsp;Complexity&nbsp;Barriers** [\[ABCK 26\]](https://arxiv.org/abs/2511.05759v2) | [Uniform generation sample bounds](GenLimitLean/GenLimit/Paper16_ComplexityBarriers/Results/Overview.lean) for context-free, regular, locally threshold testable, and non-erasing pattern languages. The pattern result holds exactly for positive sizes. [P16 map](GenLimitLean/PaperMaps/Paper16_ComplexityBarriers.md). |
| **#17&nbsp;—&nbsp;Infinite&nbsp;Contamination** [\[MVYZ 25\]](https://arxiv.org/abs/2511.07417v1) | [Membership-query generation, density bounds, bounded displacement, and the finite-class threshold](GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean). Lean refutes Theorem 7.7 at the printed displacement factor and proves the corrected obstruction. [P17 map](GenLimitLean/PaperMaps/Paper17_InfiniteContamination.md). |
| **#18&nbsp;—&nbsp;Safe&nbsp;Language&nbsp;Generation** [\[AAK 26\]](https://arxiv.org/abs/2601.08648v2) | [Theorems 3.1, 5.1, 6.1–6.3, and Corollary 6.1](GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean), including the independent impossibility proof for computable safe generators. [P18 map](GenLimitLean/PaperMaps/Paper18_SafeLanguageGeneration.md). |
| **#19&nbsp;—&nbsp;Effect&nbsp;of&nbsp;Noise** [\[LZ 26\]](https://arxiv.org/abs/2601.21237v2) | [Theorems 2.16–2.19](GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean) and the [numerical noisy-closure dimension bounds](GenLimitLean/GenLimit/Paper19_EffectOfNoise/NumericalDimension.lean). [P19 map](GenLimitLean/PaperMaps/Paper19_EffectOfNoise.md). |
| **#20&nbsp;—&nbsp;Agnostic&nbsp;Identification&nbsp;and&nbsp;Generation** [\[HP 26\]](https://arxiv.org/abs/2601.23258v4) | [Theorems 2.1–2.5, 3.1–3.2, 3.4–3.5, and Corollary 3.3](GenLimitLean/GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/Results/Overview.lean) cover identification rates with attained and unattained optima, minimal identification, and generation with finite or infinite witness index. [P20 map](GenLimitLean/PaperMaps/Paper20_AgnosticLanguageIdentificationAndGeneration.md). |
| **#21&nbsp;—&nbsp;On&nbsp;Generation&nbsp;in&nbsp;Metric&nbsp;Spaces** [\[LRT 26\]](https://arxiv.org/abs/2602.07710v2) | [Theorems 3.1, 3.3, 3.5, 4.1, 4.2, 4.4, 4.6, 4.7, and 4.10; Corollaries 3.2, 3.4, and 4.3; Proposition D.1; Examples 4.5, 4.8, 4.9, 4.11, and B.3; and Lemmas C.1 and C.2](GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean); [Lemma 2.1](GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean); and the [orthogonal covering estimate](GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/OrthogonalCovering.lean). The development follows arXiv v2 at the semantic level; formalization of Appendix E’s oracle and computability discussion remains future work. See the [detailed P21 map](GenLimitLean/PaperMaps/Paper21_GenerationInMetricSpaces.md). |
| **#22&nbsp;—&nbsp;Language&nbsp;Generation&nbsp;with&nbsp;Replay** [\[RVS 26\]](https://arxiv.org/abs/2603.11784v2) | [Theorems 4.1, 5.1, 6.1, 6.6, 7.1, and 7.3](GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean). Theorem 7.1 proves the proper membership-query lower bound using a computable diagonal family. |
| **#23&nbsp;—&nbsp;Banach&nbsp;Density** [\[KW 26b\]](https://arxiv.org/abs/2604.02385v2) | [Theorems 2.2, 4.5, 5.1, and 5.8](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/Results/Overview.lean) give the one-dimensional and rectangular obstructions, the sharp finite-rank interval guarantee, and the sharp centered-cube guarantee. Corollaries 4.3, 4.6, and 4.7 cover finite output speed, window bounds, and reordered strings. A [separate Lean proof](GenLimitLean/External/Paper23PowerFilter.lean) gives 5.5 and 5.6 for filters dominating a positive logarithmic power, and the fixed-shape density bound in 5.7. Every divergent filter is covered on the integer line. The general higher-dimensional claims in 2.5, 5.5, and 5.6 remain unproved. Equation (28) in the proof of 5.5 has a counterexample. The [paper map](GenLimitLean/PaperMaps/Paper23_BanachDensityTopologyAndGeometry.md) records the window conventions in 4.1, the exact-identification counterexample to 5.7, and the counterexample and correction to 5.9. |
| **#24&nbsp;—&nbsp;Price&nbsp;of&nbsp;Privacy** [LHJG 26](https://arxiv.org/abs/2604.07238v2) | [All six main theorems](GenLimitLean/GenLimit/Paper24_PriceOfPrivacy/Results/Overview.lean) cover private identification and generation on IID samples, finite-sample error with a known or unknown witness bound, and quantitative privacy lower bounds. |
| **#25&nbsp;—&nbsp;Private&nbsp;Generation&nbsp;and&nbsp;Identification** [MVYZ 26](https://arxiv.org/abs/2604.08504v1) | [Theorems 1.1, 1.2, 1.5 and 1.6](GenLimitLean/GenLimit/Paper25_PrivateGenerationAndIdentification/Results/Overview.lean) cover private generation, its finite-family sample bound, and online and stochastic identification. Both bounds of 1.3 are proved for every collection size k ≥ 2. The [paper map](GenLimitLean/PaperMaps/Paper25_PrivateGenerationAndIdentification.md) records the singleton obstruction, the counterexamples to the sharper Appendix C.3 coefficient, and the proof of the online identification upper bound C.5 for Algorithm 2. |
| **#26&nbsp;—&nbsp;Identification&nbsp;with&nbsp;Computational&nbsp;Trace** [PSV 26](https://openreview.net/forum?id=1OAGf7ntSE) | Perfect TM traces and the robust DFA, pushdown, and TM thresholds, including both impossibility results. [Theorems 3.1, 4.1, 4.3, and 4.5](GenLimitLean/GenLimit/Paper26_IdentificationWithComputationalTrace/Results/Overview.lean) |
| **#27&nbsp;—&nbsp;Feedback&nbsp;Queries&nbsp;and&nbsp;Mistakes** [\[HKMV 26\]](https://openreview.net/forum?id=jvfXyIcQ8a) | [Theorems 3.1–3.4 and 3.9–3.10, Corollaries 3.6–3.8](GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean). All nine main results. Appendix Lemma A.8 refuted, with an independent proof of 3.9. |
| **#28&nbsp;—&nbsp;Contrastive&nbsp;Generation** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1) | [Theorems 4.3, 4.7, 5.4–5.5, 5.13–5.14, 6.5–6.6 and 6.8](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Results/Overview.lean). Includes the strict clean hierarchy, general infinite-defect identification and unordered observation transport. |
| **#29&nbsp;—&nbsp;Mistake-Bounded&nbsp;Language&nbsp;Generation** [\[KPR 26\]](https://arxiv.org/abs/2605.10809v1) | [Qualified 4.1 and 5.1, logarithmic bound 6.1, and refutation of pointwise 6.4](GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean). [Tightness 5.3 and noisy bounds 7.1–7.2](GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Supporting.lean). The weighted bound needs positive target weight. Generator-first timing gives a one-round shift in 5.1. |
| **#30&nbsp;—&nbsp;Time-Sensitive&nbsp;Language&nbsp;Generation** [\[GMDT 26\]](https://arxiv.org/abs/2605.11302v2) | [Almost-sure impossibilities 1–2, uniform-rate refutation for 3, sharp timely upper density 1/2 for 4](GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean). Theorem 4 uses a queue-totalized generator with a matching adaptive exact presentation. |
| **#31&nbsp;—&nbsp;Bounded&nbsp;Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1) | The [9 main-text and 4 appendix results](GenLimitLean/GenLimit/Paper31_BoundedMemory/Results/Overview.lean) cover memoryless generation, fixed-order density with bounded memory, and incremental identification and generation. [Scope and proof map](GenLimitLean/PaperMaps/Paper31_BoundedMemory.md). |
| **#32&nbsp;—&nbsp;Infinitely&nbsp;Many&nbsp;Hallucinations** [\[SBC 26\]](https://arxiv.org/abs/2606.28354v1) | [Precision, recall and novelty theorems](GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), including 4.9 for Algorithm 7. Lean counterexamples give zero lower recall for Algorithms 2 and 6 on full input (4.5 and 4.8). A different generator attains the 4.8 bound. [Proofs and counterexamples](GenLimitLean/PaperMaps/Paper32_InfinitelyManyHallucinations.md). |
| **#39&nbsp;—&nbsp;Dense&nbsp;Generation** [\[CLSWZ 26\]](https://arxiv.org/abs/2608.01320v2) | [Theorem 3.15 lower density 1/2 and Theorem B.3](GenLimitLean/GenLimit/Paper39_DenseGeneration/Results/Overview.lean). The separate optimality upper bound and randomized/multi-order results remain unformalized. See the [paper map](GenLimitLean/PaperMaps/Paper39_DenseGeneration.md). |

The Lean formalization for this research topic is surprisingly short. Building
on the shared definitions in [`Core`](GenLimitLean/GenLimit/Core/), the
paper-specific semantic verification that the KM algorithm generates in the
limit—excluding the separate finite-query implementation—uses only about 330
non-comment lines of Lean.

For detailed paper-to-Lean correspondence, formalization boundaries, and
cross-paper relationships, see the [paper registry](GenLimitLean/PAPER_MAP.md)
and [detailed paper maps](GenLimitLean/PaperMaps/).

For machine-assisted theorem discovery, the generated
[declaration cards](registry/generated/declarations.jsonl) expose the actual
Lean types, modules, direct dependencies, aliases, and claim links for public
library declarations; the companion
[declaration index](registry/generated/declaration-index.json) provides lookup
facets.

## Verification and audit

These formalizations were developed with AI assistance (`GPT-5.6-sol ultra` and `xhigh`)
under human direction. Lean's kernel checks the formal proofs; paper-to-Lean
translation is assessed separately through AI-assisted source comparison and,
where recorded, human audit.

We distinguish three cumulative levels of human paper-to-Lean audit:

| Level | Human check |
|---|---|
| **1. Theorem specification** | The main theorem's assumptions, inputs, outputs, and mathematical conclusion match the paper. |
| **2. Algorithm correspondence** | Level 1, plus the full formal construction or state machine match the paper's algorithm. |
| **3. Proof correspondence** | Level 2, plus the intermediate lemmas and proof dependencies are checked against their Lean counterparts. |

Detailed human and AI-assisted audit records are maintained under
[`AuditRecords`](GenLimitLean/AuditRecords/), while kernel and logical-dependency
checks are documented in [`AUDIT.md`](GenLimitLean/AUDIT.md).

## Build and reading path

The project pins Lean 4.24.0 and Mathlib 4.24.0.

```bash
cd GenLimitLean
lake exe cache get
lake build
lake build Examples
../scripts/check_lean_audit.sh
```

The unified audit command runs the generated `RegistryAudit.lean` check for
every registry-linked declaration and the hand-maintained `Audit.lean`
regression probes. GitHub Actions builds the library and the separate compiling
[usage examples](GenLimitLean/Examples.lean), runs both audit layers, and
checks for unfinished proofs. The
[Lean package README](GenLimitLean/README.md) provides the main theorem entry
points and module-level reading order.


## References

- **#0 — Language Identification in the Limit** [\[G 67\]](https://doi.org/10.1016/S0019-9958(67)91165-5).
  E. Mark Gold. *Information and Control* 10(5), pp. 447–474, 1967.

- **#0A — Inductive Inference from Positive Data** [\[A 80\]](https://doi.org/10.1016/S0019-9958(80)90285-5).
  Dana Angluin. *Information and Control* 45(2), pp. 117--135, 1980.

- **#01 — Language Generation in the Limit** [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html).
  Jon Kleinberg and Sendhil Mullainathan. *Advances in Neural Information
  Processing Systems 37 (NeurIPS 2024)*, 2024.
  [Proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) ·
  [arXiv](https://arxiv.org/abs/2404.06757) ·
  [DOI](https://doi.org/10.52202/079017-2111).

- **#02 — Generation through the Lens of Learning Theory** [\[LRT 25\]](https://arxiv.org/abs/2410.13714v5).
  Jiaxun Li, Vinod Raman, and Ambuj Tewari. *Proceedings of the 38th Conference
  on Learning Theory (COLT 2025)*, PMLR 291, pp. 4740--4776, 2025.
  [arXiv v5](https://arxiv.org/abs/2410.13714v5).

- **#03 — On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse** [\[KMV 25\]](https://arxiv.org/abs/2411.09642v3).
  Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas. 2025.
  [arXiv v3](https://arxiv.org/abs/2411.09642v3).

- **#04 — Exploring Facets of Language Generation in the Limit** [\[CP 24\]](https://arxiv.org/abs/2411.15364v2).
  Moses Charikar and Chirag Pabbaraju. arXiv:2411.15364v2, 2024.
  [arXiv v2](https://arxiv.org/abs/2411.15364v2).

- **#05 — On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability** [\[KMV 24\]](https://arxiv.org/abs/2412.18530v2).
  Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas.
  arXiv:2412.18530v2, 2024. [arXiv v2](https://arxiv.org/abs/2412.18530v2).

- **#06 — Generation from Noisy Examples** [\[RR 25\]](https://proceedings.mlr.press/v267/raman25a.html).
  Ananth Raman and Vinod Raman. *Proceedings of the 42nd International
  Conference on Machine Learning (ICML 2025)*, PMLR 267, pp. 51079--51093,
  2025.
  [Proceedings](https://proceedings.mlr.press/v267/raman25a.html) ·
  [arXiv v2](https://arxiv.org/abs/2501.04179v2).

- **#07 — Density Measures for Language Generation** [\[KW 25\]](https://arxiv.org/abs/2504.14370).
  Jon Kleinberg and Fan Wei. *Proceedings of the 66th IEEE Symposium on
  Foundations of Computer Science (FOCS 2025)*, pp. 620--658, 2025.
  [arXiv](https://arxiv.org/abs/2504.14370) ·
  [DOI](https://doi.org/10.1109/FOCS63196.2025.00034).

- **#08 — (Im)possibility of Automated Hallucination Detection in Large Language Models** [\[KMSV 25\]](https://arxiv.org/abs/2504.17004v2).
  Amin Karbasi, Omar Montasser, John Sous, and Grigoris Velegkas.
  arXiv:2504.17004v2, 2025.
  [arXiv v2](https://arxiv.org/abs/2504.17004v2).

- **#09 — Representative Language Generation** [\[PRR 25\]](https://proceedings.mlr.press/v267/peale25a.html).
  Charlotte Peale, Vinod Raman, and Omer Reingold. *Proceedings of the 42nd
  International Conference on Machine Learning (ICML 2025)*, PMLR 267,
  pp. 48518--48541, 2025.
  [Proceedings](https://proceedings.mlr.press/v267/peale25a.html) ·
  [arXiv v1](https://arxiv.org/abs/2505.21819v1).

- **#10 — On Union-Closedness of Language Generation** [\[HKMV 25\]](https://arxiv.org/abs/2506.18642v1).
  Steve Hanneke, Amin Karbasi, Anay Mehrotra, and Grigoris Velegkas.
  arXiv:2506.18642v1, 2025.
  [arXiv v1](https://arxiv.org/abs/2506.18642v1).

- **#11 — Learning Algorithms in the Limit** [\[PF 25\]](https://proceedings.mlr.press/v291/papazov25a.html).
  Hristo Papazov and Nicolas Flammarion. *Proceedings of the 38th Conference
  on Learning Theory (COLT 2025)*, PMLR 291, pp. 4486--4510, 2025.
  [Proceedings](https://proceedings.mlr.press/v291/papazov25a.html).

- **#12 — Language Generation in the Limit: Noise, Loss, and Feedback** [\[BPZ 25\]](https://arxiv.org/abs/2507.15319v2).
  Yannan Bai, Debmalya Panigrahi, and Ian Zhang. arXiv:2507.15319v2, 2025.
  [arXiv v2](https://arxiv.org/abs/2507.15319v2).

- **#13 — Pareto-optimal Non-uniform Language Generation** [\[CP 25\]](https://arxiv.org/abs/2510.02795v1).
  Moses Charikar and Chirag Pabbaraju. arXiv:2510.02795v1, 2025.
  [arXiv v1](https://arxiv.org/abs/2510.02795v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2510.02795).

- **#14 — A Characterization of List Language Identification in the Limit** [\[CPT 25\]](https://arxiv.org/abs/2511.04103v1).
  Moses Charikar, Chirag Pabbaraju, and Ambuj Tewari.
  arXiv:2511.04103v1, 2025.
  [arXiv v1](https://arxiv.org/abs/2511.04103v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2511.04103).

- **#15 — Partial Enumeration** [\[KW 26\]](https://arxiv.org/abs/2511.05295).
  Jon Kleinberg and Fan Wei. "Language Generation and Identification From
  Partial Enumeration: Tight Density Bounds and Topological
  Characterizations." *Proceedings of the 58th Annual ACM Symposium on Theory
  of Computing (STOC 2026)*, 2026.
  [arXiv](https://arxiv.org/abs/2511.05295) ·
  [STOC accepted paper](https://acm-stoc.org/stoc2026/accepted-papers.html).

- **#16 — Language Generation: Complexity Barriers and Implications for Learning** [\[ABCK 26\]](https://arxiv.org/abs/2511.05759v2).
  Marcelo Arenas, Pablo Barceló, Luis Cofré, and Alexander Kozachinskiy.
  arXiv:2511.05759v2, January 2026. [arXiv v2](https://arxiv.org/abs/2511.05759v2).

- **#17 — Language Generation with Infinite Contamination** [\[MVYZ 25\]](https://arxiv.org/abs/2511.07417v1).
  Anay Mehrotra, Grigoris Velegkas, Xifan Yu, and Felix Zhou.
  arXiv:2511.07417v1, 2025. [arXiv v1](https://arxiv.org/abs/2511.07417v1).

- **#18 — Safe Language Generation in the Limit** [\[AAK 26\]](https://arxiv.org/abs/2601.08648v2).
  Antonios Anastasopoulos, Giuseppe Ateniese, and Evgenios M. Kornaropoulos.
  arXiv:2601.08648v2, 2026.
  [arXiv v2](https://arxiv.org/abs/2601.08648v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2601.08648).

- **#19 — Characterizing the Effect of Noise in Language Generation in the Limit** [\[LZ 26\]](https://arxiv.org/abs/2601.21237v2).
  Aaron Li and Ian Zhang. arXiv:2601.21237v2, 2026.
  [arXiv v2](https://arxiv.org/abs/2601.21237v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2601.21237).

- **#21 — On Generation in Metric Spaces** [\[LRT 26\]](https://arxiv.org/abs/2602.07710v2).
  Jiaxun Li, Vinod Raman, and Ambuj Tewari. arXiv:2602.07710v2, 2026;
  revised 24 October 2026.
  [arXiv v2](https://arxiv.org/abs/2602.07710v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2602.07710).

- **#22 — Language Generation with Replay** [\[RVS 26\]](https://arxiv.org/abs/2603.11784v2).
  Giorgio Racca, Michal Valko, and Amartya Sanyal. "Language Generation with
  Replay: A Learning-Theoretic View of Model Collapse." Accepted at
  *International Conference on Machine Learning (ICML 2026)*, 2026.
  [arXiv v2](https://arxiv.org/abs/2603.11784v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2603.11784).

- **#23 — Banach Density, Topology, and Geometry** [\[KW 26b\]](https://arxiv.org/abs/2604.02385v2).
  Jon Kleinberg and Fan Wei. "Validity, Sparse Holes, and Breadth in Language
  Generation: Banach Density, Topology, and Geometry." arXiv:2604.02385v2,
  2026.
  [arXiv v2](https://arxiv.org/abs/2604.02385v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2604.02385).

- **#24 — On the Price of Privacy for Language Identification and Generation**. Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao. [arXiv v2](https://arxiv.org/abs/2604.07238v2).

- **#25 — Private Generation and Identification**. Anay Mehrotra, Grigoris Velegkas, Xifan Yu, and Felix Zhou. “Differentially Private Language Generation and Identification in the Limit.” [arXiv v1](https://arxiv.org/abs/2604.08504v1).

- **#26 — Language Identification in the Limit with Computational Trace**. Binghui Peng, Amin Saberi, and Grigoris Velegkas. ICLR 2026. [Paper](https://openreview.net/pdf?id=1OAGf7ntSE) · [PaperMap](GenLimitLean/PaperMaps/Paper26_IdentificationWithComputationalTrace.md)

- **#27 — Language Generation with Feedback: Queries and Mistakes** [\[HKMV 26\]](https://openreview.net/forum?id=jvfXyIcQ8a).
  Steve Hanneke, Amin Karbasi, Anay Mehrotra, and Grigoris Velegkas.
  *International Conference on Machine Learning (ICML 2026)*, 2026.
  [OpenReview](https://openreview.net/forum?id=jvfXyIcQ8a).

- **#28 — Contrastive Identification and Generation in the Limit** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1).
  Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao.
  arXiv:2605.06211v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.06211v1).

- **#29 — Mistake-Bounded Language Generation** [\[KPR 26\]](https://arxiv.org/abs/2605.10809v1).
  Jon Kleinberg, Charlotte Peale, and Omer Reingold.
  arXiv:2605.10809v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.10809v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.10809).

- **#30 — A Theory of Time-Sensitive Language Generation** [\[GMDT 26\]](https://arxiv.org/abs/2605.11302v2).
  Atul Ganju, Travis McVoy, Shaddin Dughmi, and Shang-Hua Teng.
  arXiv:2605.11302v2, 2026.
  [arXiv v2](https://arxiv.org/abs/2605.11302v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.11302).

- **#31 — On Language Generation in the Limit with Bounded Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1).
  Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas.
  arXiv:2605.30324v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.30324v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.30324).

- **#32 — Generating in the Limit with Infinitely Many Hallucinations** [\[SBC 26\]](https://arxiv.org/abs/2606.28354v1).
  Irene Strauss, Alexandra Butoi, and Ryan Cotterell.
  arXiv:2606.28354v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2606.28354v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2606.28354).

- **#39 — Dense Language Generation Made Simple** [\[CLSWZ 26\]](https://arxiv.org/abs/2608.01320v2).
  Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng Zhang.
  "Dense Language Generation Made Simple: Deterministic, Randomized, and
  Multi-Order Algorithms." arXiv:2608.01320v2, 2026.
  [arXiv v2](https://arxiv.org/abs/2608.01320v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2608.01320).

Bibliographic entries for the source papers are collected in
[`GenLimitLean/CITATION.bib`](GenLimitLean/CITATION.bib).

## Citation

```bibtex
@misc{li2026genlimitlib,
  title         = {{GenLimitLib}: A Formal Library for Language Generation in the Limit
                   and {AI}-Assisted Mathematical Research},
  author        = {Li, Shuangping and Zhang, Peng},
  year          = {2026},
  eprint        = {2609.36663},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LG},
  url           = {https://arxiv.org/abs/2609.36663}
}
```

## License

The repository is licensed under the [Apache License 2.0](LICENSE).
