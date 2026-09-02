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
[Shuangping Li](https://github.com/fifalsp) and Peng Zhang.

## Current scope

The modern identifiers follow stable first-appearance order in the
[Language Generation reading list](https://languagegeneration.github.io/):
`#01`--`#36` retain the repository's working-inventory numbers, and later
additions continue the sequence. The foundational identification papers use
`#0` for Gold (1967) and the adjacent identifier `#0A` for Angluin (1980),
without renumbering the modern sequence.

| Paper | Formalized in Lean |
|---|---|
| **#0&nbsp;—&nbsp;Language&nbsp;Identification** [\[G 67\]](https://doi.org/10.1016/S0019-9958(67)91165-5) | [Semantic identification model](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Model.lean#L33); [Theorem 7.1](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Abstract/Enumeration.lean#L290); [finite-language learning](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Finite.lean#L120); [locking](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Locking.lean#L373) and [finite tell-tales](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean#L123); the [Section 8 finite/superfinite boundary](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean#L229); and [complete-informant enumeration](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Informant/Enumeration.lean#L180). |
| **#0A&nbsp;—&nbsp;Inductive&nbsp;Inference&nbsp;from&nbsp;Positive&nbsp;Data** [\[A 80\]](https://doi.org/10.1016/S0019-9958(80)90285-5) | [Semantic characterization](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Characterization.lean#L278), [effective Theorem 1](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L598), and [effective Corollary 1](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L614), with semantic and computability layers kept separate. |
| **#01&nbsp;—&nbsp;Language&nbsp;Generation** [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) | [Section 4 semantic construction](GenLimitLean/GenLimit/Paper01_LanguageGeneration/Semantic.lean#L113); [literal finite-set interface](GenLimitLean/GenLimit/Paper01_LanguageGeneration/SetInterface.lean#L217); and [Theorem 2.1 (NeurIPS proceedings)](GenLimitLean/GenLimit/Paper01_LanguageGeneration/FiniteQuery/Main.lean#L60) and [Theorem 2.1 (arXiv v1)](GenLimitLean/GenLimit/Paper01_LanguageGeneration/FiniteQuery/ArxivV1.lean#L307). |
| **#02&nbsp;—&nbsp;Learning&nbsp;Theory** [\[LRT 25\]](https://arxiv.org/abs/2410.13714v5) | [Proposition 2.1](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L53), [Theorem 2.4](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L75), and [Theorem 2.5](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L87); [Theorem 3.3](GenLimitLean/GenLimit/Paper02_LearningTheory/Closure.lean#L258) and its [sample-complexity bounds](GenLimitLean/GenLimit/Paper02_LearningTheory/UniformSampleComplexity.lean#L281); [Theorem 3.5](GenLimitLean/GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean#L145); [Theorem 3.10](GenLimitLean/GenLimit/Paper02_LearningTheory/GenerationInLimitCharacterization.lean#L375); prompted [Theorem 5.1](GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedClosure.lean#L486) and [Theorem 5.2](GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L161); hierarchy-separation [Lemmas 3.4](GenLimitLean/GenLimit/Paper02_LearningTheory/EarlierSectionThreeExamples.lean#L102), [3.9](GenLimitLean/GenLimit/Paper02_LearningTheory/EarlierSectionThreeExamples.lean#L192), [3.12](GenLimitLean/GenLimit/Paper02_LearningTheory/LimitVsNonuniformSeparation.lean#L439), [4.2](GenLimitLean/GenLimit/Paper02_LearningTheory/LimitVsNonuniformSeparation.lean#L456), and [4.3](GenLimitLean/GenLimit/Paper02_LearningTheory/CountableUnionSeparation.lean#L603); [Theorem 4.1's VC/Littlestone combinatorial core](GenLimitLean/GenLimit/Paper02_LearningTheory/Prediction.lean#L1218); and Appendix [Theorem C.2](GenLimitLean/GenLimit/Paper02_LearningTheory/FiniteEUCUnion.lean#L489) and [Theorem C.4](GenLimitLean/GenLimit/Paper02_LearningTheory/EventuallyUnboundedClosure.lean#L223). |
| **#03&nbsp;—&nbsp;Limits&nbsp;of&nbsp;Language&nbsp;Generation** [\[KMV 25\]](https://arxiv.org/abs/2411.09642v3) | Probability-free semantic support-oracle cores of [Theorems 3.5, 3.7, and 3.9](GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean), plus [finite-tell-tale structural lemmas](GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FurtherIdentification.lean) motivated by Propositions 3.11–3.12. Statistical rates and Turing-machine computability are not formalized. |
| **#04&nbsp;—&nbsp;Exploring&nbsp;Facets&nbsp;of&nbsp;Language&nbsp;Generation** [\[CP 24\]](https://arxiv.org/abs/2411.15364v2) | [Theorems 1--5](GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean), [original detailed Theorems 6--7](GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Detailed.lean), Propositions 6.1--6.3 and 7.1, Claim 5.2, and Examples 9--10. |
| **#05&nbsp;—&nbsp;Hallucinations,&nbsp;Breadth,&nbsp;and&nbsp;Stability** [\[KMV 24\]](https://arxiv.org/abs/2412.18530v2) | Semantic [Theorem 3.3](GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L27), the sufficiency direction of [Theorem 3.8](GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L37), and the approximate clause of [Theorem 3.15](GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L46). |
| **#06&nbsp;—&nbsp;Noisy&nbsp;Examples** [\[RR 25\]](https://proceedings.mlr.press/v267/raman25a.html) | [Theorem 3.1](GenLimitLean/GenLimit/Paper06_NoisyExamples/UniformIndependent.lean#L306), [Theorem 3.3](GenLimitLean/GenLimit/Paper06_NoisyExamples/NoisyClosure.lean#L625), [Theorem 3.9](GenLimitLean/GenLimit/Paper06_NoisyExamples/NoiselessRobustification.lean#L740), [Theorem 3.10](GenLimitLean/GenLimit/Paper06_NoisyExamples/FiniteUnionLimit.lean#L218), Appendix [Lemma C.2](GenLimitLean/GenLimit/Paper06_NoisyExamples/AlternatePositive.lean#L343), [Theorem C.3](GenLimitLean/GenLimit/Paper06_NoisyExamples/AlternatePositive.lean#L327), and [Lemma D.2](GenLimitLean/GenLimit/Paper06_NoisyExamples/NonuniformIndependent.lean#L245). |
| **#07&nbsp;—&nbsp;Density&nbsp;Measures** [\[KW 25\]](https://arxiv.org/abs/2504.14370v1) | [Theorem 2.1](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfinitelyOften.lean#L225), [Corollary 2.2](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/IndexLimsup.lean#L64), [Claims 4.2--4.7](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Feasible.lean), the [finite-rank forest through Corollary 6.10](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Fallback.lean), the [Claim 6.11 persistence diagnostic](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/PersistenceCounterexample.lean), and the conditional [`1/8`](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/OneEighth.lean) / corrected capacity-two [`1/10`](GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/CapacityCharge.lean) Theorem 6.12 endgames. |
| **#08&nbsp;—&nbsp;Hallucination&nbsp;Detection** [\[KMSV 25\]](https://arxiv.org/abs/2504.17004v2) | [Theorem 2.1](GenLimitLean/GenLimit/Paper08_HallucinationDetection/Reductions.lean#L237), [Corollary 2.2](GenLimitLean/GenLimit/Paper08_HallucinationDetection/AngluinCondition.lean#L85), [Theorem 2.3](GenLimitLean/GenLimit/Paper08_HallucinationDetection/NegativeExamples.lean#L58), [Theorem A.1](GenLimitLean/GenLimit/Paper08_HallucinationDetection/Appendix.lean#L102), and [Theorem A.2](GenLimitLean/GenLimit/Bridges/Paper02ToPaper08.lean#L19); Lean also [corrects the false Example 1 inference](GenLimitLean/GenLimit/Paper08_HallucinationDetection/ExampleOne.lean). |
| **#09&nbsp;—&nbsp;Representative&nbsp;Language&nbsp;Generation** [\[PRR 25\]](https://proceedings.mlr.press/v267/peale25a.html) | The [published-result surface](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L29) covers Theorem 3.3, Corollaries 3.4--3.6, Theorem 3.7, Corollary 3.8, and Lemmas 4.3, 4.6, and 4.9; Corollary 3.6 exposes the intended infinite-universe witness. Lean also [kernel-checks a counterexample to printed Theorem 4.4](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L132) and gives [separately named exact-profile repairs](GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L141) for Lemma 4.8 and Theorem 4.4; those repairs are not counted as coverage of the printed claims. |
| **#10&nbsp;—&nbsp;Union-Closedness&nbsp;of&nbsp;Language&nbsp;Generation** [\[HKMV 25\]](https://arxiv.org/abs/2506.18642v1) | [Theorems 3.1–3.3](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean); [detailed Theorems 4.1, 4.3, and 4.4](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Detailed.lean); and deterministic [Proposition A.1](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/DeterministicDiagonal.lean). Randomized Proposition A.2 is not formalized. Appendix A.2 includes only a [generic conditional prefix-realizability core](GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/PrefixRealizability.lean), not the concrete construction or Remark A.3. |
| **#11&nbsp;—&nbsp;Learning&nbsp;Algorithms&nbsp;in&nbsp;the&nbsp;Limit** [\[PF 25\]](https://proceedings.mlr.press/v291/papazov25a.html) | The [main-result surface](GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L26) covers Lemma 9; Theorems 12, 14, 16, 17, and 21; and Corollaries 13, 15, and 18. Lemma 9 and the [concrete finite-table single-tape specialization of Corollary 15](GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L102) are fully covered. The remaining seven claims have semantic, constructive, or conditional cores. The `q`-ECTT bridges, parametrized TM complexity classes, and complete TM/PTO and Halting reductions are not formalized; moreover, the current source argument does not establish the invariant required for unconditional MSM convergence. See the [detailed P11 map](GenLimitLean/PaperMaps/Paper11_LearningAlgorithmsInTheLimit.md). |
| **#12&nbsp;—&nbsp;Noise,&nbsp;Loss,&nbsp;and&nbsp;Feedback** [\[BPZ 25\]](https://arxiv.org/abs/2507.15319v2) | [Theorems 1.1–1.8](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean); [Algorithm 4](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/InfiniteFeedback.lean#L624) and [Theorem 6.3](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/InfiniteFeedback.lean#L1707) in the mandatory-query interface; [finite-feedback elimination / Theorem 6.7](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/FiniteFeedback.lean#L578); and [Algorithm 6 / Theorem 1.8 for feedback identification](GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/FeedbackIdentification.lean#L327). |
| **#13&nbsp;—&nbsp;Pareto-optimal&nbsp;Non-uniform&nbsp;Generation** [\[CP 25\]](https://arxiv.org/abs/2510.02795v1) | [Theorems 1, 4–6, and 8](GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean); [Procedure 1](GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean); [Procedure 2](GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/NoisyProcedure.lean); and the conditional [Theorem 9 scheduler endgame](GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/VariantExactPareto.lean). Representative Theorem 7 and the concrete Theorem 9 remain open. |
| **#14&nbsp;—&nbsp;List&nbsp;Language&nbsp;Identification** [\[CPT 25\]](https://arxiv.org/abs/2511.04103v1) | Deterministic [Theorems 1–2](GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean), [Algorithm 1 and Theorem 6](GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Algorithm.lean), and [Theorem 7](GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/GeneralNecessity.lean). Statistical Theorem 3 and Sections 8–10 remain open. |
| **#15&nbsp;—&nbsp;Partial&nbsp;Enumeration** [\[KW 26\]](https://arxiv.org/abs/2511.05295v1) | [Theorem 2.1](GenLimitLean/GenLimit/Paper15_PartialEnumeration/FiniteScope.lean#L154), [Lemma 2.3](GenLimitLean/GenLimit/Paper15_PartialEnumeration/ElementSemiIndex.lean), the [concrete Algorithm 1 / Lemma 2.5 and Theorems 2.2, 2.4, and 1.8](GenLimitLean/GenLimit/Paper15_PartialEnumeration/AlgorithmOneRun.lean), the [Section 3 warm-up priority run, Lemma 3.2, and conditional latest-return charge](GenLimitLean/GenLimit/Paper15_PartialEnumeration/WarmupPriorityRun.lean), [density and growing-pod limit accounting](GenLimitLean/GenLimit/Paper15_PartialEnumeration/PodLimit.lean), the complete causal full-text [Theorem 4.9](GenLimitLean/GenLimit/Paper15_PartialEnumeration/FullTextIdentification.lean) and repaired exact-text [Corollaries 4.10–4.11](GenLimitLean/GenLimit/Paper15_PartialEnumeration/FullTextSeparation.lean), and a [counterexample to the source's stronger arbitrary-partial-text separation claim](GenLimitLean/GenLimit/Paper15_PartialEnumeration/PartialSeparationCounterexample.lean). |
| **#17&nbsp;—&nbsp;Infinite&nbsp;Contamination** [\[MVYZ 25\]](https://arxiv.org/abs/2511.07417v1) | [Theorems 5.1 and 5.4](GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L117); [Theorems 6.1, 6.4, 6.5, 6.11, and 6.14](GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L148); [Theorem 6.15, Corollary 6.16, and Theorem 6.18](GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L236); and [Proposition 7.4, Lemma 7.5, and Theorem 7.8](GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L324). Theorem 6.14 is proved for the justified range `0 < c < 1`; the source's `c = 1` endpoint is not claimed. See the [detailed P17 map](GenLimitLean/PaperMaps/Paper17_InfiniteContamination.md). |
| **#19&nbsp;—&nbsp;Effect&nbsp;of&nbsp;Noise** [\[LZ 26\]](https://arxiv.org/abs/2601.21237v2) | [Theorems 2.16–2.19](GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean#L39). See the [detailed P19 map](GenLimitLean/PaperMaps/Paper19_EffectOfNoise.md). |
| **#23&nbsp;—&nbsp;Banach&nbsp;Density** [\[KW 26b\]](https://arxiv.org/abs/2604.02385v2) | [Claims 3.3 and 3.5](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/WindowDensity.lean), [Claim 3.6](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/Topology.lean#L57), the repaired [Claim 4.11](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/FiniteRankSequence.lean), [Claims 4.18 and 4.20](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/FiniteTreeLCA.lean), and [Claim 4.4 / Appendix Claim 7.1](GenLimitLean/GenLimit/Paper23_BanachDensityTopologyAndGeometry/Nice.lean#L75). |
| **#28&nbsp;—&nbsp;Contrastive&nbsp;Generation** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1) | [Theorem 4.7](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/IdentifierCharacterization.lean#L641); [Theorem 5.4](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/ClosureDimension.lean#L432); [Theorem 5.5](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/NonuniformClosure.lean#L265); [core criteria](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean) and [Theorems 5.13–5.14 punctured](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L329) and [disjoint witnesses](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DisjointHierarchy.lean#L174); [Theorem 6.5](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean#L111); [Theorem 6.6](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/AbsenceCount.lean#L477); [Theorem 6.8](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedIncomparability.lean#L505); and [Proposition 6.3](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DefectInfimum.lean#L467). |
| **#31&nbsp;—&nbsp;Bounded&nbsp;Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1) | [Theorem 1.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/FinitelyRepeating.lean#L273); [Theorem 3.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/ArbitraryRepetitions.lean#L149); [Theorem 3.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/OutputSeparations.lean#L584); order-robust [Theorem 4.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L233), [Theorem 4.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L416), [Theorem 4.10](GenLimitLean/GenLimit/Paper31_BoundedMemory/WindowHardInstance.lean#L1137), and [Theorem 4.15](GenLimitLean/GenLimit/Paper31_BoundedMemory/AdaptiveBuffer.lean#L1102); [Proposition 5.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/ExactIdentificationObstruction.lean#L347) and [Theorem 5.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean#L546); Appendix [Theorem A.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean#L659), [Proposition A.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean#L292), and [Lemma A.3 plus element coding](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalElementCoding.lean#L313). |
| **#39&nbsp;—&nbsp;Dense&nbsp;Generation** [\[CLSWZ 26\]](https://arxiv.org/abs/2608.01320v1) | **Earlier manuscript only; arXiv v1 is not yet formalized.** The Lean files use [recursive criticality](GenLimitLean/GenLimit/Paper39_DenseGeneration/Critical.lean#L19), whereas public v1 Definition 3.2 compares against every earlier consistent language. For the earlier manuscript, Lean covers the [patient-scope construction](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Machine.lean), [Lemma 3.11](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Validity.lean#L233), [Theorem 3.14](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Main.lean#L36), [Example 3.15](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Counterexample.lean#L248), [Lemma 3.16](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Validity.lean#L47), and [Theorem 3.17](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Main.lean#L63). The last three are numbered Example 3.17, Lemma 3.18, and Theorem 3.19 in arXiv v1. |

For detailed paper-to-Lean correspondence, formalization boundaries, and
cross-paper relationships, see the [paper registry](GenLimitLean/PAPER_MAP.md)
and [detailed paper maps](GenLimitLean/PaperMaps/).

The Lean formalization for this research topic is surprisingly short. Building
on the shared definitions in [`Core`](GenLimitLean/GenLimit/Core/), the
paper-specific semantic verification that the KM algorithm generates in the
limit—excluding the separate finite-query implementation—uses only about 325
non-comment lines of Lean.

## Verification and audit

These formalizations were developed with AI assistance (`GPT-5.6-sol ultra`)
under human direction. Lean's kernel checks the formal proofs; paper-to-Lean
translation is assessed separately through AI-assisted source comparison and,
where recorded, named human audit.

We distinguish three cumulative levels of human paper-to-Lean audit:

| Level | Human check |
|---|---|
| **1. Theorem specification** | The main theorem's assumptions, inputs, outputs, and mathematical conclusion match the paper. |
| **2. Algorithm correspondence** | Level 1, plus the paper-facing definitions and the full formal construction or state machine match the paper's algorithm. |
| **3. Proof correspondence** | Level 2, plus the intermediate lemmas, proof dependencies, and manuscript proof steps are checked against their Lean counterparts. |

Detailed human and AI-assisted audit records are maintained under
[`AuditRecords`](GenLimitLean/AuditRecords/), while kernel and axiom checks are
documented in [`AUDIT.md`](GenLimitLean/AUDIT.md).

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

- **#17 — Language Generation with Infinite Contamination** [\[MVYZ 25\]](https://arxiv.org/abs/2511.07417v1).
  Anay Mehrotra, Grigoris Velegkas, Xifan Yu, and Felix Zhou.
  arXiv:2511.07417v1, 2025. [arXiv v1](https://arxiv.org/abs/2511.07417v1).

- **#19 — Characterizing the Effect of Noise in Language Generation in the Limit** [\[LZ 26\]](https://arxiv.org/abs/2601.21237v2).
  Aaron Li and Ian Zhang. arXiv:2601.21237v2, 2026.
  [arXiv v2](https://arxiv.org/abs/2601.21237v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2601.21237).

- **#23 — Banach Density, Topology, and Geometry** [\[KW 26b\]](https://arxiv.org/abs/2604.02385v2).
  Jon Kleinberg and Fan Wei. "Validity, Sparse Holes, and Breadth in Language
  Generation: Banach Density, Topology, and Geometry." arXiv:2604.02385v2,
  2026.
  [arXiv v2](https://arxiv.org/abs/2604.02385v2) ·
  [DOI](https://doi.org/10.48550/arXiv.2604.02385).

- **#28 — Contrastive Identification and Generation in the Limit** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1).
  Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao.
  arXiv:2605.06211v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.06211v1).

- **#31 — On Language Generation in the Limit with Bounded Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1).
  Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas.
  arXiv:2605.30324v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.30324v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.30324).

- **#39 — Dense Language Generation Made Simple** [\[CLSWZ 26\]](https://arxiv.org/abs/2608.01320v1).
  Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng Zhang.
  "Dense Language Generation Made Simple: Deterministic, Randomized, and
  Multi-Order Algorithms." arXiv:2608.01320v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2608.01320v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2608.01320).

Bibliographic entries for the source papers are collected in
[`GenLimitLean/CITATION.bib`](GenLimitLean/CITATION.bib).

## License

The repository is licensed under the [Apache License 2.0](LICENSE).
