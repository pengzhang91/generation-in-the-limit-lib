# Language Generation in the Limit: A Lean Library and Paper Map

This repository develops a Lean 4 library and a paper-centered research map for
**language generation in the limit**. This framework was introduced
by Jon Kleinberg and Sendhil Mullainathan [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html).
In this model, an adversary
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
additions continue the sequence. The foundational identification papers use
`#0` for Gold (1967) and the adjacent identifier `#0A` for Angluin (1980),
without renumbering the modern sequence.

`Paper11` below is the checked-in Lean module name; this documentation does
not derive that identifier from the local knowledge-graph markdown.

| Paper | Formalized in Lean |
|---|---|
| **#0&nbsp;—&nbsp;Language&nbsp;Identification** [\[G 67\]](https://doi.org/10.1016/S0019-9958(67)91165-5) | [Semantic identification model](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Model.lean#L33); [Theorem 7.1](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Abstract/Enumeration.lean#L290); [finite-language learning](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Finite.lean#L120); [locking](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Locking.lean#L373) and [finite tell-tales](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean#L123); the [Section 8 finite/superfinite boundary](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean#L229); and [complete-informant enumeration](GenLimitLean/GenLimit/Paper00_LanguageIdentification/Informant/Enumeration.lean#L180). |
| **#0A&nbsp;—&nbsp;Inductive&nbsp;Inference&nbsp;from&nbsp;Positive&nbsp;Data** [\[A 80\]](https://doi.org/10.1016/S0019-9958(80)90285-5) | [Semantic characterization](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Semantic/Characterization.lean#L278), [effective Theorem 1](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L598), and [effective Corollary 1](GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L614), with semantic and computability layers kept separate. |
| **#01&nbsp;—&nbsp;Language&nbsp;Generation** [\[KM 24\]](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) | [Section 4 semantic construction](GenLimitLean/GenLimit/Paper01_LanguageGeneration/Semantic.lean#L113); [literal finite-set interface](GenLimitLean/GenLimit/Paper01_LanguageGeneration/SetInterface.lean#L217); and [Theorem 2.1 (NeurIPS proceedings)](GenLimitLean/GenLimit/Paper01_LanguageGeneration/FiniteQuery/Main.lean#L60) and [Theorem 2.1 (arXiv v1)](GenLimitLean/GenLimit/Paper01_LanguageGeneration/FiniteQuery/ArxivV1.lean#L307). |
| **#02&nbsp;—&nbsp;Learning&nbsp;Theory** [\[LRT 25\]](https://arxiv.org/abs/2410.13714v5) | [Proposition 2.1](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L53), [Theorem 2.4](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L75), and [Theorem 2.5](GenLimitLean/GenLimit/Paper02_LearningTheory.lean#L87); [Theorem 3.3](GenLimitLean/GenLimit/Paper02_LearningTheory/Closure.lean#L258) and its [sample-complexity bounds](GenLimitLean/GenLimit/Paper02_LearningTheory/UniformSampleComplexity.lean#L281); [Theorem 3.5](GenLimitLean/GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean#L145); [Theorem 3.10](GenLimitLean/GenLimit/Paper02_LearningTheory/GenerationInLimitCharacterization.lean#L375); prompted [Theorem 5.1](GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedClosure.lean#L486) and [Theorem 5.2](GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L161); hierarchy-separation [Lemmas 3.4](GenLimitLean/GenLimit/Paper02_LearningTheory/EarlierSectionThreeExamples.lean#L102), [3.9](GenLimitLean/GenLimit/Paper02_LearningTheory/EarlierSectionThreeExamples.lean#L192), [3.12](GenLimitLean/GenLimit/Paper02_LearningTheory/LimitVsNonuniformSeparation.lean#L439), [4.2](GenLimitLean/GenLimit/Paper02_LearningTheory/LimitVsNonuniformSeparation.lean#L456), and [4.3](GenLimitLean/GenLimit/Paper02_LearningTheory/CountableUnionSeparation.lean#L603); [Theorem 4.1's VC/Littlestone combinatorial core](GenLimitLean/GenLimit/Paper02_LearningTheory/Prediction.lean#L1218); and Appendix [Theorem C.2](GenLimitLean/GenLimit/Paper02_LearningTheory/FiniteEUCUnion.lean#L489) and [Theorem C.4](GenLimitLean/GenLimit/Paper02_LearningTheory/EventuallyUnboundedClosure.lean#L223). |
| **#06&nbsp;—&nbsp;Noisy&nbsp;Examples** [\[RR 25\]](https://proceedings.mlr.press/v267/raman25a.html) | Every paper-owned numbered definition and valid qualitative result, including [Theorem 3.1](GenLimitLean/GenLimit/Paper06_NoisyExamples/UniformIndependent.lean#L306), [Theorem 3.3](GenLimitLean/GenLimit/Paper06_NoisyExamples/NoisyClosure.lean#L625), [Theorem 3.9](GenLimitLean/GenLimit/Paper06_NoisyExamples/NoiselessRobustification.lean#L740), [Theorem 3.10](GenLimitLean/GenLimit/Paper06_NoisyExamples/FiniteUnionLimit.lean#L218), Appendix [Lemma C.2](GenLimitLean/GenLimit/Paper06_NoisyExamples/AlternatePositive.lean#L343), [Theorem C.3](GenLimitLean/GenLimit/Paper06_NoisyExamples/AlternatePositive.lean#L327), and [Lemma D.2](GenLimitLean/GenLimit/Paper06_NoisyExamples/NonuniformIndependent.lean#L245). |
| **#08&nbsp;—&nbsp;Hallucination&nbsp;Detection** [\[KMSV 25\]](https://arxiv.org/abs/2504.17004v2) | [Theorem 2.1](GenLimitLean/GenLimit/Paper08_HallucinationDetection/Reductions.lean#L237), [Corollary 2.2](GenLimitLean/GenLimit/Paper08_HallucinationDetection/AngluinCondition.lean#L85), [Theorem 2.3](GenLimitLean/GenLimit/Paper08_HallucinationDetection/NegativeExamples.lean#L58), [Theorem A.1](GenLimitLean/GenLimit/Paper08_HallucinationDetection/Appendix.lean#L102), and [Theorem A.2](GenLimitLean/GenLimit/Bridges/Paper02ToPaper08.lean#L19); Lean also [corrects the false Example 1 inference](GenLimitLean/GenLimit/Paper08_HallucinationDetection/ExampleOne.lean). |
| **Paper11&nbsp;—&nbsp;Union-Closedness&nbsp;of&nbsp;Language&nbsp;Generation** [\[HKMV 25\]](https://arxiv.org/abs/2506.18642v1) | [Overview Theorems 3.1–3.3](GenLimitLean/GenLimit/Paper11_UnionClosednessOfLanguageGeneration/Results/Overview.lean); [detailed Theorems 4.1, 4.3, and 4.4](GenLimitLean/GenLimit/Paper11_UnionClosednessOfLanguageGeneration/Results/Detailed.lean); and deterministic [Proposition A.1](GenLimitLean/GenLimit/Paper11_UnionClosednessOfLanguageGeneration/DeterministicDiagonal.lean). Randomized Proposition A.2 is not formalized. Appendix A.2 includes only a [generic conditional prefix-realizability core](GenLimitLean/GenLimit/Paper11_UnionClosednessOfLanguageGeneration/PrefixRealizability.lean), not the concrete construction or Remark A.3. |
| **#28&nbsp;—&nbsp;Contrastive&nbsp;Generation** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1) | [Theorem 4.7](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/IdentifierCharacterization.lean#L641); [Theorem 5.4](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/ClosureDimension.lean#L432); [Theorem 5.5](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/NonuniformClosure.lean#L265); [core criteria](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean) and [Theorems 5.13–5.14 punctured](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L329) and [disjoint witnesses](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DisjointHierarchy.lean#L174); [Theorem 6.5](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean#L111); [Theorem 6.6](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/AbsenceCount.lean#L477); [Theorem 6.8](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedIncomparability.lean#L505); and [Proposition 6.3](GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DefectInfimum.lean#L467). |
| **#31&nbsp;—&nbsp;Bounded&nbsp;Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1) | [Theorem 1.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/FinitelyRepeating.lean#L273); [Theorem 3.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/ArbitraryRepetitions.lean#L149); [Theorem 3.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/OutputSeparations.lean#L584); order-robust [Theorem 4.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L233), [Theorem 4.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L416), [Theorem 4.10](GenLimitLean/GenLimit/Paper31_BoundedMemory/WindowHardInstance.lean#L1137), and [Theorem 4.15](GenLimitLean/GenLimit/Paper31_BoundedMemory/AdaptiveBuffer.lean#L1102); [Proposition 5.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/ExactIdentificationObstruction.lean#L347) and [Theorem 5.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean#L546); Appendix [Theorem A.1](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean#L659), [Proposition A.2](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean#L292), and [Lemma A.3 plus element coding](GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalElementCoding.lean#L313). |
| **#39&nbsp;—&nbsp;Dense&nbsp;Generation** [\[CLSWZ 26\]](https://arxiv.org/abs/2608.01320v1) | **Earlier manuscript only; arXiv v1 is not yet formalized.** The Lean files use [recursive criticality](GenLimitLean/GenLimit/Paper39_DenseGeneration/Critical.lean#L19), whereas public v1 Definition 3.2 compares against every earlier consistent language. For the earlier manuscript, Lean covers the [patient-scope construction](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Machine.lean), [Lemma 3.11](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Validity.lean#L233), [Theorem 3.14](GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Main.lean#L36), [Example 3.15](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Counterexample.lean#L248), [Lemma 3.16](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Validity.lean#L47), and [Theorem 3.17](GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Main.lean#L63). The last three are numbered Example 3.17, Lemma 3.18, and Theorem 3.19 in arXiv v1. |

The native #02 development formalizes ordinary and prompted generation at
semantic, set-theoretic interfaces. Cross-paper bridges separately provide
[Theorem 2.2](GenLimitLean/GenLimit/Bridges/GoldToPaper02.lean#L63) and the
[corrected countable form of Theorem 2.3](GenLimitLean/GenLimit/Bridges/AngluinToPaper02.lean#L231);
the paper's arbitrary-class wording of Theorem 2.3 is false. Theorem 4.1 is
present only at its finite-VC/finite-Littlestone combinatorial boundary. The
library does not claim literal PAC/IID or online-regret models, computational
or membership-oracle implementations, or efficiency results. See the
[#02 paper map](GenLimitLean/PaperMaps/Paper02_LearningTheory.md) for the
detailed correspondence and source repairs.

Kleinberg and Wei introduced density measures for language generation
[\[KW 25\]](https://arxiv.org/abs/2504.14370)
and later proved that `1 / 2` is the tight deterministic lower-density bound
[\[KW 26\]](https://arxiv.org/abs/2511.05295). Dense Generation gives a simpler patient-scope construction achieving
the same guarantee. In the partial-enumeration setting, Kleinberg and Wei were
also the first to establish the optimal guarantee: if the enumerated subset
has relative lower density `α` in the target, the optimal guarantee is
`α / 2` [\[KW 26\]](https://arxiv.org/abs/2511.05295).

The detailed [#0 Language Identification map](GenLimitLean/PaperMaps/Paper00_LanguageIdentification.md),
[#0A Inductive Inference from Positive Data map](GenLimitLean/PaperMaps/Paper00A_PositiveDataInference.md),
[#01 Language Generation map](GenLimitLean/PaperMaps/Paper01_LanguageGeneration.md),
[#02 Learning Theory map](GenLimitLean/PaperMaps/Paper02_LearningTheory.md),
[#06 Noisy Examples map](GenLimitLean/PaperMaps/Paper06_NoisyExamples.md),
[#08 Hallucination Detection map](GenLimitLean/PaperMaps/Paper08_HallucinationDetection.md),
[Paper11 Union-Closedness map](GenLimitLean/PaperMaps/Paper11_UnionClosednessOfLanguageGeneration.md),
[#28 Contrastive Generation map](GenLimitLean/PaperMaps/Paper28_ContrastiveGeneration.md),
[#31 Bounded Memory map](GenLimitLean/PaperMaps/Paper31_BoundedMemory.md), and
[#39 Dense Generation map](GenLimitLean/PaperMaps/Paper39_DenseGeneration.md)
record paper-to-Lean correspondence and formalization boundaries. Audit status
in those maps is only a summary; the authoritative records live under
[`GenLimitLean/AuditRecords/`](GenLimitLean/AuditRecords/).

The formalization is deliberately modular. The #01 Language Generation
development separates
whole-language semantics, the observed-set interface, shared finite-critical
selection, and the two source-version-specific finite-query machines.
The #02 Learning Theory path is split into ordinary generation, prediction,
prompted generation, examples, and Appendix C modules so each boundary remains
reviewable. The #06 Noisy Examples development depends only on neutral generic
Core vocabulary, not on the substantive #02 theorem layer. The #08
Hallucination Detection development imports the supporting
[#0A identification layer](GenLimitLean/PaperMaps/Paper00A_PositiveDataInference.md),
whose declarations retain the `GenLimit.Angluin` namespace.
Its native results remain independent of substantive #02 theorems; the one
#02-dependent Appendix A.2 result is isolated in an explicit bridge. The #28
Contrastive Generation development likewise uses the neutral generic Core
and the semantic necessity theorem in the Angluin sibling. It imports neither
the #02 Learning Theory development nor the #08 Hallucination Detection
development. The
paper-independent identification-to-fresh-generation argument is owned by
`GenLimit.Core.IdentificationGeneration` and reused through a thin #28 wrapper.
The Paper11 Union-Closedness development reuses #02's EUC and countable-class
generation results, but keeps its duplicate-free presentation interface,
signed-integer witnesses, and shared alternating diagonal recursion local.
The #31 Bounded Memory development imports only neutral Core and Mathlib modules:
generic presentation vocabulary comes from `GenLimit.Core.GenericGeneration`,
and the Kleinberg--Wei ordered-density interface is housed in
`GenLimit.Core.OrderedDensity`. It imports no sibling paper or bridge.

## Repository guide

- `GenLimitLean/GenLimit/Core/` contains paper-independent definitions and
  semantic lemmas.
- `GenLimitLean/GenLimit/Paper00_LanguageIdentification/` contains the #0 Language Identification abstract, arbitrary-text, and
  informant semantic developments.
- `GenLimitLean/GenLimit/Paper02_LearningTheory/` contains #02 Learning Theory ordinary and prompted
  generation theory, prediction-dimension proxies, and Appendix C EUC results.
- `GenLimitLean/GenLimit/Paper06_NoisyExamples/` contains the #06 Noisy Examples uniform, non-uniform,
  robustification, separation, and appendix results for noisy examples.
- `GenLimitLean/GenLimit/Paper00A_PositiveDataInference/` contains #0A semantic
  identification, finite tell-tales, and the separately marked effective
  Theorem 1 development.
- `GenLimitLean/GenLimit/Paper08_HallucinationDetection/` contains #08 Hallucination Detection's native
  detector, reduction, Example 1, negative-example, and appendix results.
- `GenLimitLean/GenLimit/Paper11_UnionClosednessOfLanguageGeneration/`
  contains the union-closedness witnesses, paper-facing overview theorems, and
  deterministic appendix development.
- `GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/` contains #28 Contrastive Generation's geometry,
  identification, closure, hierarchy, corruption, and defect developments.
- `GenLimitLean/GenLimit/Paper31_BoundedMemory/` contains #31 Bounded Memory's memoryless,
  density, sliding-window, adaptive-buffer, incremental-identification, and
  appendix developments.
- `GenLimitLean/GenLimit/Paper01_LanguageGeneration/` contains the #01 Language Generation semantic and finite-query paths.
- `GenLimitLean/GenLimit/Paper39_DenseGeneration/` contains the #39 Dense Generation patient-scope and
  partial-enumeration developments.
- `GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/` contains the Section 3.3
  counterexample and partial-enumeration proof.
- `GenLimitLean/GenLimit/Bridges/` contains explicit cross-paper comparisons.
- [`GenLimitLean/PAPER_MAP.md`](GenLimitLean/PAPER_MAP.md) is the paper
  registry; detailed maps are under
  [`GenLimitLean/PaperMaps/`](GenLimitLean/PaperMaps/).
- [`GenLimitLean/AuditRecords/`](GenLimitLean/AuditRecords/) is the
  authoritative home for both checksum-verified ChatGPT Pro records and the
  separate named-human audit ledger.

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
cover the #01 Language Generation semantic development at Level 3, the stated
#39 Dense Generation
exact- and partial-enumeration paths against the earlier supplied manuscript at
Level 2, and the shared Core plus #0 Language Identification text path at Level
2. The #02 record is deliberately scope-based rather than assigned one global
level: it covers Proposition 2.1, Theorems 2.4 and 2.5, and the ordinary
Section 3 Theorems 3.3, 3.5, and 3.10 against arXiv v5 at checkpoint
`d40205b`. It does not independently certify their supporting lemmas and
corollaries, Sections 4--5, or Appendix C.

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
| #02 Learning Theory | Ordinary and prompted generation, sample-complexity interfaces, hierarchy results, Appendix C, and the Theorem 4.1 combinatorial boundary, against arXiv v5 | Partial human audit complete for Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5, and 3.10; remaining P02 scope pending |
| #06 Noisy Examples | All paper-owned qualitative statements, exposed assumptions and source repairs, and quantitative exclusions, against arXiv v2 | Pending |
| #08 Hallucination Detection | Detection/identification reductions, tell-tale and negative-example results, Appendix results, Example 1, and oracle/effectivity boundaries, against arXiv v2 | Pending |
| #28 Contrastive Generation | Deterministic statements, hierarchy and robustness coverage, and the Theorem 6.6 witness interface, against the arXiv-v1 pre-repair baseline | Pending; the named-witness repair is kernel-checked separately |
| #31 Bounded Memory | Deterministic statements, universe/order/output/indexing boundaries, and Appendix Lemma A.3, against the arXiv-v1 pre-repair baseline | Pending; the Lemma A.3 wrapper repair is kernel-checked separately |

Paper11 has a separate AI-assisted local comparison against the pinned
arXiv-v1 PDF. It has no checksum-verified ChatGPT Pro record and no completed
named human audit; human review remains pending.

Those checks did not audit theorem proof-body correctness,
establish proof correspondence, rerun Lean, certify the papers' mathematics,
or constitute a human audit. The uniform records, evidence links, and remaining human-review
slots are indexed in [`GenLimitLean/AuditRecords/Human/README.md`](GenLimitLean/AuditRecords/Human/README.md);
kernel and axiom
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

For #0 Language Identification, the next audit step is the Abstract Theorem 7.1 path, followed by
the abstract/text specialization, informant, and bridge paths.

Each development should record its source and version, formalized results,
assumptions, Lean entry points, dependencies, audit status, and known gaps.
AI-assisted contributions should remain reviewable, with clear human
responsibility for their mathematical meaning.

## References

- **#0 — Language Identification in the Limit** [\[G 67\]](https://doi.org/10.1016/S0019-9958(67)91165-5).
  E. Mark Gold. *Information and Control* 10(5), pp. 447–474, 1967.

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

- **Paper11 — On Union-Closedness of Language Generation** [\[HKMV 25\]](https://arxiv.org/abs/2506.18642v1).
  Steve Hanneke, Amin Karbasi, Anay Mehrotra, and Grigoris Velegkas.
  arXiv:2506.18642v1, 2025.
  [arXiv v1](https://arxiv.org/abs/2506.18642v1).

- **#06 — Generation from Noisy Examples** [\[RR 25\]](https://proceedings.mlr.press/v267/raman25a.html).
  Ananth Raman and Vinod Raman. *Proceedings of the 42nd International
  Conference on Machine Learning (ICML 2025)*, PMLR 267, pp. 51079--51093,
  2025.
  [Proceedings](https://proceedings.mlr.press/v267/raman25a.html) ·
  [arXiv v2](https://arxiv.org/abs/2501.04179v2).

- **#08 — (Im)possibility of Automated Hallucination Detection in Large Language Models** [\[KMSV 25\]](https://arxiv.org/abs/2504.17004v2).
  Amin Karbasi, Omar Montasser, John Sous, and Grigoris Velegkas.
  arXiv:2504.17004v2, 2025.
  [arXiv v2](https://arxiv.org/abs/2504.17004v2).

- **#28 — Contrastive Identification and Generation in the Limit** [\[LHJG 26\]](https://arxiv.org/abs/2605.06211v1).
  Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao.
  arXiv:2605.06211v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.06211v1).

- **#31 — On Language Generation in the Limit with Bounded Memory** [\[KMSV 26\]](https://arxiv.org/abs/2605.30324v1).
  Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas.
  arXiv:2605.30324v1, 2026.
  [arXiv v1](https://arxiv.org/abs/2605.30324v1) ·
  [DOI](https://doi.org/10.48550/arXiv.2605.30324).

- **#0A — Inductive Inference from Positive Data** [\[A 80\]](https://doi.org/10.1016/S0019-9958(80)90285-5).
  Dana Angluin. *Information and Control* 45(2), pp. 117--135, 1980.

- **#07 — Density Measures for Language Generation** [\[KW 25\]](https://arxiv.org/abs/2504.14370).
  Jon Kleinberg and Fan Wei. *Proceedings of the 66th IEEE Symposium on
  Foundations of Computer Science (FOCS 2025)*, pp. 620--658, 2025.
  [arXiv](https://arxiv.org/abs/2504.14370) ·
  [DOI](https://doi.org/10.1109/FOCS63196.2025.00034).

- **#15 — Partial Enumeration** [\[KW 26\]](https://arxiv.org/abs/2511.05295).
  Jon Kleinberg and Fan Wei. "Language Generation and Identification From
  Partial Enumeration: Tight Density Bounds and Topological
  Characterizations." *Proceedings of the 58th Annual ACM Symposium on Theory
  of Computing (STOC 2026)*, 2026.
  [arXiv](https://arxiv.org/abs/2511.05295) ·
  [STOC accepted paper](https://acm-stoc.org/stoc2026/accepted-papers.html).

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
