# Main theorem human audit inventory

截至 2026-10-21，覆盖当前库的 **30 篇论文、232 个主结果候选组**。目标是 Level 1：定理规格和决定其含义的定义与原文的对应关系。

计数单位是 registry 的 claim group，不一定等于一个定理编号。多个版本、同一定理的分项和 overview/detailed 重述按下列范围处理。每篇的范围依据都列出；`main-text-candidates` 是保守候选范围，可在开始该篇审核时收窄。

人审状态只适用于证据明确覆盖的声明、定义和来源版本。当前记录不自动覆盖其他实现、其他版本、构造或证明。AI 检查和 Lean kernel 检查均不算 human audit。

有些已完成人审的 Lean 规格带有明确的来源限定，其形式化覆盖仍为 partial。这两件事分别记录；不会因为原论文其他分项尚未形式化，就撤销已有规格的人审。

## 版本与使用方法

数学代码基于 `fb37e6b978f56eb0bcd7b6425ed4e13b1dd9e456`；当前数学代码与该提交一致。本表包含本地审核记录更新，尚未建立 rebuttal 冻结版本。完整输入文件哈希见 [JSON](MainTheoremAudit.json)。

主结果范围由 [MainTheoremScope.json](MainTheoremScope.json) 明确列出。表格由 registry、声明索引及现有人审指纹生成，不新增任何审核结论。刷新命令：

```bash
python3 scripts/build_main_theorem_audit.py --as-of 2026-10-21
python3 scripts/build_main_theorem_audit.py --check
```

先看已有完整形式化且待首次人审的项；有旧人审的项仅续审受影响范围。部分形式化应先明确实际 Lean 规格和缺口，再审核已有部分。无原陈述形式化的项单列为 gap；反例、修正和条件性结论不能代替原陈述。

## 总数

| 人审状态 | 主结果组数 |
|---|---:|
| 已有现行人审 | 20 |
| 仅部分规格有人审 | 1 |
| 需续审 | 3 |
| 待首次人审 | 143 |
| 原陈述无形式化 | 65 |

形式化覆盖按现有注册范围统计：完整 120 组，部分 47 组，无原陈述形式化 65 组。它与上表是同一批结果的不同维度，不能相加。

待首次人审的 143 组中，97 组已有完整注册规格，46 组只有部分形式化。

已有现行人审不等于整篇 paper 已审完。仅部分规格有人审仍有未覆盖范围；无原陈述形式化包括明确不计划按字面证明的错误原陈述。

## 按论文汇总

| Paper | 候选组 | 现行人审 | 部分人审 | 续审 | 首次人审 | 无原陈述形式化 |
|---|---:|---:|---:|---:|---:|---:|
| [P00](#p00) | 8 | 0 | 0 | 1 | 2 | 5 |
| [P00A](#p00a) | 8 | 0 | 1 | 0 | 3 | 4 |
| [P01](#p01) | 4 | 2 | 0 | 0 | 1 | 1 |
| [P02](#p02) | 12 | 6 | 0 | 0 | 5 | 1 |
| [P03](#p03) | 13 | 0 | 0 | 0 | 3 | 10 |
| [P04](#p04) | 5 | 5 | 0 | 0 | 0 | 0 |
| [P05](#p05) | 18 | 0 | 0 | 0 | 4 | 14 |
| [P06](#p06) | 6 | 4 | 0 | 0 | 2 | 0 |
| [P07](#p07) | 6 | 0 | 0 | 0 | 4 | 2 |
| [P08](#p08) | 3 | 0 | 0 | 0 | 3 | 0 |
| [P09](#p09) | 8 | 0 | 0 | 0 | 7 | 1 |
| [P10](#p10) | 3 | 3 | 0 | 0 | 0 | 0 |
| [P11](#p11) | 9 | 0 | 0 | 0 | 9 | 0 |
| [P12](#p12) | 8 | 0 | 0 | 0 | 8 | 0 |
| [P13](#p13) | 7 | 0 | 0 | 0 | 6 | 1 |
| [P14](#p14) | 3 | 0 | 0 | 0 | 2 | 1 |
| [P15](#p15) | 7 | 0 | 0 | 0 | 5 | 2 |
| [P17](#p17) | 19 | 0 | 0 | 0 | 14 | 5 |
| [P18](#p18) | 6 | 0 | 0 | 0 | 5 | 1 |
| [P19](#p19) | 4 | 0 | 0 | 0 | 4 | 0 |
| [P21](#p21) | 9 | 0 | 0 | 0 | 7 | 2 |
| [P22](#p22) | 6 | 0 | 0 | 0 | 6 | 0 |
| [P23](#p23) | 6 | 0 | 0 | 0 | 0 | 6 |
| [P27](#p27) | 9 | 0 | 0 | 0 | 9 | 0 |
| [P28](#p28) | 15 | 0 | 0 | 0 | 14 | 1 |
| [P29](#p29) | 4 | 0 | 0 | 0 | 3 | 1 |
| [P30](#p30) | 4 | 0 | 0 | 0 | 4 | 0 |
| [P31](#p31) | 8 | 0 | 0 | 0 | 8 | 0 |
| [P32](#p32) | 5 | 0 | 0 | 0 | 5 | 0 |
| [P39](#p39) | 9 | 0 | 0 | 2 | 0 | 7 |

## P00

Language Identification in the Limit

范围：Main-text numbered results and the three Section 8 language-identifiability headlines; Appendix I results remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P00.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper00_LanguageIdentification.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 7.1](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 458--459 | [`gold_theorem_7_1`](../../../GenLimitLean/GenLimit/Paper00_LanguageIdentification/Abstract/Enumeration.lean#L275) | 完整（注册范围） | 待首次人审 |
| [Language Identifiability, first paragraph](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 460 | [`informantEnumerationLearner_identifiesFamily`](../../../GenLimitLean/GenLimit/Paper00_LanguageIdentification/Informant/Enumeration.lean#L170) | 完整（注册范围） | 待首次人审 |
| [Language Identifiability, second paragraph](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 460 | — | 无原陈述形式化; recursive-and-primitive-recursive-text-interfaces-not-formalized | 原陈述无形式化 |
| [Language Identifiability, third paragraph](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 460 | [`finiteLanguages_maximal_semanticallyIdentifiable`](../../../GenLimitLean/GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean#L229) | 完整（注册范围） | 需续审; [P0-arbitrary-text-semantic-level2](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P00_ArbitraryTextSemanticLevel2.json) (needs-review) |
| [Theorem 10.1 (learning-time theorem)](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 462 | — | 无原陈述形式化; learning-time-comparison-framework-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 10.1 (naming-translation theorem)](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 464 | — | 无原陈述形式化; coded-naming-relations-and-limit-recursive-translations-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Corollary 10.1](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 464 | — | 无原陈述形式化; limiting-tester-to-generator-translation-lower-bound-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 10.2](https://doi.org/10.1016/S0019-9958(67)91165-5) — Information and Control 10 (1967), pp. 447--474; p. 465 | — | 无原陈述形式化; kleene-hierarchy-and-domain-generator-translations-not-formalized | 原陈述无形式化; source: accepted-with-qualification |

表外的 9 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P00A

Inductive Inference of Formal Languages from Positive Data

范围：All five numbered theorems and three corollaries in the existing source inventory; the semantic core of effective Theorem 1 remains distinguished. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P00A.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper00A_PositiveDataInference.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 121--123 | [`theoremOne`](../../../GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L582) | 完整（注册范围） | 仅部分规格有人审; [P0A-semantic-characterization-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P0A_SemanticCharacterization.json) (current); Only the semantic characterization has a current Level 1 record. Effective Theorem 1 remains outside that record. |
| [Corollary 1](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 123 | [`corollaryOne`](../../../GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean#L598) | 完整（注册范围） | 待首次人审 |
| [Corollary 2](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 123--124 | [`corollaryTwo`](../../../GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Corollaries.lean#L609) | 完整（注册范围） | 待首次人审 |
| [Corollary 3](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 124--125 | [`corollaryThree`](../../../GenLimitLean/GenLimit/Paper00A_PositiveDataInference/Effective/Corollaries.lean#L327) | 完整（注册范围） | 待首次人审 |
| [Theorem 2](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 127--129 | — | 无原陈述形式化; condition-two-counterexample-not-formalized | 原陈述无形式化 |
| [Theorem 3](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 129--130 | — | 无原陈述形式化; halting-telltale-separation-not-formalized | 原陈述无形式化 |
| [Theorem 4](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 131--132 | — | 无原陈述形式化; conservative-inference-separation-not-formalized | 原陈述无形式化 |
| [Theorem 5](https://doi.org/10.1016/S0019-9958(80)90285-5) — Information and Control 45(2) (1980), pp. 117--135; p. 133 | — | 无原陈述形式化; conditions-three-and-five-learner-not-formalized | 原陈述无形式化 |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P01

Language Generation in the Limit

范围：The four primary result groups N1--N4 in the pinned-source inventory; the informal no-repeat strengthening is outside this main-result scope. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P01.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper01_LanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 2.1; concrete correctness equation (5.7)](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) — NeurIPS 2024 proceedings; p. 4 and 8 | [`theorem_2_1`](../../../GenLimitLean/GenLimit/Paper01_LanguageGeneration/Results/Overview.lean#L26); [`theorem_2_1_of_equiv`](../../../GenLimitLean/GenLimit/Paper01_LanguageGeneration/Results/Overview.lean#L34); 其余见 JSON | 完整（注册范围） | 已有现行人审; [P01-main-theorems-2-1-2-2-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P01_MainTheorems2_1And2_2Level1.json) (current); Current review covers the named finite-query specifications and the separately scoped round-dependent semantic route; the observed-set repair is excluded. |
| [Theorem 2.2](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) — NeurIPS 2024 proceedings; p. 4 and 13--14 | [`theorem_2_2`](../../../GenLimitLean/GenLimit/Paper01_LanguageGeneration/Results/Overview.lean#L42); [`theorem_2_2_of_equiv`](../../../GenLimitLean/GenLimit/Paper01_LanguageGeneration/Results/Overview.lean#L54); 其余见 JSON | 完整（注册范围） | 已有现行人审; [P01-main-theorems-2-1-2-2-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P01_MainTheorems2_1And2_2Level1.json) (current) |
| [Equation (4.1), with correctness equation (4.6)](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) — NeurIPS 2024 proceedings; p. 5--6 | [`kleinbergMullainathan_set_interface`](../../../GenLimitLean/GenLimit/Paper01_LanguageGeneration/SetInterface.lean#L191) | 部分; arbitrary-countable-universe-transport-not-proved | 待首次人审; The related round-dependent semantic construction has a current Level 2 record. It does not renew the literal observed-set specification or its repair.; source: accepted-with-qualification |
| [Theorem 7.1, supported by (A.1)--(A.2)](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html) — NeurIPS 2024 proceedings; p. 10 and 14--15 | — | 无原陈述形式化; p01-string-prompt-model-not-present, p01-prompted-generator-interface-not-present | 原陈述无形式化 |

表外的 1 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P02

Generation through the Lens of Learning Theory

范围：Main-text theorem and corollary cards plus Proposition 2.1; Appendix C, quantitative prose and prompt-separation lemmas remain separate supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P02.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper02_LearningTheory.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Proposition 2.1](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 7 | [`proposition_2_1`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/Introductory.lean#L22) | 部分; finite-universe-literal-reading-not-formalized | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current); The existing infinite-universe Lean specification has a completed current Level 1 review. The partial formalization flag concerns the source finite-universe literal reading, not an unfinished review of that Lean specification.; source: accepted-with-qualification |
| [Theorem 2.2](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 9 | [`theorem_2_2_countable_uus_not_identifiable`](../../../GenLimitLean/GenLimit/Bridges/GoldToPaper02.lean#L63) | 部分; finite-universe-literal-reading-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Theorem 2.3](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 9--10 | [`printed_theorem_2_3_is_false`](../../../GenLimitLean/GenLimit/Bridges/Paper02IdentificationDiagnostics.lean#L157) (refutes); [`theorem_2_3_countable`](../../../GenLimitLean/GenLimit/Bridges/AngluinToPaper02.lean#L224) (corrects) | 无原陈述形式化; source-claim-refuted | 原陈述无形式化; source: refuted |
| [Theorem 2.4](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 10 | [`theorem_2_4`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/Introductory.lean#L44) | 完整（注册范围） | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current) |
| [Theorem 2.5](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 10 | [`theorem_2_5`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/Introductory.lean#L55) | 完整（注册范围） | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current) |
| [Theorem 3.3](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 12 | [`uniform_generatability_iff_finite_closure_dimension`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/Closure.lean#L258) | 完整（注册范围） | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current); [P02-theorem-3-3-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_Theorem3_3Level1.json) (current) |
| [Theorem 3.5](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 13 | [`nonuniform_generatability_iff_nondecreasing_finite_closure_cover`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean#L145) | 完整（注册范围） | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current); [P02-theorem-3-5-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_Theorem3_5Level1.json) (current) |
| [Theorem 3.10](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 16 | [`finite_closure_dimension_cover_implies_generatable_in_limit`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/GenerationInLimitCharacterization.lean#L375) | 完整（注册范围） | 已有现行人审; [P02-named-section2-3-results](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_NamedSection2And3Results.json) (current); [P02-theorem-3-10-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P02_Theorem3_10Level1.json) (current) |
| [Theorem 4.1(i)--(vi)](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 19 | [`theorem_4_1_combinatorial_core`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/Prediction.lean#L1218) (provides-core) | 部分; literal-online-transport-not-formalized, literal-pac-transport-not-formalized, finite-universe-literal-reading-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Theorem 5.1](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 24 | [`prompted_uniform_generatability_iff_finite_prompted_closure_dimension`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedClosure.lean#L486) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 5.2](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 24 | [`prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L161) | 完整（注册范围） | 待首次人审 |
| [Corollary 5.3(i)--(iii)](https://arxiv.org/abs/2410.13714v5) — arXiv:2410.13714v5; p. 24--25 | [`countable_prompt_classes_are_nonuniformly_generatable`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L310); [`countable_prompt_classes_are_generatable_in_limit`](../../../GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L354) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |

表外的 13 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P03

On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse

范围：Section 3 Theorems 3.1--3.9 and 3.13 and Propositions 3.10--3.12; Appendix A/B statements are outside this candidate scope. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P03.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper03_HallucinationAndModeCollapse.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 27 | — | 无原陈述形式化; statistical-universal-rate-framework-not-formalized | 原陈述无形式化 |
| [Theorem 3.2](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 28 | — | 无原陈述形式化; statistical-universal-rate-framework-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 3.3](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 30 | — | 无原陈述形式化; statistical-universal-rate-framework-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 3.4](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 30 | — | 无原陈述形式化; turing-machine-model-not-formalized | 原陈述无形式化 |
| [Theorem 3.5](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 31 | [`theorem_3_5_semantic`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean#L18) (provides-core); [`repeatingBreadthInLimit_implies_identifiableInLimit`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/OnlineReductions.lean#L151) (provides-core) | 部分; repeating-positive-direction-not-formalized, turing-and-mop-realization-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Theorem 3.6 and its preceding displayed error](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 32 | — | 无原陈述形式化; statistical-universal-rate-framework-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 3.7](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 33 | [`theorem_3_7_semantic`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean#L26) (provides-core) | 部分; turing-and-mop-interface-not-formalized | 待首次人审 |
| [Theorem 3.8](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 34 | — | 无原陈述形式化; statistical-universal-rate-framework-not-formalized | 原陈述无形式化 |
| [Theorem 3.9](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 34 | [`theorem_3_9_semantic`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean#L35) (provides-core) | 部分; turing-and-mop-interface-not-formalized | 待首次人审 |
| [Proposition 3.10](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 34--35 | — | 无原陈述形式化; subset-oracle-rate-algorithm-not-formalized | 原陈述无形式化 |
| [Proposition 3.11](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 35 | [`finiteCollection_conditionTwo`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FurtherIdentification.lean#L32) (provides-core) | 无原陈述形式化; statistical-exponential-rate-not-formalized | 原陈述无形式化 |
| [Proposition 3.12](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 35 | [`finiteLanguages_conditionTwo`](../../../GenLimitLean/GenLimit/Paper03_HallucinationAndModeCollapse/FurtherIdentification.lean#L77) (provides-core) | 无原陈述形式化; statistical-exponential-rate-not-formalized | 原陈述无形式化 |
| [Theorem 3.13](https://arxiv.org/abs/2411.09642v3) — arXiv:2411.09642v3; p. 36 | — | 无原陈述形式化; labeled-statistical-rate-framework-not-formalized | 原陈述无形式化 |

表外的 4 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P04

Exploring Facets of Language Generation in the Limit

范围：Overview Theorems 1--5. Detailed Theorem 7 is the realization of overview Theorem 2, not a second audit task; quantitative Theorem 6 is supporting inventory. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P04.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper04_ExploringFacetsOfLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1](https://arxiv.org/abs/2411.15364v2) — arXiv:2411.15364v2; p. 3 | [`theorem_1`](../../../GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean#L22) | 完整（注册范围） | 已有现行人审; [P04-overview-theorems-1-4](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1To4.json) (current); [P04-overview-theorems-1-3-4-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1_3_4Level1.json) (current) |
| [Theorem 2](https://arxiv.org/abs/2411.15364v2) — arXiv:2411.15364v2; p. 3 | [`theorem_2`](../../../GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean#L31) | 完整（注册范围） | 已有现行人审; [P04-overview-theorems-1-4](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1To4.json) (current); source: accepted-with-qualification |
| [Theorem 3, overview statement and Section 5.1 restatement](https://arxiv.org/abs/2411.15364v2) — arXiv:2411.15364v2; p. 4 and 13--14 | [`theorem_3`](../../../GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean#L35) | 完整（注册范围） | 已有现行人审; [P04-overview-theorems-1-4](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1To4.json) (current); [P04-overview-theorems-1-3-4-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1_3_4Level1.json) (current) |
| [Theorem 4](https://arxiv.org/abs/2411.15364v2) — arXiv:2411.15364v2; p. 4 | [`theorem_4`](../../../GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean#L44) | 完整（注册范围） | 已有现行人审; [P04-overview-theorems-1-4](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1To4.json) (current); [P04-overview-theorems-1-3-4-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_OverviewTheorems1_3_4Level1.json) (current) |
| [Theorem 5](https://arxiv.org/abs/2411.15364v2) — arXiv:2411.15364v2; p. 5 | [`theorem_5`](../../../GenLimitLean/GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean#L53) | 完整（注册范围） | 已有现行人审; [P04-theorem-5-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P04_Theorem5Level1.json) (current) |

表外的 15 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P05

On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability

范围：Main-text theorem, proposition and corollary cards in the existing P05 result map; multi-clause characterizations remain separate claim groups. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P05.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper05_HallucinationsBreadthAndStability.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.3](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 9 | [`theorem_3_3_semantic`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L27); [`exactBreadthGeneratable_iff_conditionTwo`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/ExactBreadth.lean#L250) | 部分; effective-generator-realization-not-formalized | 待首次人审 |
| [Theorem 3.5](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 10 and 22--26 | — | 无原陈述形式化; generic-uniqueness-framework-not-formalized | 原陈述无形式化 |
| [Theorem 3.8](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 11 | [`theorem_3_8_sufficiency_semantic`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L37); [`weakAngluin_implies_approximateBreadthGeneratable`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/ApproximateBreadth.lean#L94) | 部分; necessity-direction-not-formalized, effective-generator-realization-not-formalized | 待首次人审 |
| [Theorem 3.10](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 12 and 26 | — | 无原陈述形式化; finite-non-uniqueness-framework-not-formalized | 原陈述无形式化 |
| [Theorem 4.3(1), unambiguous-generation bullet](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 16 | — | 无原陈述形式化; p05-unambiguous-generation-not-formalized | 原陈述无形式化 |
| [Theorem 4.3(2), exhaustive-generation bullet](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 16 | [`paper04_exhaustive_iff_paper05_weakAngluin`](../../../GenLimitLean/GenLimit/Bridges/Paper04ToPaper05.lean#L73) (provides-core) | 无原陈述形式化; p05-exhaustive-interface-equivalence-not-proved, effective-generator-realization-not-formalized | 原陈述无形式化 |
| [Theorem 3.15, approximate-breadth clause](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 12--13 | [`theorem_3_15_approximate_semantic`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L46); [`stableApproximateGeneratable_iff_conditionTwo`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StableApproximate.lean#L55) | 部分; arbitrary-countable-universe-transport-not-proved, effective-generator-realization-not-formalized | 待首次人审 |
| [Theorem 3.15, exact-breadth clause](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 12--13 | [`theorem_3_15_literal_exact_inconsistent`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L57) (refutes); [`no_stable_exactBreadth_for_infinite_family`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StabilityGap.lean#L72) (refutes); 其余见 JSON | 无原陈述形式化; literal-reading-countertheorem-pending-source-audit | 原陈述无形式化; source: disputed |
| [Theorem 4.5, stable unambiguous-generation bullet](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 17 | — | 无原陈述形式化; p05-stable-unambiguous-generation-not-formalized | 原陈述无形式化 |
| [Theorem 4.5, stable exhaustive-generation bullet](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 17 | — | 无原陈述形式化; stable-exhaustive-generation-not-formalized | 原陈述无形式化 |
| [Theorem 5.2](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 20 | — | 无原陈述形式化; probability-and-rate-framework-not-present | 原陈述无形式化 |
| [Theorem 5.3](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 21 | — | 无原陈述形式化; probability-and-rate-framework-not-present | 原陈述无形式化; source: accepted-with-qualification |
| [Proposition 8.4](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 35--36 | — | 无原陈述形式化; infinite-coverage-construction-not-formalized | 原陈述无形式化 |
| [Theorem 8.7](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 36--37 | [`no_stable_infiniteCoverage_for_infinite_family`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StabilityGap.lean#L134) | 部分; source-witness-family-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Proposition 8.10](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 38--39 | [`proposition_8_10_literal_specification_inconsistent`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L80) (refutes); [`no_stable_infiniteCoverage_for_infinite_family`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StabilityGap.lean#L134) (refutes) | 无原陈述形式化; literal-reading-countertheorem-pending-source-audit | 原陈述无形式化; source: disputed |
| [Corollary 8.11(1)](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 38 | [`no_stable_exactBreadth_for_infinite_family`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StabilityGap.lean#L72) (refutes); [`theorem_3_15_corrected_wholeTarget_semantic`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L68) (corrects) | 无原陈述形式化; literal-reading-countertheorem-pending-source-audit | 原陈述无形式化; source: disputed |
| [Corollary 8.11(2)](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 38 | [`proposition_8_10_literal_specification_inconsistent`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean#L80) (refutes); [`no_stable_infiniteCoverage_for_infinite_family`](../../../GenLimitLean/GenLimit/Paper05_HallucinationsBreadthAndStability/StabilityGap.lean#L134) (refutes) | 无原陈述形式化; literal-reading-countertheorem-pending-source-audit | 原陈述无形式化; source: disputed |
| [Proposition 8.14](https://arxiv.org/abs/2412.18530v2) — arXiv:2412.18530v2; p. 40 | — | 无原陈述形式化; increasing-coverage-framework-not-formalized, source-convention-requires-audit | 原陈述无形式化; source: accepted-with-qualification |

表外的 1 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P06

Generation from Noisy Examples

范围：Section 3 Theorems 3.1, 3.3, 3.9, 3.10 and Corollaries 3.4, 3.7; quantitative prose and appendix results remain separate. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P06.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper06_NoisyExamples.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 5 | [`theorem_3_1`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/UniformIndependent.lean#L275) | 完整（注册范围） | 已有现行人审; [P06-section3-theorems-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P06_Section3TheoremsLevel1.json) (current); source: accepted-with-qualification |
| [Theorem 3.3](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 6 | [`theorem_3_3`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/NoisyClosure.lean#L556) | 完整（注册范围） | 已有现行人审; [P06-section3-theorems-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P06_Section3TheoremsLevel1.json) (current); source: accepted-with-qualification |
| [Corollary 3.4](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 6 | [`corollary_3_4`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/FiniteClasses.lean#L123) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 3.7](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 7 | [`corollary_3_7`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/Nonuniform.lean#L277) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 3.9](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 8 | [`theorem_3_9`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/NoiselessRobustification.lean#L741) | 完整（注册范围） | 已有现行人审; [P06-section3-theorems-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P06_Section3TheoremsLevel1.json) (current); source: accepted-with-qualification |
| [Theorem 3.10](https://arxiv.org/abs/2501.04179v2) — arXiv:2501.04179v2; p. 8 | [`theorem_3_10`](../../../GenLimitLean/GenLimit/Paper06_NoisyExamples/FiniteUnionLimit.lean#L192) | 完整（注册范围） | 已有现行人审; [P06-section3-theorems-level1](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P06_Section3TheoremsLevel1.json) (current); source: accepted-with-qualification |

表外的 14 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P07

Density Measures for Language Generation

范围：Overview Theorems 2.1 and 2.3--2.6 and Corollary 2.2; technical truth-index, finite-rank and accounting claims remain supporting inventory. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P07.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper07_DensityMeasuresForLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1 / Overview Theorem 2.1](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | [`theorem_2_1`](../../../GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfinitelyOften.lean#L225) (corrects) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 2.2](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | [`corollary_2_2`](../../../GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/IndexLimsup.lean#L64) | 完整（注册范围） | 待首次人审 |
| [Overview Theorem 2.3](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | — | 无原陈述形式化; index-breadth-obstruction-not-formalized | 原陈述无形式化 |
| [Overview Theorem 2.4 / Theorem 4.1](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | [`claim_4_7`](../../../GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Feasible.lean#L157) (provides-core) | 部分; index-breadth-characterization-not-assembled | 待首次人审 |
| [Overview Theorem 2.5 / Theorem 5.1](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | — | 无原陈述形式化; element-upper-density-algorithm-not-formalized | 原陈述无形式化 |
| [Theorem 6.12 / Overview Theorem 2.6](https://arxiv.org/abs/2504.14370v1) — arXiv:2504.14370v1 | [`theorem_6_12_finite_accounting`](../../../GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/OneEighth.lean#L53) (provides-core); [`orderedLowerDensity_one_eighth_of_longBadCharge`](../../../GenLimitLean/GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfiniteRank/LongCharge.lean#L98) (provides-core); 其余见 JSON | 部分; dynamic-charge-bridge-open | 待首次人审; source: disputed |

表外的 4 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P08

(Im)possibility of Automated Hallucination Detection in Large Language Models

范围：Theorem 2.1 / Informal Result I, Corollary 2.2 and Theorem 2.3 / Informal Result II; Appendix results remain supporting inventory. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P08.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper08_HallucinationDetection.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 2.1](https://arxiv.org/abs/2504.17004v2) — arXiv:2504.17004v2; p. 7 | [`theorem_2_1`](../../../GenLimitLean/GenLimit/Paper08_HallucinationDetection/Reductions.lean#L237) | 完整（注册范围） | 待首次人审 |
| [Corollary 2.2](https://arxiv.org/abs/2504.17004v2) — arXiv:2504.17004v2; p. 7 | [`corollary_2_2`](../../../GenLimitLean/GenLimit/Paper08_HallucinationDetection/AngluinCondition.lean#L23) | 完整（注册范围） | 待首次人审 |
| [Theorem 2.3](https://arxiv.org/abs/2504.17004v2) — arXiv:2504.17004v2; p. 8 | [`theorem_2_3`](../../../GenLimitLean/GenLimit/Paper08_HallucinationDetection/NegativeExamples.lean#L58) | 完整（注册范围） | 待首次人审 |

表外的 14 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P09

Representative Language Generation

范围：Main-text theorems and corollaries plus Lemma 4.9, which is previewed as Lemma 1.3; other proof lemmas remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P09.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper09_RepresentativeLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.3](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 6 | [`theorem_3_3`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L31) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 3.4](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 6 | [`corollary_3_4`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L44) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 3.5](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 6 | [`corollary_3_5`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L57) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 3.6](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 6 | [`corollary_3_6`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L70) | 部分; finite-universe-literal-reading-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Theorem 3.7](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 7 | [`theorem_3_7`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L82) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 3.8](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 7 | [`corollary_3_8`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L94) | 完整（注册范围） | 待首次人审 |
| [Theorem 4.4](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 7 | [`printed_theorem_4_4_counterexample`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L147) (refutes); [`corrected_theorem_4_4`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L171) (corrects) | 无原陈述形式化; printed-finite-support-condition-disputed | 原陈述无形式化; source: disputed |
| [Lemma 4.9](https://proceedings.mlr.press/v267/peale25a.html) — ICML 2025 proceedings, PMLR 267; p. 9 | [`lemma_4_9`](../../../GenLimitLean/GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean#L185) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |

表外的 4 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P10

On Union-Closedness of Language Generation

范围：Overview Theorems 3.1--3.3; detailed Theorems 4.1, 4.3 and 4.4 are corresponding presentations, not extra audit tasks. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P10.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://arxiv.org/abs/2506.18642v1) — arXiv:2506.18642v1; p. 8 | [`theorem_3_1`](../../../GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean#L28) | 完整（注册范围） | 已有现行人审; [P10-overview-theorems-3-1-3-3](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P10_OverviewTheorems3_1To3_3.json) (current) |
| [Theorem 3.2](https://arxiv.org/abs/2506.18642v1) — arXiv:2506.18642v1; p. 9 | [`theorem_3_2`](../../../GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean#L92) | 完整（注册范围） | 已有现行人审; [P10-overview-theorems-3-1-3-3](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P10_OverviewTheorems3_1To3_3.json) (current); source: accepted-with-qualification |
| [Theorem 3.3](https://arxiv.org/abs/2506.18642v1) — arXiv:2506.18642v1; p. 9 | [`theorem_3_3`](../../../GenLimitLean/GenLimit/Paper10_UnionClosednessOfLanguageGeneration/Results/Overview.lean#L177) | 完整（注册范围） | 已有现行人审; [P10-overview-theorems-3-1-3-3](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P10_OverviewTheorems3_1To3_3.json) (current); source: accepted-with-qualification |

表外的 8 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P11

Learning Algorithms in the Limit

范围：The nine result groups explicitly designated main results by the P11 claim inventory, including Lemma 9 and Corollaries 13, 15 and 18. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P11.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper11_LearningAlgorithmsInTheLimit.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Lemma 9 (Distinguishability)](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 9, 20 | [`lemma_9_distinguishability`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L27) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 12 (Time-Restricted IOO-Learning)](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 10, 20--21 | [`theorem_12_timeRestrictedIOO_core`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L45) (provides-core); [`theorem_12_minIndex_claim_not_justified`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L62) (corrects) | 部分; q-ectt-bridge-not-formalized | 待首次人审; source: accepted-with-qualification |
| [Corollary 13](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 10 | [`corollary_13_parametrizedTMClass_core`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L70) (provides-core) | 部分; concrete-complexity-classes-not-instantiated | 待首次人审 |
| [Theorem 14 (Universal Learning with TBOs)](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 10--11, 21--22 | [`theorem_14_universalTBO_core`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L86) (provides-core) | 部分; q-ectt-bridge-not-formalized | 待首次人审 |
| [Corollary 15](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 11 | [`corollary_15_turingTBO`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L103) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 16 (Recursive-to-Rational Reduction)](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 12, 22--23 | [`theorem_16_recursiveToRational_behavior`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L113) (provides-core); [`theorem_16_rationalEnumeration_core`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L120) (provides-core) | 部分; full-tm-pto-geometry-not-modeled | 待首次人审 |
| [Theorem 17 (Unbounded Characteristic Sets)](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 12--13, 23--24 | [`theorem_17_lateSplit_characteristic_obstruction`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L140) (provides-core); [`theorem_17_mass_lower_bound_core`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L158) (provides-core) | 部分; halting-reduction-not-formalized | 待首次人审 |
| [Corollary 18](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 13 | [`corollary_18_forgetting_preserves_indistinguishability`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L178) (provides-core); [`corollary_18_characteristic_bound_lifts_to_richer_observations`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L188) (provides-core) | 部分; machine-level-non-iptd-premise-missing | 待首次人审 |
| [Theorem 21](https://proceedings.mlr.press/v291/papazov25a.html) — COLT 2025 proceedings, PMLR 291; p. 14, 24--25 | [`theorem_21_tagged_two_step`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L213) (implements-construction); [`taggedMachine_runFrom`](../../../GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean#L223) (implements-construction); 其余见 JSON | 部分; unconditional-msm-invariant-not-established | 待首次人审; source: disputed |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P12

Language Generation in the Limit: Noise, Loss, and Feedback

范围：The eight summary Theorems 1.1--1.8; detailed counterparts and algorithms are supporting inventory. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P12.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper12_NoiseLossAndFeedback.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1.1](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 2, 6--8 | [`theorem_1_1`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L221) | 完整（注册范围） | 待首次人审 |
| [Theorem 1.2](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 2 | [`theorem_1_2`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L233) (corrects) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 1.3](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 2, 9--10 | [`theorem_1_3`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L243) | 完整（注册范围） | 待首次人审 |
| [Theorem 1.4](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 3 | [`theorem_1_4`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L252) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 1.5](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 3 | [`theorem_1_5`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L266) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 1.6](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 3, 14--16 | [`theorem_1_6`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L278) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 1.7](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 3 | [`theorem_1_7`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L287) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 1.8](https://arxiv.org/abs/2507.15319v2) — arXiv:2507.15319v2; p. 3, 20 | [`theorem_1_8`](../../../GenLimitLean/GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean#L297) | 完整（注册范围） | 待首次人审 |

表外的 11 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P13

Pareto-optimal Non-uniform Language Generation

范围：The seven headline groups explicitly inventoried: overview Theorem 1 and detailed Theorems 4--9. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P13.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper13_ParetoOptimalNonuniformGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_1`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L35) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 4](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_4`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L49) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 5](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_5`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L59) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 6](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_6`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L73) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 7](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | — | 无原陈述形式化; representative-construction-open | 原陈述无形式化 |
| [Theorem 8](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_8`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L87) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 9](https://arxiv.org/abs/2510.02795v1) — arXiv:2510.02795v1 | [`theorem_9_representative_endgame`](../../../GenLimitLean/GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean#L103) (provides-core) | 部分; representative-certificate-open | 待首次人审 |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P14

A Characterization of List Language Identification in the Limit

范围：The three Section 1.1 headline Theorems 1--3. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P14.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper14_ListLanguageIdentification.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1](https://arxiv.org/abs/2511.04103v1) — arXiv:2511.04103v1; p. 3, 23--24 | [`theorem_1`](../../../GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean#L34) | 完整（注册范围） | 待首次人审 |
| [Theorem 2](https://arxiv.org/abs/2511.04103v1) — arXiv:2511.04103v1; p. 3, 17--18 | [`theorem_2`](../../../GenLimitLean/GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean#L46) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 3](https://arxiv.org/abs/2511.04103v1) — arXiv:2511.04103v1; p. 4, 18--24 | — | 无原陈述形式化; statistical-rate-development-not-formalized | 原陈述无形式化 |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P15

Language Generation and Identification From Partial Enumeration: Tight Density Bounds and Topological Characterizations

范围：Overview Theorems 1.5--1.11, keeping each detailed counterpart in the same source claim group. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P15.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper15_PartialEnumeration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Overview Theorem 1.5 / Theorem 2.1](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | [`theorem_2_1`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/FiniteScope.lean#L151) | 完整（注册范围） | 待首次人审 |
| [Overview Theorem 1.7](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | [`theorem_1_7`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/SemiIndex.lean#L58) | 完整（注册范围） | 待首次人审 |
| [Overview Theorem 1.8](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | [`theorem_1_8`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/AlgorithmOneRun.lean#L851) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 3.5 / Overview Theorem 1.6](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | [`fixedPod_finite_counting`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/PodLimit.lean#L36) (provides-core); [`alpha_half`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/PodLimit.lean#L167) (provides-core) | 部分; dynamic-pod-bridge-open | 待首次人审; source: disputed |
| [Overview Theorem 1.9 / Theorem 4.9](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | [`theorem_4_9_fullText`](../../../GenLimitLean/GenLimit/Paper15_PartialEnumeration/FullTextIdentification.lean#L159) | 完整（注册范围） | 待首次人审 |
| [Overview Theorem 1.10 / Theorem 4.12](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | — | 无原陈述形式化; ambiguous-partial-enumeration-topology | 原陈述无形式化; source: disputed |
| [Overview Theorem 1.11 / Theorem 4.13](https://arxiv.org/abs/2511.05295v1) — arXiv:2511.05295v1 | — | 无原陈述形式化; depends-on-ambiguous-partial-topology | 原陈述无形式化; source: disputed |

表外的 3 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P17

Language Generation with Infinite Contamination

范围：Main-text theorem and corollary cards, including the independent membership-query corollary; Appendix B and proof lemmas remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P17.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper17_InfiniteContamination.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Algorithm 4 and Theorem 5.1](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_5_1`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L117) (corrects); [`theorem_5_1_printed_containment_is_reversed`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/VanishingNoise.lean#L120) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 5.4](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_5_4`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L131) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.1](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_1`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L148) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.4 and Example 6.6](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_4_semantic_obstruction`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/SetDensityObstruction.lean#L138); [`theorem_6_4_half_density_instance`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/SetDensityObstruction.lean#L439); 其余见 JSON | 完整（注册范围） | 待首次人审 |
| [Theorem 6.5](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_5`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L183) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 6.11](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_11`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L203) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.14](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_14`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L218) (corrects) | 部分; source-endpoint-c-equals-one-unsupported | 待首次人审; source: accepted-with-qualification |
| [Theorem 6.15](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_15`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L236) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 6.16](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`corollary_6_16`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L265) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 6.18](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_18`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L290) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Algorithm 9 and Theorem 7.8](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_7_8`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L354) (corrects) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 1.2 / Corollary 4.5](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | — | 无原陈述形式化; machine-level-membership-query-implementation-not-formalized | 原陈述无形式化 |
| [Theorem 6.19 and Corollary 6.20](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_6_18`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L290) (provides-core) | 部分; noiseless-numerical-premises-not-fully-formalized | 待首次人审; source: accepted-with-qualification |
| [Theorem 6.21](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`exists_common_vanishingNoise_presentation`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/SharedVanishingPresentation.lean#L409) | 部分; indistinguishability-density-obstruction-not-assembled | 待首次人审 |
| [Theorem 7.6](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | — | 无原陈述形式化; bounded-displacement-identification-model-not-formalized | 原陈述无形式化 |
| [Example 7.2 and Theorem 7.7](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | — | 无原陈述形式化; source-boundedness-constant-defect, constant-noise-bounded-displacement-obstruction-not-formalized | 原陈述无形式化; source: disputed |
| [Theorem 7.9](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | — | 无原陈述形式化; bounded-displacement-density-obstruction-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 7.10](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | [`theorem_7_8`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L354) (provides-core); [`theorem_6_15`](../../../GenLimitLean/GenLimit/Paper17_InfiniteContamination/Results/Overview.lean#L236) (provides-core) | 部分; source-facing-composition-wrapper-not-present | 待首次人审 |
| [Theorem 7.11](https://arxiv.org/abs/2511.07417v1) — arXiv:2511.07417v1 | — | 无原陈述形式化; element-density-bounded-displacement-obstruction-not-formalized | 原陈述无形式化; source: accepted-with-qualification |

表外的 8 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P18

Safe Language Generation in the Limit

范围：All numbered source results in the existing inventory: Theorems 3.1, 5.1, 6.1--6.3 and Corollary 6.1. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P18.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper18_SafeLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`theorem_3_1`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L53) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 5.1](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`theorem_5_1`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L80) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 6.1](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`theorem_6_1`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L98) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Corollary 6.1](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`corollary_6_1_printed_reduction_collapses`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L127) (refutes) | 无原陈述形式化; source-proof-gap | 原陈述无形式化; source: disputed |
| [Theorem 6.2](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`theorem_6_2`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L138) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 6.3](https://arxiv.org/abs/2601.08648v2) — arXiv:2601.08648v2 | [`theorem_6_3`](../../../GenLimitLean/GenLimit/Paper18_SafeLanguageGeneration/Results/Overview.lean#L151) | 完整（注册范围） | 待首次人审 |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P19

Characterizing the Effect of Noise in Language Generation in the Limit

范围：The four explicitly designated headline Theorems 2.16--2.19. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P19.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper19_EffectOfNoise.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 2.16](https://arxiv.org/abs/2601.21237v2) — arXiv:2601.21237v2 | [`theorem_2_16`](../../../GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean#L39) | 完整（注册范围） | 待首次人审 |
| [Theorem 2.17 and Algorithm 1](https://arxiv.org/abs/2601.21237v2) — arXiv:2601.21237v2 | [`theorem_2_17`](../../../GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean#L53) | 完整（注册范围） | 待首次人审 |
| [Theorem 2.18](https://arxiv.org/abs/2601.21237v2) — arXiv:2601.21237v2 | [`theorem_2_18`](../../../GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean#L62) | 完整（注册范围） | 待首次人审 |
| [Theorem 2.19](https://arxiv.org/abs/2601.21237v2) — arXiv:2601.21237v2 | [`theorem_2_19`](../../../GenLimitLean/GenLimit/Paper19_EffectOfNoise/Results/Overview.lean#L80) | 完整（注册范围） | 待首次人审 |

表外的 4 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P21

On Generation in Metric Spaces

范围：All main-text theorem and corollary groups; Proposition D.1 is a supporting discrete-reduction result. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P21.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper21_GenerationInMetricSpaces.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_3_1_sufficiency`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L51) | 部分; source-statement-false | 待首次人审; source: disputed |
| [Corollary 3.2](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`corollary_3_2`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L76) (corrects); [`corollary_3_4`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L128) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 3.3](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_3_3_sufficiency`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L99) | 部分; source-statement-false | 待首次人审; source: disputed |
| [Theorem 3.5](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_3_5_printed_statement_is_false`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L145) (refutes) | 无原陈述形式化; source-statement-false | 原陈述无形式化; source: refuted |
| [Theorem 3.6](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_3_6`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L150) | 完整（注册范围） | 待首次人审 |
| [Theorem 4.1](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_4_1`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L162) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 4.4](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_4_4_proof_inference_is_false`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L201) (mirrors-construction); [`theorem_4_4_bilipschitz_repair`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L205) (provides-core) | 无原陈述形式化; source-proof-gap | 原陈述无形式化; source: disputed |
| [Theorem 4.6](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_4_6`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L236); [`theorem_4_7_uniform`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L246); 其余见 JSON | 完整（注册范围） | 待首次人审 |
| [Theorem 4.10](https://arxiv.org/abs/2602.07710v1) — arXiv:2602.07710v1 | [`theorem_4_10`](../../../GenLimitLean/GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean#L278) | 完整（注册范围） | 待首次人审 |

表外的 1 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P22

Language Generation with Replay: A Learning-Theoretic View of Model Collapse

范围：The six explicitly inventoried headline Theorems 4.1, 5.1, 6.1, 6.6, 7.1 and 7.3. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P22.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper22_LanguageGenerationWithReplay.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 4.1](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`theorem_4_1`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L41) | 完整（注册范围） | 待首次人审 |
| [Theorem 5.1](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`theorem_5_1`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L50) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.1](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`theorem_6_1_finite_query`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L72) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.6](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`theorem_6_6`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L79) | 完整（注册范围） | 待首次人审 |
| [Theorem 7.1](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`Theorem71Statement`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/ProperMembershipLowerBound.lean#L151) (provides-core); [`theorem_7_1_of_algorithm3`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L90) (provides-core); 其余见 JSON | 部分; missing-machine-construction, source-proof-gap | 待首次人审; source: accepted-with-qualification |
| [Theorem 7.3](https://arxiv.org/abs/2603.11784v2) — arXiv:2603.11784v2 | [`theorem_7_3`](../../../GenLimitLean/GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean#L102) | 完整（注册范围） | 待首次人审 |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P23

Validity, Sparse Holes, and Breadth in Language Generation: Banach Density, Topology, and Geometry

范围：Overview Theorems 2.2--2.5 and the two further theorem groups 5.8 and 5.9 / 7.4; structural claims remain supporting inventory. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P23.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper23_BanachDensityTopologyAndGeometry.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Overview Theorem 2.2](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; infinite-rank-adversarial-construction-not-formalized | 原陈述无形式化 |
| [Overview Theorem 2.3](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; finite-rank-dynamic-generator-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Overview Theorem 2.4](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; higher-dimensional-geometric-obstruction-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Overview Theorem 2.5](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; filtered-higher-dimensional-generation-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 5.8](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; higher-dimensional-asymptotic-density-not-formalized | 原陈述无形式化 |
| [Theorem 5.9](https://arxiv.org/abs/2604.02385v2) — arXiv:2604.02385v2 | — | 无原陈述形式化; size-sensitive-discrepancy-not-formalized | 原陈述无形式化 |

表外的 7 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P27

Language Generation with Feedback: Queries and Mistakes

范围：The nine Section 3 headline theorems and corollaries; Appendix Lemma A.8 remains an explicit supporting proof obligation. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P27.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper27_FeedbackQueriesAndMistakes.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 3.1](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_1`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L56) | 完整（注册范围） | 待首次人审 |
| [Theorem 3.2](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_2`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L66) | 完整（注册范围） | 待首次人审 |
| [Theorem 3.3](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_3`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L77) | 完整（注册范围） | 待首次人审 |
| [Theorem 3.4](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_4`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L85) | 完整（注册范围） | 待首次人审 |
| [Corollary 3.6; Corollaries A.2--A.3](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`corollary_3_6`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L95) | 完整（注册范围） | 待首次人审 |
| [Corollary 3.7; Corollaries A.4--A.5](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`corollary_3_7`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L108) | 完整（注册范围） | 待首次人审 |
| [Corollary 3.8; Theorems A.6--A.7](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`corollary_3_8`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L121) | 完整（注册范围） | 待首次人审 |
| [Theorem 3.9](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_9_set_to_element`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L135); [`theorem_3_9_of_selfLocking`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L142) | 部分; appendix-self-locking-proof-gap | 待首次人审; source: disputed |
| [Theorem 3.10](https://openreview.net/forum?id=jvfXyIcQ8a) — ICML 2026 OpenReview record jvfXyIcQ8a | [`theorem_3_10_finiteInnerCover_sufficient`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L167); [`theorem_3_10_countableInnerCover_example`](../../../GenLimitLean/GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean#L176); 其余见 JSON | 部分; theorem-3-9-dependency | 待首次人审; source: disputed |

表外的 1 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P28

Contrastive Identification and Generation in the Limit

范围：Main-text theorem and proposition groups and overview Main Result (4); definitions, examples, algorithms and appendix-only propositions remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P28.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper28_ContrastiveGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Proposition 4.2](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 6 | [`NotEliminableFrom`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Geometry.lean#L151); [`proposition_4_2`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Geometry.lean#L208) | 完整（注册范围） | 待首次人审 |
| [Theorem 4.3](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 6 | [`theorem_4_3`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Geometry.lean#L87) | 部分; named-regime-classification-not-packaged | 待首次人审 |
| [Theorem 4.7](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 7 | [`OverlappingCover`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/IdentificationGeometry.lean#L21); [`theorem_4_7_identifier_equivalence`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/IdentifierCharacterization.lean#L623); 其余见 JSON | 完整（注册范围） | 待首次人审 |
| [Theorem 5.4](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 8 | [`theorem_5_4`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/ClosureDimension.lean#L432); [`theorem_5_4_quantitative`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/ClosureDimension.lean#L419) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 5.5](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 8 | [`theorem_5_5`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/NonuniformClosure.lean#L265) | 完整（注册范围） | 待首次人审 |
| [Proposition 5.8](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 9 | [`proposition_5_8`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean#L141) | 完整（注册范围） | 待首次人审 |
| [Proposition 5.11](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 9 | [`IsEventualCore`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean#L156); [`proposition_5_11`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean#L216) | 完整（注册范围） | 待首次人审 |
| [Proposition 5.12](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 9 | [`proposition_5_12`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L149) | 完整（注册范围） | 待首次人审 |
| [Theorem 5.13](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 9 | [`contrastiveIdentification_implies_generation`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L64); [`theorem_5_13_5_14_punctured_witness`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L316); 其余见 JSON | 部分; contrastive-generation-to-text-generation-link-missing, text-identification-strictness-wrapper-missing, text-identification-to-text-generation-strictness-missing | 待首次人审 |
| [Theorem 5.14](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 10 | [`theorem_5_13_5_14_punctured_witness`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean#L316); [`theorem_5_13_5_14_disjoint_witness`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DisjointHierarchy.lean#L178) | 完整（注册范围） | 待首次人审 |
| [Proposition 6.3](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 10 | [`positiveDefectSet`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DefectInfimum.lean#L39); [`defectNumber`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/DefectInfimum.lean#L43); 其余见 JSON | 完整（注册范围） | 待首次人审 |
| [Main Result (4), robustness reversal under corruption](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 3 | — | 无原陈述形式化; general-infinite-defect-theorem-not-stated, co-singleton-defect-formulas-not-packaged | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 6.5](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 10--11 | [`coSingletonFamily`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean#L79); [`theorem_6_5`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean#L111) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.6](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 11 | [`absenceCountIdentifier_finitely_identifies`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/AbsenceCount.lean#L408) | 完整（注册范围） | 待首次人审 |
| [Theorem 6.8](https://arxiv.org/abs/2605.06211v1) — arXiv:2605.06211v1; p. 11 | [`theorem_6_8`](../../../GenLimitLean/GenLimit/Paper28_ContrastiveGeneration/CorruptedIncomparability.lean#L488) | 完整（注册范围） | 待首次人审 |

表外的 12 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P29

Mistake-Bounded Language Generation

范围：The four numbered headline Theorems 4.1, 5.1, 6.1 and 6.4. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P29.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper29_MistakeBoundedLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 4.1](https://arxiv.org/abs/2605.10809v1) — arXiv:2605.10809v1 | [`theorem_4_1`](../../../GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean#L42) | 部分; source-claim-underspecified | 待首次人审; source: corrected |
| [Theorem 5.1](https://arxiv.org/abs/2605.10809v1) — arXiv:2605.10809v1 | [`theorem_5_1`](../../../GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean#L71) | 部分; source-convention-requires-audit | 待首次人审; source: corrected |
| [Theorem 6.1](https://arxiv.org/abs/2605.10809v1) — arXiv:2605.10809v1 | [`theorem_6_1`](../../../GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean#L106) (corrects) | 完整（注册范围） | 待首次人审; source: corrected |
| [Theorem 6.4](https://arxiv.org/abs/2605.10809v1) — arXiv:2605.10809v1 | [`theorem_6_4_proof_diagnostic`](../../../GenLimitLean/GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean#L181) (provides-core) | 无原陈述形式化; source-claim-underspecified | 原陈述无形式化; source: disputed |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P30

A Theory of Time-Sensitive Language Generation: Sparse Hallucination Beats Mode Collapse

范围：The four numbered main-text headline Theorems 1--4. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P30.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper30_TimeSensitiveLanguageGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1](https://arxiv.org/abs/2605.11302v2) — arXiv:2605.11302v2 | [`theorems_1_2_pathwise_counting_core`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean#L49) (provides-core) | 部分; randomized-almost-sure-layer-open | 待首次人审; source: accepted-with-qualification |
| [Theorem 2](https://arxiv.org/abs/2605.11302v2) — arXiv:2605.11302v2 | [`theorems_1_2_pathwise_counting_core`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean#L49) (provides-core) | 部分; randomized-almost-sure-layer-open | 待首次人审; source: accepted-with-qualification |
| [Theorem 3](https://arxiv.org/abs/2605.11302v2) — arXiv:2605.11302v2 | [`appendix_D_rate_core`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean#L72) (provides-core); [`lemma_2_density_endgame`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean#L60) (provides-core) | 部分; joint-randomized-process-open | 待首次人审 |
| [Theorem 4 and Appendix Theorem 12](https://arxiv.org/abs/2605.11302v2) — arXiv:2605.11302v2 | [`appendix_E_accurate_oracle_from_paper07`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/AccurateBridge.lean#L25) (provides-core); [`theorem_4_density_endgame`](../../../GenLimitLean/GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean#L101) (provides-core); 其余见 JSON | 完整（注册范围） | 待首次人审; source: corrected |

表外的 0 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P31

On Language Generation in the Limit with Bounded Memory

范围：Main-text theorem cards including the informal Theorem 1.2 counterparts; standalone Facts, proof lemmas and Appendix A remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P31.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper31_BoundedMemory.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 1.1](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 4, 13 | [`MemorylessSetGenerator`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/Definitions.lean#L23); [`FinitelyRepeating`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/Definitions.lean#L47); 其余见 JSON | 部分; intrinsically-infinite-codomain-not-formalized, countable-universe-transport-not-formalized | 待首次人审 |
| [Theorem 3.1](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 14 | [`singletonCore`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/Definitions.lean#L68); [`theorem_3_1`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/ArbitraryRepetitions.lean#L138) | 部分; one-example-full-memory-interface-not-formalized | 待首次人审 |
| [Theorem 3.2](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 14 | [`theorem_3_2_element`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/OutputSeparations.lean#L393); [`theorem_3_2_index`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/OutputSeparations.lean#L529) | 完整（注册范围） | 待首次人审 |
| [Theorem 4.2](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 18 | [`theorem_4_2_no_uniform_positive_lower_density`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L401) (provides-core) | 部分; fixed-global-order-hard-instance-not-formalized | 待首次人审 |
| [Informal Theorem 1.2(1)](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 5 | [`memorylessSpernerValue_guaranteed`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean#L144) | 部分; fixed-global-order-upper-bound-not-formalized, countable-universe-transport-not-formalized | 待首次人审 |
| [Informal Theorem 1.2(2)](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 5 | [`windowSpernerValue_guaranteed`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/WindowHardInstance.lean#L985) | 部分; fixed-global-order-upper-bound-not-formalized, countable-universe-transport-not-formalized | 待首次人审 |
| [Informal Theorem 1.2(3)](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 5 | [`theorem_4_15_adaptive_buffer_lower_bound`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/AdaptiveBuffer.lean#L1102) | 部分; countable-universe-transport-not-formalized, buffer-memoryless-comparison-not-packaged | 待首次人审 |
| [Theorem 1.3](https://arxiv.org/abs/2605.30324v1) — arXiv:2605.30324v1; p. 6 | [`theorem_5_2`](../../../GenLimitLean/GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean#L546) | 完整（注册范围） | 待首次人审 |

表外的 20 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P32

Generating in the Limit with Infinitely Many Hallucinations

范围：Main-text theorem and proposition groups; appendix-only statements and proof lemmas remain supporting inventory. (`main-text-candidates`)

依据：[registry](../../../registry/papers/P32.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper32_InfinitelyManyHallucinations.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| [Theorem 2.1](https://arxiv.org/abs/2606.28354v1) — arXiv:2606.28354v1 | [`lemma_2_2`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L49) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Proposition 2.4](https://arxiv.org/abs/2606.28354v1) — arXiv:2606.28354v1 | [`proposition_2_4_single_step`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L52); [`proposition_2_4_constant_step`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L55); 其余见 JSON | 完整（注册范围） | 待首次人审 |
| [Theorem 3.5](https://arxiv.org/abs/2606.28354v1) — arXiv:2606.28354v1 | [`theorem_3_5_fixed_pod_endgame`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L89) (provides-core) | 部分; dynamic-pod-bridge-open, matching-upper-bound-open | 待首次人审; source: accepted-with-qualification |
| [Theorem 4.3](https://arxiv.org/abs/2606.28354v1) — arXiv:2606.28354v1 | [`theorem_4_3`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L68) | 完整（注册范围） | 待首次人审; source: accepted-with-qualification |
| [Theorem 4.8](https://arxiv.org/abs/2606.28354v1) — arXiv:2606.28354v1 | [`theorem_4_8_of_trace_certificate`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L78); [`theorem_4_9_of_trace_certificate`](../../../GenLimitLean/GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean#L83) | 部分; safe-pod-trace-open | 待首次人审; source: accepted-with-qualification |

表外的 5 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## P39

Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms

范围：The deterministic upper bound and two achievability results from the earlier manuscript, their distinct public-v1 cards, and the four public-v1 randomized or multi-order headlines. Source editions are not merged. (`existing-headline-scope`)

依据：[registry](../../../registry/papers/P39.json)；[PaperMap](../../../GenLimitLean/PaperMaps/Paper39_DenseGeneration.md)。

| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |
|---|---|---|---|
| Discussion following Definition 2.2 — Earlier manuscript supplied for formalization; p. 7 | — | 无原陈述形式化; deterministic-upper-bound-not-formalized | 原陈述无形式化 |
| Theorem 3.14 (Lower Density) — Earlier manuscript supplied for formalization; p. 16 | [`patientScope_lowerDensity_half`](../../../GenLimitLean/GenLimit/Paper39_DenseGeneration/Patient/Main.lean#L36) | 完整（注册范围） | 需续审; [P39-exact-presentation-main](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P39_ExactPresentationMain.json) (needs-review) |
| [Theorem 3.14 (Lower Density)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 16--17 | — | 无原陈述形式化; public-v1-patient-scope-interface-not-formalized, deterministic-optimality-upper-bound-not-formalized | 原陈述无形式化 |
| Theorem 3.17 (Lower Density from Partial Enumeration) — Earlier manuscript supplied for formalization; p. 18--19 | [`theorem_3_17`](../../../GenLimitLean/GenLimit/Paper39_DenseGeneration/Partial/Main.lean#L63) | 完整（注册范围） | 需续审; [P39-partial-enumeration-level2](../../../GenLimitLean/AuditRecords/Human/Fingerprints/P39_PartialEnumerationLevel2.json) (needs-review); source: accepted-with-qualification |
| [Theorem 3.19 (Lower Density from Partial Enumeration)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 19 | — | 无原陈述形式化; public-v1-partial-density-proof-not-formalized, public-v1-patient-scope-interface-not-formalized | 原陈述无形式化; source: accepted-with-qualification |
| [Theorem 4.2 (Lower Density of a Randomized Algorithm, Lower Bound)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 20 | — | 无原陈述形式化; randomized-density-framework-not-formalized | 原陈述无形式化 |
| [Theorem 4.4 (Lower Density of a Randomized Algorithm, Upper Bound)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 20 | — | 无原陈述形式化; randomized-density-upper-bound-not-formalized | 原陈述无形式化 |
| [Theorem 5.2 (Lower Density under k Orders)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 29 | — | 无原陈述形式化; multi-order-density-framework-not-formalized | 原陈述无形式化 |
| [Theorem 5.9 (Lower Density of a Randomized Algorithm under k Orders)](https://arxiv.org/abs/2608.01320v1) — arXiv:2608.01320v1; p. 35 | — | 无原陈述形式化; multi-order-randomized-density-framework-not-formalized | 原陈述无形式化 |

表外的 14 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。

## 形式化缺口索引

下列结果无原陈述形式化。部分项有修正、反例或语义核心；是否需要补齐应按 source assessment、disposition 和缺失组件判断，不自动成为证明任务。

| Paper | 来源结果 | 处理性质 | Claim ID |
|---|---|---|---|
| [P00](#p00) | Language Identifiability, second paragraph | out-of-current-scope; source: no-known-issue | `claim:g67:countable-classes-ineffectively-identifiable-from-effective-texts` |
| [P00](#p00) | Theorem 10.1 (learning-time theorem) | out-of-current-scope; source: accepted-with-qualification | `claim:g67:enumeration-learning-time-pareto-optimality` |
| [P00](#p00) | Theorem 10.1 (naming-translation theorem) | out-of-current-scope; source: accepted-with-qualification | `claim:g67:limit-recursive-naming-translation-preserves-identifiability` |
| [P00](#p00) | Corollary 10.1 | out-of-current-scope; source: accepted-with-qualification | `claim:g67:no-limit-recursive-tester-to-generator-translation` |
| [P00](#p00) | Theorem 10.2 | out-of-current-scope; source: accepted-with-qualification | `claim:g67:no-two-recursive-domain-complement-translation` |
| [P00A](#p00a) | Theorem 2 | out-of-current-scope; source: no-known-issue | `claim:a80:condition-two-not-sufficient` |
| [P00A](#p00a) | Theorem 3 | out-of-current-scope; source: no-known-issue | `claim:a80:halting-tell-tales-not-necessary` |
| [P00A](#p00a) | Theorem 4 | out-of-current-scope; source: no-known-issue | `claim:a80:conservative-inference-separation` |
| [P00A](#p00a) | Theorem 5 | out-of-current-scope; source: no-known-issue | `claim:a80:conditions-three-and-five-conservative-inference` |
| [P01](#p01) | Theorem 7.1, supported by (A.1)--(A.2) | out-of-current-scope; source: no-known-issue | `claim:km24:robust-prompt-generation` |
| [P02](#p02) | Theorem 2.3 | not-planned; source: refuted | `claim:lrt25:printed-tell-tale-characterization` |
| [P03](#p03) | Theorem 3.1 | out-of-current-scope; source: no-known-issue | `claim:kmv25:positive-identification-rate-dichotomy` |
| [P03](#p03) | Theorem 3.2 | out-of-current-scope; source: accepted-with-qualification | `claim:kmv25:consistent-generation-exponential-rate` |
| [P03](#p03) | Theorem 3.3 | out-of-current-scope; source: accepted-with-qualification | `claim:kmv25:breadth-statistical-rate-separation` |
| [P03](#p03) | Theorem 3.4 | out-of-current-scope; source: no-known-issue | `claim:kmv25:token-by-token-mop-decidable` |
| [P03](#p03) | Theorem 3.6 and its preceding displayed error | out-of-current-scope; source: accepted-with-qualification | `claim:kmv25:statistical-stable-unambiguous-impossibility` |
| [P03](#p03) | Theorem 3.8 | out-of-current-scope; source: no-known-issue | `claim:kmv25:statistical-stable-approximate-breadth-impossibility` |
| [P03](#p03) | Proposition 3.10 | out-of-current-scope; source: no-known-issue | `claim:kmv25:subset-oracle-exponential-identification` |
| [P03](#p03) | Proposition 3.11 | out-of-current-scope; source: no-known-issue | `claim:kmv25:finite-collection-exponential-identification` |
| [P03](#p03) | Proposition 3.12 | out-of-current-scope; source: no-known-issue | `claim:kmv25:finite-language-exponential-identification` |
| [P03](#p03) | Theorem 3.13 | out-of-current-scope; source: no-known-issue | `claim:kmv25:positive-negative-exponential-identification` |
| [P05](#p05) | Theorem 3.5 | out-of-current-scope; source: no-known-issue | `claim:kmv24b:uniqueness-lower-bound` |
| [P05](#p05) | Theorem 3.10 | out-of-current-scope; source: no-known-issue | `claim:kmv24b:finite-non-uniqueness-lower-bound` |
| [P05](#p05) | Theorem 4.3(1), unambiguous-generation bullet | out-of-current-scope; source: no-known-issue | `claim:kmv24b:unambiguous-generation-characterization` |
| [P05](#p05) | Theorem 4.3(2), exhaustive-generation bullet | out-of-current-scope; source: no-known-issue | `claim:kmv24b:exhaustive-generation-characterization` |
| [P05](#p05) | Theorem 3.15, exact-breadth clause | not-planned; source: disputed | `claim:kmv24b:literal-stable-exact-characterization` |
| [P05](#p05) | Theorem 4.5, stable unambiguous-generation bullet | out-of-current-scope; source: no-known-issue | `claim:kmv24b:stable-unambiguous-characterization` |
| [P05](#p05) | Theorem 4.5, stable exhaustive-generation bullet | out-of-current-scope; source: no-known-issue | `claim:kmv24b:stable-exhaustive-characterization` |
| [P05](#p05) | Theorem 5.2 | out-of-current-scope; source: no-known-issue | `claim:kmv24b:exact-breadth-statistical-rates` |
| [P05](#p05) | Theorem 5.3 | out-of-current-scope; source: accepted-with-qualification | `claim:kmv24b:approximate-breadth-statistical-rates` |
| [P05](#p05) | Proposition 8.4 | out-of-current-scope; source: no-known-issue | `claim:kmv24b:universal-infinite-coverage` |
| [P05](#p05) | Proposition 8.10 | not-planned; source: disputed | `claim:kmv24b:finite-closure-stable-infinite-coverage` |
| [P05](#p05) | Corollary 8.11(1) | not-planned; source: disputed | `claim:kmv24b:finite-family-stable-exact-corollary` |
| [P05](#p05) | Corollary 8.11(2) | not-planned; source: disputed | `claim:kmv24b:finite-family-stable-infinite-coverage-corollary` |
| [P05](#p05) | Proposition 8.14 | out-of-current-scope; source: accepted-with-qualification | `claim:kmv24b:strictly-increasing-infinite-coverage-separation` |
| [P07](#p07) | Overview Theorem 2.3 | out-of-current-scope; source: no-known-issue | `claim:kw25density:theorem-2-3` |
| [P07](#p07) | Overview Theorem 2.5 / Theorem 5.1 | out-of-current-scope; source: no-known-issue | `claim:kw25density:theorem-2-5` |
| [P09](#p09) | Theorem 4.4 | not-planned; source: disputed | `claim:prr25:printed-finite-support-limit-sufficiency` |
| [P13](#p13) | Theorem 7 | planned; source: no-known-issue | `claim:cp25pareto:theorem-7-representative-times` |
| [P14](#p14) | Theorem 3 | planned; source: no-known-issue | `claim:cpt25:statistical-rates` |
| [P15](#p15) | Overview Theorem 1.10 / Theorem 4.12 | out-of-current-scope; source: disputed | `claim:kw26partial:theorem-1-10` |
| [P15](#p15) | Overview Theorem 1.11 / Theorem 4.13 | out-of-current-scope; source: disputed | `claim:kw26partial:theorem-1-11` |
| [P17](#p17) | Corollary 1.2 / Corollary 4.5 | deferred; source: no-known-issue | `claim:mvyz25:corollary-4-5` |
| [P17](#p17) | Theorem 7.6 | deferred; source: no-known-issue | `claim:mvyz25:theorem-7-6` |
| [P17](#p17) | Example 7.2 and Theorem 7.7 | deferred; source: disputed | `claim:mvyz25:theorem-7-7` |
| [P17](#p17) | Theorem 7.9 | deferred; source: accepted-with-qualification | `claim:mvyz25:theorem-7-9` |
| [P17](#p17) | Theorem 7.11 | deferred; source: accepted-with-qualification | `claim:mvyz25:theorem-7-11` |
| [P18](#p18) | Corollary 6.1 | deferred; source: disputed | `claim:aak26:corollary-6-1` |
| [P21](#p21) | Theorem 3.5 | not-planned; source: refuted | `claim:lrt26:theorem-3-5` |
| [P21](#p21) | Theorem 4.4 | deferred; source: disputed | `claim:lrt26:theorem-4-4` |
| [P23](#p23) | Overview Theorem 2.2 | deferred; source: no-known-issue | `claim:kw26banach:theorem-4-1` |
| [P23](#p23) | Overview Theorem 2.3 | deferred; source: accepted-with-qualification | `claim:kw26banach:theorem-4-5` |
| [P23](#p23) | Overview Theorem 2.4 | deferred; source: accepted-with-qualification | `claim:kw26banach:theorem-5-1` |
| [P23](#p23) | Overview Theorem 2.5 | deferred; source: accepted-with-qualification | `claim:kw26banach:theorem-5-5` |
| [P23](#p23) | Theorem 5.8 | deferred; source: no-known-issue | `claim:kw26banach:theorem-5-8` |
| [P23](#p23) | Theorem 5.9 | deferred; source: no-known-issue | `claim:kw26banach:theorem-5-9` |
| [P28](#p28) | Main Result (4), robustness reversal under corruption | candidate; source: accepted-with-qualification | `claim:lhjg26:overview-infinite-defect-identification` |
| [P29](#p29) | Theorem 6.4 | deferred; source: disputed | `claim:kpr26:mistake-convergence-tradeoff` |
| [P39](#p39) | Discussion following Definition 2.2 | out-of-current-scope; source: no-known-issue | `claim:clswz26:earlier-deterministic-upper-bound` |
| [P39](#p39) | Theorem 3.14 (Lower Density) | out-of-current-scope; source: no-known-issue | `claim:clswz26:v1-deterministic-half-density` |
| [P39](#p39) | Theorem 3.19 (Lower Density from Partial Enumeration) | out-of-current-scope; source: accepted-with-qualification | `claim:clswz26:v1-partial-enumeration-density` |
| [P39](#p39) | Theorem 4.2 (Lower Density of a Randomized Algorithm, Lower Bound) | out-of-current-scope; source: no-known-issue | `claim:clswz26:v1-randomized-one-minus-inv-e-achievability` |
| [P39](#p39) | Theorem 4.4 (Lower Density of a Randomized Algorithm, Upper Bound) | out-of-current-scope; source: no-known-issue | `claim:clswz26:v1-randomized-one-minus-inv-e-upper-bound` |
| [P39](#p39) | Theorem 5.2 (Lower Density under k Orders) | out-of-current-scope; source: no-known-issue | `claim:clswz26:v1-multi-order-deterministic-half-density` |
| [P39](#p39) | Theorem 5.9 (Lower Density of a Randomized Algorithm under k Orders) | out-of-current-scope; source: no-known-issue | `claim:clswz26:v1-multi-order-randomized-one-minus-inv-e` |
