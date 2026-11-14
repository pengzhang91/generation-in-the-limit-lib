# P09 LLM 审计摘要

结论：Section 3 的主要语义构造有实质 native 支持。源文 printed Lemma 4.8／Theorem 4.4 在所给 positive-intersection finite-support 定义下确有反例；Lean 的 exact-profile 替代定理正确，但其假设与原条件互不蕴含，不能称为单纯“更强条件”。另核实 Definition 3.1 的 size-one zero 规则与 infinity 规则冲突，影响定性刻画；Lean 使用的是修复后连贯的 bounded-witness 读法。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留原有未提交工作。审计 13 个目标声明及完整 24 页源文、30 模块／887 声明；全部 14 个 paper 子模块已纳入。控制版本为 [ICML 2025 PMLR 267](https://proceedings.mlr.press/v267/peale25a.html)，官方 PDF SHA-256 `647dff8492c32479171e6acb4751a17a084407a39e502ec7ce6dfeebf9a6e61d`，与登记一致。

| 目标组 | 最终裁决 |
|---|---|
| 3.3、3.4 | bounded bad-cardinality 的主要等价对应，但必须明确修复源文不一致的 scalar dimension 定义。named generator 的 d+1 trigger 已存在；不是仅有定性包装。 |
| 3.5、3.6、3.7、3.8 | finite-class／partition、具体 infinite-universe 分离、逐 α 的递增 cover、nonuniform 与 limit 双结论均有 native 构造与组装。域和零／空例的限定保留。 |
| 4.3、4.6 | 一个与 α 无关的整数 block witness 支持印刷量词顺序，修复原证明先定 α 及非整数 block 的问题；criticality 的 eventual 结论对应。 |
| printed 4.8／4.4 counterexamples | 所有源文前提均满足，确实否定字面正结论，不是无法证明或 Lean 任意加强假设。 |
| corrected 4.8／4.4 | exact-profile 条件下的有用替代充分定理，完整 critical/feasible learner 已在 native；不计作原印刷声明的 coverage，也非必要／最小刻画。 |
| 4.9 | 在 finite adaptive transcript 后输出整份 law 的模型内，对普通 computable controller／任意 decoder 的否定对应；允许无限支持，不自动扩展到采样时继续查询 oracle 的 sampler。 |

主要反例是 H={ℕ} 与 tails A_i={m:m≥i}。每个 positive group-intersection 不是无限 tail 就是空，印刷 finite-support 总和为零。identity presentation 观察了 0,…,t−1 后，任何 fresh-supported 概率 law 都在 A_t 中质量 1，而经验质量为 0；对 α=1/2，每个正时间都不可行。此论证涵盖任意 normalized infinite-support law，countability、UUS、覆盖及完整 presentation 等前提均已核对。

反向不可蕴含也成立：两个可数不交副本中，target 取第一个副本；groups 包含全宇宙，以及“一个固定 target 点＋增长的外部有限前缀”。finite exact-profile points 只有这个固定点，但无限多个 positive intersections 各贡献 1。因而 exact-profile 条件并不推出印刷条件。PaperMap 的“stronger premise”表述应改为不同且互不蕴含的充分条件；本次未修改它。

对 dimension，取 H={ℕ\{n}:n≥2}，单组 ℕ。每个 singleton 的 closure 仍有未观察的共同点，故没有 size-one bad witness；但任何包含 {0,1} 的有限 S 都有 closure=S，故存在任意大的 bad witnesses。源文同时给出 GC=0 和 GC=∞。最小合理修复是“没有任何正大小的 bad witness 才置零”，其余取 supremum／最大值；native 的 bounded/unbounded predicates 正是连贯的定性版本。这不是仅缺一个数值 API。

其余真实边界：最小数值 dimension／optimal sample-complexity 接口尚缺；finite groups→exact-profile 的部分特例可加薄包装；源文额外的 empty-or-infinite group-intersection 正向 finite-query 算法尚未形式化。α=0 的 oracle 否定可由 α=1/4 的结果和单调性作非形式化组合，未声称已有该包装。语义生成函数不提供普通可计算 sampler 保证。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。完整 umbrella supplement 在正式 Stage 2 初始交接时已提供，所有模块核清。

前两阶段由不同新上下文完成，第三阶段为 Stage 2 冻结后同一审计者继续；父代理候选论证来源明确披露，均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。材料仅在 non-P38，未 git-track、stage、commit、push；未改 Lean、PaperMap、registry。Overview 与完整 umbrella 定向构建均通过，无警告；未运行全仓构建。新数学均标为非形式化核查，未作证明步骤审查或新增人类认证。
