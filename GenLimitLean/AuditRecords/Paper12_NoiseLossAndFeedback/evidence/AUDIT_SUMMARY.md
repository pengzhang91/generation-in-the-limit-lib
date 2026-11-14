# P12 LLM 审计摘要

结论：八项主结果在论文的确定性语义模型下均有 native 声明支持。部分 Overview 包装较简略；反馈预算和 Algorithm 4 的逐轮行为需要保留限定，不能把最终定理对应说成程序完全相同。发现的源文证明措辞与局部论证问题已有合理修正，不构成相应主定理失败的证据。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。审计 8 个目标声明，并盘点完整 23 页论文、77 模块 native umbrella。[arXiv:2507.15319v2](https://arxiv.org/abs/2507.15319v2) 官方 PDF SHA-256 为 `ef6dc568b5815b6fe052c5dd52bef89d01a1d7d4eed86e946c368305078c42e5`，与登记版本一致。

| 目标 | 裁决 |
|---|---|
| 1.1 | 两个自主生成正例及联合失败均对应。native 使用不同且第一类可数的见证；符合存在性定理，不主张与论文具体构造相同。 |
| 1.2–1.4 | 噪声与自主生成等价、递增无限交集 cover、同一生成器容忍无限遗漏均对应，保留全部量词和阈值依赖。有限前缀补全的修正经数学检查支持。 |
| 1.5 | 同一个整数语言族同时分离相邻噪声和遗漏等级，包含无限性及四项性质。源文遗漏证明应使用 i+1 遗漏的前提，并修正包含零的错误不变量。 |
| 1.6 | Overview 未显式绑定见证无限性，但 `unknownFiniteNoiseClass_uus` 与 `theorem_1_6_with_uus` 已对同一命名类提供完整结果；不是底层数学缺失。 |
| 1.7 | strictness、所有类／所有预算的有限反馈等价、无限反馈的 cover 结果均有 native 声明。非法回答历史的预算谓词不逐控制器等价；类级保证可由因果归一化保持。 |
| 1.8 | 语义识别对应，native 另证明稳定到最小同义名称；非空可数类有完整索引包装。重复名称不构成缺口。 |

反馈差异分两层。固定控制器可以仅在非法回答历史上无限查询，因此论文“任意回答序列”的字面预算约束与 native 的合法协议历史约束不同。审计给出递归清理回答的因果包装：弃权轮强制 `none`，查询轮强制 Boolean 回答；任意原始历史因此映射到兼容历史，并在真实执行上保持查询、输出和阈值。该类级等价论证是非形式化数学检查，尚无新增 Lean 归一化引理。

Algorithm 4 的 native optional→mandatory 转换确实证明两个 native 程序输出相同，但这不是与论文伪代码逐轮相同的证明。native 在等待／跳过时输出 0、跳过消耗一轮，并用当前样本作入口判断；论文的等待输出、即时跳过和判断时点不同。已有 eventual 生成结论仍明确存在，宜称“改变轮次记账的语义实现”。

源文 6.3 证明中孤立的“uniformly”不能升级 displayed eventual 定理。对全体余有限自然数语言，任意共同有限轮次及查询记录都可由某个目标实现，同时令当轮输出已观察或落在目标之外；该类又是单元素一致可生成类的可数并。这给出非形式化反例，支持把孤立措辞改为 eventual。有限反馈证明的树边方向、Appendix A 的阈值类型和 `T+1` distinct-count 记账也作了局部核查。

没有发现缺失的 native 主结果成分。后续最小工作是修正文档中的程序同一性表述，并可补显式反馈归一化引理；本次没有修改源码或登记。

证据：[Lean 盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验清单](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。Stage 1 收到仅含代码的显式类型补充后修订；此前草稿的原始字节已精确复原并留存，具体时序在 Stage 1 记录中披露。

前两阶段由不同全新上下文完成，第三阶段在 Stage 2 冻结后由同一审计者继续；均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。所有新增材料仅在 non-P38，未 git-track、stage、commit 或 push；未修改库中 Lean、PaperMap、registry。准备阶段 Overview 定向构建通过（1429 jobs），日志无警告；审计未新增全仓构建、证明步骤审计或人类认证。
