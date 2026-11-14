# P05 LLM 审计摘要

结论：现有语义核心对应良好，但 P05 仍是部分形式化。两条 literal stability 反定理是有数学依据、预先披露的源文规格诊断，不计为未解释的 Lean 错误；它们也不能代替论文相应的正向算法、维数条件和定量保证。整个论文不评为全部通过／完整覆盖。

范围：当前 `work/non-p38` 字节版本，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，有既存未提交工作。6 个公开结果声明均完成盲重建、独立源文对照和差异裁决；对照另盘点全文 57 个编号条目与 4 张图，检查 34 个 native umbrella 模块。论文固定为 [arXiv:2412.18530v2](https://arxiv.org/abs/2412.18530v2)，2025-07-03，46 PDF 页，SHA-256 `ba5c0de2215a156ea45791e2399487aed75e08715176d57c24e6238ce4fdd7dd`。

| 项目 | 最终裁决 |
|---|---|
| 3.3 exact breadth | 语义刻画对应；算法实现／有效访问保证另有限定。 |
| 3.8 approximate breadth | 充分方向对应；必要方向与有效实现仍缺。 |
| 3.15 stable approximate | 在 Nat 上语义等价对应；一般域运输与计算性未补齐。 |
| 3.15 literal stable exact 反定理 | 字面 fresh support 与 raw stability 不相容，诊断合理。不能把它当作论文的正向 stable exact 定理。 |
| whole-target 修正版 | 对应论文 p.17 脚注的局部允许重复样本约定。fresh／seen 两版本的存在性转换不保留 raw stability，不能静默互换。 |
| 8.10 literal stable infinite-coverage 反定理 | 字面冲突有非空、有效 oracle 的例子支持；正向修正版的有限维数、VSI 算法和 d+1 样本保证尚未提供。 |

本次裁决的一个积极修正是：P05 Definition 4.2 的非稳定 exhaustive-generation 语义刻画，已可在导入的 P04 中找到匹配接口。将它一概记为“接口实质不同、没有数学覆盖”过于保守。这里有自然的有限初始轮次转换；没有 P05 自己的包装定理不等于整个库里没有该数学结果。此结论尚非新编译的接口等价定理，也不包含有效程序保证，公共 registry 保持原样。

源文问题已经逐项核验，而不是仅采信注释。对 8.10，裁决给出两个无限可判定语言、closure dimension 恰为 1、VSI 可计算的具体例子，排除了附加前提无法满足导致的空真。关于稳定性的转换和该维数／oracle 例子均标为非 Lean 形式化的数学论证。已有反定理类型是单独的声明证据；本次没有检查其证明步骤。

仍需补充的范围包括：approximate necessity、一般 uniqueness／finite non-uniqueness 框架、统计 law／loss／rate 结果、完整 stable breadth 表、increasing coverage，以及正向算法实现等。其他论文中有相关基础不等于 P05 这些主张已有完整接口。

证据：

- [第一阶段：Lean 重建](code-only-reconstruction.md)，独立上下文、论文 withheld。
- [第二阶段：源文对照](source-comparison.md)，另一独立上下文，先盘点论文再读第一阶段。
- [第三阶段：差异裁决](adjudication.md)，第二阶段冻结后由同一审计者继续，才开放已有注释和 PaperMap；不冒充第三次独立盲审。
- [总记录](audit-run-record.json)、[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决 provenance](adjudication-run.json)、[父代理校验](parent-validation.json)、[结果校验清单](SHA256SUMS)。

模型调用均为 `gpt-6.1-sol`、`xhigh`；后端 revision 未暴露。材料、输入与结果均在 non-P38，未 git-track、stage、commit 或 push。没有修改库中 Lean、PaperMap 或 registry。准备阶段 Overview 定向构建通过（937 jobs），捕获日志没有警告；模型审计没有重新构建、没有全仓构建，也没有新增具名人类或 proof-step 审计。
