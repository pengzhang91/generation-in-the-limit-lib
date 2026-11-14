# P04 LLM 审计摘要

结论：7 个主定理声明的核心语义内容对应良好，membership-query 下界与反馈策略的已披露修补有数学依据；正向 oracle 算法的正式实现证书及若干全文附加结果仍有覆盖缺口。不是无条件的整篇论文／全部计算模型认证。

当前对象为 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。范围包括 Overview Theorems 1–5 与 Detailed Theorems 6–7；2 和 7 是同一数学命题的两个入口，分别核查但不重复计算独立命题。另盘点全部 31 页源文及 55 个 native umbrella 模块，完成 32 个比较单元。

论文为 [arXiv:2411.15364v2](https://arxiv.org/abs/2411.15364v2)。官方下载实际 SHA-256 为 `52e1f0d2111d73a2a248e7b8bdc113ee4f331e0c0478a3e5c7826b0417b7ab8b`；与 registry 旧预期字节哈希不同。本次明确固定实际官方 v2，核对其版本、标题、页码与公式，不声称取得旧哈希对应的不可用文件，也不修改 registry。详见 [源文身份](../stage2/source-identity.json)。

| 项目 | 最终裁决 |
|---|---|
| 1、6：非一致生成与显式阈值 | 核心量词、distinct-input 计数及索引转换对应；更强的语义域／输入范围合理。membership 加交集有限性 oracle 的数学实现解释可信，实际命名语义函数的正式相对计算证书仍缺。 |
| 2、7：membership-query 下界 | 在明确的 computable next-action／adaptive dialogue 模型下对应；所有轮次的有限终止条件被保留。source-proof 中“无限查询即无限不同元素”的推断不成立，已有 completion-driven 修补合理。一般机器编码的等价未单独认证。 |
| 3：regular-language 反例 | Boolean-word 见证满足源文所要求的存在性性质；不需要与论文证明中的具体整数构造相同。 |
| 4：exhaustive 刻画 | 语义等价对应；强 oracle 的正式相对实现接口仍缺，不从 Classical.choose 推出算法计算性。 |
| 5：feedback/GF 刻画 | 抽象策略层对应，允许更一般的语言类。shadow/replay 策略转换补齐源文省略的适应性论证；数值维数零边界按已说明约定解释。 |

本次裁决纠正了两种容易误判的情况。第一，被引用的有效 Angluin 定理在规范模块 `GenLimit.Angluin.theoremOne` 中存在，虽未进入第二阶段的 umbrella 输入闭包，也不能记为整个库缺失；第三阶段单独核查并记录其有效语言族前提。第二，registry 对 Example 11 称印刷 `O(i)` 需改为 `O(|i|)`，但本次官方 v2 p.30 已显示绝对值，因此对实际审阅字节不接受这项“源文符号修正”。不推断不可用旧字节的内容。

仍有实质缺口：随机化 Corollary 5.1、Propositions 6.2/6.3 的正式 oracle 实现证书、Example 11 的公开渐近速率结论，以及部分 relaxed-generation 附加命题。已有语义构造和注释不能自动填补它们。Nat／整数、有限初始轮次、输入顺序及维数空最大值等界面转换也应保留各自限定。

完整证据：

- [Lean 盲重建](code-only-reconstruction.md)、[独立论文对照](source-comparison.md)、[差异裁决](adjudication.md)。
- [总记录](audit-run-record.json)、[Stage 1 provenance](stage1-run.json)、[Stage 2 provenance](stage2-run.json)、[裁决 provenance](adjudication-run.json)、[父代理校验](parent-validation.json)、[结果校验清单](SHA256SUMS)。

前两阶段使用不同的全新上下文；第三阶段在第二阶段冻结后，由同一审计者继续读取开发者说明并独立核验其数学依据，不冒充第三次盲审。各次调用配置为 `gpt-6.1-sol` / `xhigh`，具体后端 revision 未暴露。新数学解释与运输论证均明确标为非新增 Lean 验证，不认证证明步骤或具名人类审计。

所有材料位于 non-P38 且未 git-track、stage、commit 或 push；库中 Lean、PaperMap 和 registry 未改。准备阶段 Overview 定向构建通过（1045 jobs），捕获日志没有警告。模型审计没有重新运行 Lean，也没有全仓构建。
