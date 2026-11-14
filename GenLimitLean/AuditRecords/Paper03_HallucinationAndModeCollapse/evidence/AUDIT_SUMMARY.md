# P03 Overview：两阶段 LLM 声明审计摘要

结论（加入差异裁决后）：P03 的核心语义数学与已明示的 oracle 构造总体对应良好。Theorem 3.6 属于有依据的源文修正；无限目标假设符合论文上下文；计算模型对应则保留已说明的条件和源文解释问题。13 个目标声明均已覆盖，但不能把整个 Overview 标为无条件逐字等价／全部通过。完成状态与数学 verdict 分开，也不表示新增证明或人类认证。

审计对象是 `work/non-p38` 工作树中当前字节版本的 `GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview`：Theorems 3.1–3.9、Propositions 3.10–3.12、Theorem 3.13。记录 HEAD 为 `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，工作树有既存未提交修改，因此实际版本由冻结输入的 SHA-256 确定。96 个 Lean／配置输入在收尾时仍与当前 non-P38 工作树逐字节一致。输入没有 P38 依赖；该工作树也没有 Paper38 formalization 或 P38 registry 条目。

论文固定为 arXiv:2411.09642v3（2025-10-14），98 页，PDF SHA-256 为 `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`。报告页码同时标注论文印刷页与 PDF 页。

| 事项 | 审计结论 |
|---|---|
| 3.6 的 unambiguity loss | 有依据的源文修正：已有 Lean 注释和 PaperMap 明确披露成功／失败互补。新增非形式化反例满足无限语言、不可识别、稳定、普通可计算且 MOP 可判定等前提，显示印刷 success-loss 的不可能性字面结论不成立。支持保留 Lean 的 failure-loss；仍不称为字面等价，也不消除独立计算模型限定。 |
| 3.1，以及使用 nonidentifiability 的 3.3、3.5–3.9 | Lean 的 `IdentifiableInLimit` 是任意函数意义下的语义可识别性，`ConditionTwo` 是有限 tell-tale 的存在。论文涉及可计算学习器和 oracle／枚举程序，但对其计算能力约定并不始终明确。负向结论一方面覆盖更多非计算学习器，另一方面语义 nonidentifiability 会缩小适用语言族；不能用一个“更强／更弱”标签概括。 |
| 3.3、3.5 的正向 breadth | Lean 明确给出语义构造、oracle MOP 与有条件的普通计算性。普通 MOP 的证书要求可计算的 family membership；统一采样器及 uniform MOP 证书还要求可计算的 tell-tale emission。3.3 同时给出同一个生成器的精确指数速率，强于论文正向 almost-exponential 速率部分。统计强度与计算保证必须分开比较。 |
| MOP 的 pointwise／uniform 区分 | Lean `DecidableMOP` 与论文 Definition 6 的字面量词顺序一致：每个训练历史分别存在判定器。因此不能把它直接报为 Lean 漏掉 uniform 假设。论文某些归约怎样统一调用这些判定器仍是源文模型问题。 |
| 无限语言假设 | 论文 p.2 / PDF 5 明确说 fresh generation 的目标必须无限。Lean `OracleFamily` 对 3.2、3.3、3.5 使用无限语言，符合这一上下文。初稿遗漏该段，经复核修正；不把它列为无依据的新限制。 |
| 其余对应较清楚的部分 | 3.4 的终止词支持判定、3.10 的 subset-oracle 识别、3.11 的有限语言族、3.12 的逐个有限语言、3.13 的带标签学习，核心数学任务对应清楚，并有具体见证、推广或更强下界。编码、oracle 相对计算等限定见逐项报告；这不意味着整个声明无条件逐字等价。 |

第二阶段还记录了两个较细的边界。其一，引言的 support-failure loss 与对单次随机输出取平均的错误概率通常不同；3.2 的显式确定性见证使二者相同，3.3 泛化的存在量词接口本身没有同时打包确定性／support-risk 证书。其二，3.7 第一阶段的一句自然语言把“并非对所有枚举流都最终成功”写成了“对所有流都失败”；其量词公式本来正确，第二阶段已明确纠正为存在某个坏目标及枚举流，未改写冻结的第一阶段原件。

流程和独立性：两个主阶段均通过 `fork_turns=none` 的新上下文运行，配置为 **gpt-6.1-sol，xhigh**。第一阶段只接收 Lean 类型与定义材料，未获论文、PaperMap 或旧审计；标识符仍可见，因此属于 paper-withheld，而非匿名化审计。其报告冻结后，第二阶段先独立盘点论文，再读取第一阶段重建并复查关键 Lean 定义。第二阶段初稿完成后，协调者提供遗漏的 p.2 源文位置和一个全无限语言的例子变体；审计者独立核验后修订，并在 provenance 中披露。另有同配置、独立上下文的计算模型专项复核，未读取第二阶段报告或旧审计。模型后端具体 revision 未暴露；本记录仅保证调用配置，不声称知道服务端权重版本。

后续按用户认可的 [workflow v2](../../workflow-v2/README.md) 增加了“差异裁决”，阅读并核验了已有注释和 PaperMap；不是重跑独立两阶段。前两阶段和计算性专项复核仍原样冻结。本次协调者裁决的实际模型配置、已知上下文、补充说明版本及非形式化论证状态另行记录。

完整证据：

- [差异裁决与逐项最终处置](adjudication.md)、[裁决 provenance](adjudication-run.json)。
- [第一阶段：Lean → 自然语言](code-only-reconstruction.md)，覆盖全部 13 个目标及依赖定义。
- [第二阶段：论文对照](source-comparison.md)，13 个声明档案、28 个对照单元、完整正向证书拆解及差异说明。
- [计算模型独立复核](computation-scope-review.md)，重点核查 3.1、3.3、3.5；其中三个分离例子明确标为非 Lean 验证的数学说明。
- [总运行记录](audit-run-record.json)、[第一阶段 provenance](stage1-run.json)、[第二阶段 provenance](stage2-run.json)、[专项复核 provenance](computation-scope-run.json)、[协调者验证记录](parent-validation.json)。
- [结果 SHA-256 清单](SHA256SUMS)。它覆盖 `results/` 下除自身外的最终文件；原始输入校验清单继续保持不变。

原始 `record.json`、材料包根 README 和 `results/README.md` 保留准备阶段的历史状态，不覆盖冻结输入。当前完成状态以本摘要和 `results/audit-run-record.json` 为准。材料、证据和结果均位于 `/Users/pengzhang/Documents/research/language-generation-non-p38/audit-packages/P03_Overview_2026-11-09_6062058`，未 git-track、stage、commit 或 push，也未写入权威 AuditRecords／registry。

现有历史 LLM 审计并非覆盖每篇论文：权威 AuditRecords 中有 **P01、P02、P06、P08、P28、P31** 六篇的历史记录，12 份证据哈希已核验；这不等于重新审计它们的当前工作树版本。本次之前未找到 P03 的已完成 LLM 审计；另有 P03 3.1–3.3 的人工作业记录，未作为盲审输入。现在新增本地、未跟踪的 P03 审计，因此计入本地结果后为七篇，但权威登记仍为原来的六篇。[历史清单](existing-llm-audits.json)

验证范围：冻结输入与 391 项原始 checksum 校验通过；最终输出另做 SHA-256 校验、目标覆盖核验及 Git 未跟踪核验。准备材料时曾通过 P03 Overview 的定向 Lean 构建，记录中无警告；本次审计没有改 Lean 源码、导入或生成输入，没有重新运行定向构建，也没有运行全仓构建。因此没有本次新构建的警告／失败可报告，不能据此声称重新检查了证明。

建议后续先固定论文计算模型的解释（允许哪些 oracle、是否要求统一普通计算），再决定是否补充相应的 computable／relative theorem 接口；单独记录 3.6 的源文公式与预期修正；若要覆盖引言 support-risk 版本，则补明与现有确定性见证的对应。以上属于下一步修订建议，本次没有修改定理、证明、公共文档或登记状态。
