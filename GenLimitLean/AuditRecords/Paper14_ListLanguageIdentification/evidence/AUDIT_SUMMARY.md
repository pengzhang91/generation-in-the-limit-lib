# P14 LLM 审计摘要

结论：选定的 Theorem 1、Theorem 2 与论文的确定性语义主张对应；限定好语言可呈现性、k=0 延伸和 index-layer 表示后，未发现实质不等价。Algorithm 1、Claim 5.1、Theorems 6–7、递归 Ψ、peeling、相对 learner 及分层组装均有 native 支持。经典层级例子尚缺，整个统计／IID／随机化／收敛率分支尚未形式化，不能把确定性主定理的通过扩大成全篇完成。

审计当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留原有未提交工作。范围为 2 个目标声明、完整 30 页源文及完整 umbrella 的 29 模块／491 声明记录；全部 8 个 paper 子模块均已纳入。控制版本为 [arXiv:2511.04103v1](https://arxiv.org/abs/2511.04103v1)，官方 PDF SHA-256 `fdc00078c5ca6f2794005d608ebae5c46a7b5f012e5a200891e10cfd1f4a32d4`，与登记一致。

| 目标 | 最终裁决 |
|---|---|
| `Results.theorem_1` | 同一个按 F,k 选择的有限历史 learner，对所有完整输入序列最终包含正确语言，当且仅当全体语言满足递归 k-Angluin 条件。两方向、有限 witness 的量词顺序及在同一个完整 F 内递归均保留。 |
| `Results.theorem_2` | 等价于恰 k 个 index layers 覆盖所有索引，且每层满足相对 Angluin tell-tale 条件。允许重叠、重复、空层，符合 union 而非 partition 的源文主张；相对标量 learner 和输出串接已有实现，字面 learner-valued 层包装尚可补充。 |

源文假定可数宇宙、非空语言；Lean 在任意 α 上直接假设每个 F_i 有完整 ℕ-presentation。可数情形下非空性构造这些 presentations，反向仍量化所有合法源，而非只保证存在的那一个源。k=0 两侧皆假，是保守延伸；有限非空语言允许重复，重复索引按语言外延判定成功，正确的名字或 slot 不必稳定。论文 footnote 4 明确没有可计算性限制；经典选择及语义语言测试不应被另行要求实现成普通算法，也没有 oracle 查询或运行时间保证。

论文细节问题经过第三阶段核查后分别裁决：

- cofinite 家族 C_m 中，正确递归深度是 Ψ(Z\F,r) 当且仅当 r>m−|F|。Remark 2 的删除集大小方向和 base-depth 说明有误，但层级结论可保留；该归纳是非形式化检查，经典家族本身尚无 native 实例。
- Algorithm 2 在允许有限语言时可能要求从已经耗尽的 singleton 选 unseen string。可修复为耗尽后重复已有点并修改 completeness 论证；这是印刷 routine 的 totality 问题，不是 Theorem 7 的反例。Lean 用锁定及 slot deletion 的另一条必要性路线，实际主张保持对应；本次不认证两个证明逐步等价。
- Theorem 10 的跨模型模拟可用等待已观察位置／随机位的 delayed simulation、even-only 取两值和独立 odd 数据实现因果性；Theorem 11 的 booster 不依赖统一 ε，逐 L,D 的正 gap 已足以支持存在性论证。整数 rounding 和初始小样本须明确；这些均是非形式化修复，未形式化或认证源证明全部步骤。
- Theorem 13 的随机化扩展可得到同一 target 在无穷多个 t 上错误至少 2^(−t)/(k+1)，最终大于 exp(−2t)。没有建立该定理反例。“最优下界”的 headline 必须保留 k+1 个不同语言有共同字符串的非平凡性条件；常值 singleton 类不能支持无条件下界。

已核对完整支持，统计分支缺的是概率模型、full-support IID、随机化事件、Top-k、概率阈值及 rate 定理本身，不只是漏一个 facade 名字。文档另有版本定位错误：此 30 页版本只到 Section 8.3，现有“Sections 8–10”、Theorem 1 的 Section 10／pp23–24 等定位不适用；应以本文及 [完整裁决](adjudication.md) 的源页码为准。本次未修改 PaperMap／registry。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。Stage 1 因请求补充了不含 source／注释／proof 的显式 Ψ 代码值，原始 manifest 未覆写；完整 umbrella supplement 在 Stage 2 初始交接时已提供。

前两阶段由不同全新上下文完成；第三阶段为 Stage 2 冻结后同一审计者继续，父代理问题来源已记录。模型均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。材料全部在 non-P38，未 git-track、stage、commit、push；未改 Lean、PaperMap、registry。Overview 与完整 umbrella 定向构建均通过，无警告；未运行全仓构建。新论证均为非形式化核查，未作证明步骤审查或新增人类认证。
