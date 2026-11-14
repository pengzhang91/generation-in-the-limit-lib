# P13 LLM 审计摘要

结论：clean/noisy 部分已有实质性的通用语义结果，源文零分／空见证处的局部修正有依据；尚缺论文 presentation、profile 和对角索引的 native 组装。representative 部分则仍有实质覆盖缺口。另发现论文允许 α=0，但代表性生成的通用结论在此端点失败；不能因此把 Lean 的缺失结果判为已覆盖。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。6 个目标声明完成三步审计，盘点完整 24 页论文和 24 模块 native umbrella。控制版本是 [arXiv:2510.02795v1](https://arxiv.org/abs/2510.02795v1)，实际官方 PDF SHA-256 `7cadb891b17073e917eff5fecd2db42b9ac923a138095c21d522542741fab1de`。与旧 registry 字节预期的差异已披露，不声称取得或验证不可用的旧哈希文件。[源文身份记录](../stage2/source-identity.json)

| 目标 | 裁决 |
|---|---|
| `theorem_1` | 全族可达性、正阈值、canonical prefix 与 prefix Pareto 四项均保留。源文 Claim 3.2 的“空存储见证仍属于含目标的 argmax”字面不成立；改为数值上界及有条件的见证存在是有依据的局部修正。 |
| `theorem_4` | 保留 max(entry,c+1) 的准确时间向量。injective 历史上时钟对应；有重复时 native 使用 distinct-count 调度，不能声称与源文按 chronological time 调度的命名程序逐轮相同。 |
| `theorem_5` | 有限 canonical sublevels 下精确实现 c+1 与全局 Pareto 最优均存在；不把充分条件升级为必要条件。 |
| `theorem_6` | 是任意标记坐标、任意噪声 allowance 的通用内核，可同时实例化所有语言／噪声对。源文 Procedure 2 首步无可行候选，native 的空集合／零分默认值是合理 totalization；对角实例化接口尚未组装。 |
| `theorem_8` | corrected noisy certificate 在 native 中已无条件构造，不是只假设未证明证书。精确 noisy Pareto 内核存在，仍缺对角与 presentation/profile 包装。 |
| `theorem_9_representative_endgame` | **实质缺口**：这是给定抽象 scheduler/tradeoff certificate 后的末步推论。具体概率分布、分组、scarcity、Theorem 7 生成保证及代表性证书构造尚未提供。 |

对 clean/noisy 的模型对应，裁决给出非形式化的双向论证：合法的有限 injective 历史可补全为完整目标枚举；反向将重复历史按第一次出现去重后交给 native 生成器，观察集合及 freshness 相同。noisy 情况中，去重后的 distinct outsiders 不超过源文的 outside occurrences，反向补全不增加噪声。故在源文的无限可数语言和正阈值范围，可达 profile 与 Pareto 比较在数学上对应；这不是已经新增或编译的 Lean transport 定理。

α=0 的反例满足论文全部相关前提：U=ℕ、语言均为 U、有限非空分组 `{0}` 与 `ℕ\{0}`。令 T={0,…,m−1}，第一组已无 fresh 点，却有经验质量 1/m>0，产生任意大的 scarce witness。沿完整枚举 0,1,2,…，精确代表性要求任何输出分布给已观察点 0 分配质量 1/m，因此不可能最终以概率 1 输出 fresh 目标点。源文没有 full-support 或每组无限的额外前提排除此例。把相关一般结果限制为 α>0 可排除此反例，但不等于审计已证明其余全部代表性结果。

Appendix A 的 outside-core 推理及 cutoff 端点也存在局部问题；native 提供修正后的 frontier 与不可 Pareto 结果，不应因缺少六个选定入口之一而漏算。

后续最小工作：补 presentation/profile 与 diagonal-rank 的 native 包装；保留已有零见证修正；独立建立代表性分布和 certificate，并明确准确度参数范围。本次未改源码或登记。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果清单](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。后来的 ALT/PMLR 2026 版本及新增 oracle 成本段落仅作为隔离背景保存，未替换控制版本或增加 v1 审计义务。

前两阶段由不同全新上下文完成，第三阶段在 Stage 2 冻结后由同一审计者继续；均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。所有新材料在 non-P38，未 git-track、stage、commit 或 push；未改库中 Lean、PaperMap 或 registry。准备阶段 Overview 定向构建通过（1364 jobs），日志无警告；未新增全仓构建、证明步骤审计或人类认证。新反例和 transport 论证均标为非形式化数学检查。
