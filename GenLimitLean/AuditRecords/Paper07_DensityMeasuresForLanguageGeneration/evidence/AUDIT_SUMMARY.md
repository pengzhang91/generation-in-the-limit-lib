# P07 LLM 审计摘要

结论：index generation 正结果和 perfect-tower／limit-point 等价对应良好；其余目标主要是中间或条件性数学。尚无完整的无条件 1/8 element-density 算法、finite-rank 密度定理、index-breadth iff 或 truth-index 最优性证明。既有说明中的两项推断需要收窄：pair map 单射不推出 capacity two；早期 rank-two ancestry 反例不满足 late A_acc 证明所需的关键前提。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留原有未提交工作。9 个目标声明、完整 55 页论文及全部 45 模块／1825 声明参与覆盖盘点；29 个实际 paper 子模块均已纳入。[arXiv:2504.14370v1](https://arxiv.org/abs/2504.14370v1) 官方 PDF SHA-256 为 `3a1f56b09c05e7ed84a37544f53d84393f0bb968ad013e5bbd110ff14c0a5038`，与登记一致。

| 目标组 | 最终裁决 |
|---|---|
| 2.1、2.2 | 同一 selector 的 eventual containment、任意晚的 extensional accuracy，以及 guessed-language upper-density 的外层 limsup=1 对应；不能改读为累计 element outputs 的密度。 |
| 2.4 feasibility core | 忠实的一项支持引理，不是完整 adversarial forcing／breadth characterization。 |
| Claim 6.1 | 真实 containment topology 与 proper、完整、nonredundant perfect tower 的双向对应成立，native 还推广了 ambient class。 |
| 6.2 fallback endgame／arithmetic diagnostic | fallback 的存在及目标内 containment 有支持；实际 long-bad-run→bounded rank climb 与密度桥梁仍缺。返回的 fallback 不为空，修正一处 Stage 1 文字。 |
| 6.12 finite accounting／conditional 1/8 | 算术及 liminf 推论成立，native 另有 eventual-counting、ordered 和全局单射版本；尚无实际 learner run 自动提供全部假设。 |
| conditional 1/10 | 两类分别单射的 charge certificate 下成立；不是已证明可实现的修正版算法。source-strength conditional 1/8 路径也仍存在。 |

pair 单射问题可直接核查：{10,20}、{10,30}、{10,40} 是三个不同 pair，均选择输出 10 即产生三个前像；更多 pair 可产生任意重数。实际 native Schedule 的两类单射还依赖全局 token uniqueness、消费期限、priority 和位置关系。它们足以推出 capacity two，却未由源文实际运行完整构造。NoCrossCollision 是另一个独立义务。有效的条件性 1/10 推论不能自动变成无条件 1/10 生成定理，亦不能因此断言源文 1/8 定理错误。

rank-two 反例虽满足语言全无限及仍然 consistent，却发生在目标索引之前的早期轮次，child 并非该处实际 A_acc 选择，且缺少 late criticality／purge／bad-run 前提。它否定的是不加限制的跨森林 persistence，不是否定 eventual Claim 6.11 或 Theorem 6.2。FrozenFrame 提供同一冻结森林中的有效局部 climbing；实际 bad intervals 怎样提供其 escape／seed／reset 假设仍待证明。

完整索引还核查到了真实递归输出、reservation ledger、历史链、rational inclusion levels、run thinning 和 charging bridges，不能把这些工作误报为不存在。但 RunSpec 接受任意 supplied current／edges／reservation sets，尚未绑定到因果的源文 selector 和实际区间；native 永久禁止复用已 reserved 字符也不同于原 queue 规则。替代构造可以合法支持存在性结果，前提是另行证明完整 validity／density，而非仅靠名称。

局部源文解释也分开处理：StrictCritical 的 earlier-index 解释有正文依据；tower start 的 nonempty 条件已由源文全语言无限保证，是 native 推广域的限制，非源文域内额外修复。详细 Theorem 5.1 的 ∃A∀c 与 overview/proof 的 ∀c∃A 存在实际 witness-order 差别，不能只以 c/2 重参数化消除。源文明确允许任意函数，因此 classical/noncomputable 本身不是这里的计算模型错误。

证据：[盲重建](code-only-reconstruction.md)、[正式独立对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[正式 Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。

最初索引漏掉仅由 umbrella 导入的 365 个声明，已追加同一冻结字节的完整索引并核清全部模块。第一次 Stage 2 因代理状态查询意外显示其他论文摘要，已保存为[辅助／被替代记录](initial-stage2-superseded/stage2-run.json)；正式 Stage 2 由新上下文重新执行，使用完整输入且未读辅助记录，后续裁决同样排除它。原始输入及报告均未追溯改写。

前两阶段为不同新上下文，第三阶段在正式 Stage 2 冻结后由同一 clean reviewer 继续；父代理候选论证来源明确披露，均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。材料仅在 non-P38、未 git-track／stage／commit／push；未改 Lean、PaperMap、registry。Overview 与完整 umbrella 定向构建均通过，无警告；未运行全仓构建。新论证为非形式化检查，没有新增证明步骤审查或人类认证。
