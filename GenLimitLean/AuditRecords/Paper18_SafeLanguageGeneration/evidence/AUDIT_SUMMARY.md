# P18 LLM 审计摘要

结论：确定性的否定结果、padding reduction 和具体机器码下的不可判定性有实质支持；正向生成／识别结果主要停留在语义函数层，尚未形式化源文的有限 membership-query 实现。Corollary 6.1 本身仍未覆盖：已验证的是特定 printed reduction 的失效，不能宣称推论被反驳。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。8 个目标声明完成三步审计，并盘点完整 18 页论文、42 模块 native umbrella。控制源 [arXiv:2601.08648v2](https://arxiv.org/abs/2601.08648v2) 官方 PDF SHA-256 为 `c978aaa43d875597f3a349660efaf87b1307a717007138d4edd2d8847f96bcb0`，与登记版本一致。

| 目标 | 裁决 |
|---|---|
| `theorem_3_1` | 固定无限语言族先于任意识别器，完整逆向流保证其失败。确定性不可能结果对应；未定义 random insertion 的概率语义。reindexing 声明同时运输 learner，不是未知重排下不改控制器的保证。 |
| `theorem_5_1` | 对任意待识别族的 padded-family SG 假设导出语义识别，且 native 有同一固定运行的前缀接口。修复源文 fixed-collection／universal-solver 量词及模拟时序问题有依据；有效程序转换尚未提供。 |
| `theorem_6_1` | 具体 total Boolean program-code 的无限接受语言 promise 下，不存在总可计算 emptiness decider。uniform hard-pair compiler、validity 和准确归约接口均存在，不是仅假设未提供的 embedding。 |
| `theorem_6_1_restricted` | 硬子族的空／无限差集归约有效；它与源文空／单元素差集构造不同，不能直接替代后者来推出 SG 推论。 |
| `theorem_6_1_of_hard_embedding` | 给定可计算且准确的 embedding 后的条件性传递引理；不无条件证明所有表示等价，也不单独保证解释集合无限或可判定。 |
| `corollary_6_1_printed_reduction_collapses` | 准确诊断源文构造：停机／不停机都产生有限差集，都只要求 eventually bottom。推论本身未证明，也未反驳。 |
| `theorem_6_2` | 固定 padded punctured families 排除全部语义生成器，因而也排除具体 oracle 程序。替代证明有依据；不依赖源文 P* 的未完成推理。oracle 不提供实际隐藏目标索引。 |
| `theorem_6_3` | all-cross infinite differences 下的 named semantic generator 对应存在性结论，但使用全局集合包含测试与 classical fresh choice；尚未提供有限 membership-query 的实现。 |

Corollary 6.1 的关键区别是“可判定 emptiness”与“最终行为正确”。Definition 2 对空差集及单元素差集都允许永远 bottom，因此该 printed pair 没有必需的行为差异。把单元素改成无限差集也只给出极限信号，不自动给出可观察的有限停机决定。这解释了为什么原归约不能证明推论，却不足以否定任何可能的其他证明。

Remark 1 的 emptiness-only oracle 不一定需要额外 finiteness oracle：在识别稳定后，如允许查询残余描述 `(K\S_t)\H`，可先测 emptiness，再用 membership 搜索 fresh safe 点。有限差集最终全部被观察，无限差集始终有剩余。这里要求 oracle 查询语法对删去有限集合封闭；若仅能查询原始候选索引对，该论证不能直接使用。source 的访问模型需明确，native 尚无相应 SG 接口。

对 6.3，源文从 finite-prefix criticality 推到候选全局包含于 K 的解释并不成立。裁决另给出非形式化修复：在固定轮次增长 vocabulary，有限候选的 criticality 仅有限次改变，加上 all-cross infinitude 保证搜索终止；最终选中 target index 至少为真实索引，给出当轮输出属于 K；最小 consistent harmful candidate 最终包含真实 H，给出安全性。该修复支持源文可能有有效证明，不代表当前 native 已实现这个有限查询过程。

仍缺：Corollary 6.1 的独立论证、Remark 1 的正式访问协议、正向有限查询程序与 reduction、部分策略失败诊断和完整有效 KM 算法。family-wide finite-cross-intersection 推论在 native 中已有声明，不计为缺失。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果清单](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。Stage 2 的提取器曾附带显示四条 simp 证明值；记录了具体位置、时序及未用作含义／证明证据的限制，之后已修正提取器。这不改变 Stage 1 的盲重建隔离。

前两阶段由不同全新上下文完成，第三阶段在 Stage 2 冻结后由同一审计者继续；均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。所有新增材料在 non-P38，未 git-track、stage、commit 或 push；未改库中 Lean、PaperMap 或 registry。准备阶段 Overview 定向构建通过（819 jobs），日志无警告；未新增全仓构建、证明步骤审计或人类认证。新数学修复均标为非形式化检查。
