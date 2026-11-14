# P15 LLM 审计摘要

结论：partial generation、有限交集假设的生成及 full-text 识别／分离有实质 native 支持；α/3、α/2 密度结果仍是条件性组件，缺少完整运行与证书组装。论文 partial topology 的定义与 Theorem 4.12 存在实质冲突，Lean 尚未形式化该部分。本次裁决也撤回了一项第二阶段的错误判断：按观察数量对齐后，没有所谓 current-input freshness 缺口。

对象为当前 `work/non-p38` 工作区字节快照，HEAD 定位符 `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。审计 13 个目标声明，独立盘点完整 46 页源文、48 模块 native umbrella；16 个实际 paper 子模块均在快照及覆盖范围内。[arXiv:2511.05295v1](https://arxiv.org/abs/2511.05295v1) 官方 PDF SHA-256 为 `a33b59725302753cefee10d33d93c9c7b0f7215b1f4858abc8fce532234c5d7b`，与登记一致。

| 目标组 | 最终裁决 |
|---|---|
| 1.5、1.7、1.8、2.1、2.2、2.4 | 对应论文的语义生成结论，保留同一 learner、完整的 presented subset、eventual validity 与 cofinal containment。具体 Algorithm 1 使用 raw-index stuttering 实现，未主张逐轮相同。 |
| 3.1 validity | 有实际优先队列运行和有效性／freshness／injectivity 声明。PDF 未指定的 downward token 取 2 可支持 validity；不能因此声称 density schedule 已获证明。 |
| 3.1 density certificate | 给定完整 charge certificate 后推出 α/3 的数学成立；实际运行的全域 eligibility、good/bad charging 和完整证书仍缺。 |
| 3.5 fixed-pod endgame | 同一输出集合上所有固定 s 的界推出 α/2，有限算术和 liminf 组件已存在；实际 pod run、动态 capture 与证书构造仍缺。 |
| 4.9、4.11 | full-text 语义识别 iff countable T_D、full-text 分离 iff inclusion antichain 对应。tell-tale 显示式采用紧邻正文支持的 strict-sublanguage 解释。 |
| 4.10 full-text 与 partial 反例 | full-text 特例成立；两个无限语言共用无限 partial text 的反例否定源文更强的分离措辞。它不否定 finite-family conjunction identification。 |

源文时间 t 看到 x₁,…,x_t，正好对应 Lean 的 stream 0,…,stream(t−1)。第二阶段曾把下一观察 stream t 当作当前输入，错误地报告一个额外桥梁需求。裁决明确撤回该项，冻结的原报告保留历史原貌。

对 τ_C，源文给所有不包含 C 的语言 singleton open，而包含 C 的语言在 quotient 中不可区分；由有限正约束可把前者与后者双向分开。该 quotient 在所用包含约定下总是 T₁，故总是 T_D。另一方面，全体自然数加上所有单点删除语言是全部无限、可数但不能 full-identify 的类，因而也不能满足包含 full case 的 partial-identification 要求。如此，印刷定义的右侧不能刻画 Theorem 4.12 的性质。此为非形式化、逐项核对前提的反例；未暗中选取修复后的拓扑。4.12、4.13 的 native 数学仍缺。

对密度证明的判断保持有限：实际源文递推的一个精确有限前缀可否定“两次 full 后必曾 revisit”的局部推理，但不能否定允许更晚 cutoff 的 eventual lemma；generic input-purge 诊断本身更不够。pod 的 historical-capture 步骤尚待证明，周围正文允许按“最小 unused 点”理解，不应仅由伪代码漏字宣布定理错误。源文 gcd-of-values 的 arithmetic-progression 见证确有反例，用 minimum 与差值 gcd 可作非形式化修复；该例并未因此在 Lean 中补齐。

后续应完成实际 warm-up／pod 运行的证书，另行处理 sharpness、density-preserving translation、partial topology 和 deletion；合理的源文局部修正不能代替这些结果。本次未修改代码或公共登记。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。最初 census 只加载 Overview 的范围问题已由独立校验的 full-umbrella supplement 核清；本篇两份 census 的 1267 个声明实际相同，原输入未改写。

前两阶段是不同的新上下文，第三阶段由冻结后的同一 Stage 2 审计者继续，父代理提示来源明确记录；模型均为 gpt-6.1-sol / xhigh，未知后端 revision 不猜测。材料仅在 non-P38，未加入 Git 跟踪、暂存、提交或推送；未改库中 Lean、PaperMap、registry。Overview 与完整 native umbrella 定向构建均通过，无警告；未运行全仓构建。新数学及有限前缀实验均标明验证层级，不构成证明步骤审查或人类认证。
