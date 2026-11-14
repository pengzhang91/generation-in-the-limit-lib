# P11 LLM 审计摘要

结论：具体有限程序 TM／TBO 学习器有实质构造，Corollary 15 的具体有效接口特例应获完整信用；其余时间类、转导、不可计算下界及 MSM 结果主要是已披露的条件性核心。Lemma 9／25 在论文允许的部分函数、仅正观察语义下有反例；Lean 的共同输入源／完整 Option 正确性版本成立，但不能不加限定地登记为原引理的完整形式化。

审计当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留原有未提交工作。范围为 16 个目标声明、完整 25 页源文，以及完整 umbrella 的 15 模块／516 声明记录；全部 10 个 paper 子模块均已纳入。源文是 [COLT 2025 PMLR 291 官方版本](https://proceedings.mlr.press/v291/papazov25a.html)，PDF SHA-256 `83aef91acf3b06c6dbbe6432fa5c1084cc7396c206684a5ebf0d4f62c0e61d57`。历史登记的 `0fd7…cd0c` 字节实际可在原工作区批注本找到；25 页经规范化的正文文本逐页等同官方版，未把批注交给审计者，未声称两份 PDF 字节相同。详见 [source-byte discrepancy](../owner/source-byte-discrepancy.json)。

| 目标组 | 最终裁决 |
|---|---|
| Lemma 9 | 共同源上完整 Option 值不等时的 characteristic-core 分离成立；这是限定模型／修复读法，未覆盖论文全部部分域情形。 |
| Theorem 12、Corollary 13、Theorem 14 | 有统一有限历史筛选器及收敛定理；Q/q、合理编码、具体时间类到候选的统一覆盖组装尚缺。给定操作有效时可成为普通算法，任意语义函数参数不自动有效。 |
| minimum-index diagnostic | 仅证明两个可行预算之间不能推出全局最小表示；没有实际 learner／TM 枚举实例，不构成源文可学习性定理的反例。冻结 Stage 2 的定位笔误已在裁决更正为 TimeBounds:263–284。 |
| Corollary 15 | 有限指令程序、配对编码的 program＋scale、有限预算解释器与一个覆盖整个源的固定候选均真实存在；最终同一解码程序对所有输入正确。Nat 状态只访问有限支撑。任意 I/O 参数需有效接口限定；标准字符串实例可用普通有限列表算法实现，此说明未新增 Lean 定理。 |
| Theorem 16 | 给定扫描字的完整输出列表一致及给定机器族的学习核心存在；全体有限转导器枚举、真实 TM 扫描历史／前缀／学习器归约的连接缺失。 |
| Theorem 17、Corollary 18 | late-split 阈值的 characteristic-core 障碍、有限输入质量不等式和遗忘转移成立；实际停机归约、线性时间机器、不可计算界、完整观察编码质量比较及 non-IPTD 组装尚缺。 |
| Theorem 21 四项 | tagged 两步动作、整字状态保持及长度加倍、有限 transition cover 和六前提下的贪心终局均有 native 支持；真实 teacher TM、观察树、cascade／score gap 及无条件 MSM 学习定理仍缺。cover 大小不是对任意到达顺序的时间界。 |

Lemma 9 的反例取 D=I=ℕ，M 为全域常零程序，N 在偶数输出零、奇数发散。两者均有无限定义域，且是不同的部分函数。模型类取 {M,N}，IOO 附加信息为空；恒输出 M 编码的普通可计算 learner 在每个教师允许的任意定义域内输入源上始终正确。两个非空 characteristic cores 都可取 {0}，其并集既无定义域区别，也无观察区别，否定印刷分离结论。源文没有排除此例的全域假设。最小修复之一是要求某个共同有定义输入上的值冲突，或要求共同源上全域正确；Option 编码本身不会产生未观察的发散标签。反例不否定 Theorem 17 使用的全域机器对。

对 lower bound，native 的 ∑(n+1) 输入质量与源文包含输出／辅助轨迹的完整观察质量不能直接等同；固定输入集合测度的遗忘定理也不自动比较两种编码长度。MSM 的六项假设确实足以推出所述条件结论，不能由“取最大分数”单独获得实际 score gap。以上缺口大多已被原说明坦诚标为 partial，说明的存在不替代缺失构造。

全篇盘点还区分了未覆盖的 Gold Theorem 10、Theorem 22 的 Nerode／最小性、Theorem 23 的算法复杂度及 Proposition 24 的双射／状态排序／little-o／多项式解码保证；已有 encode/decode 恒等式不等于后者已完成。建议首先限定 Lemma 9 的 full 标签及有效接口描述，再分别安排时间类覆盖、完整机器归约、观察质量下界和具体 MSM 不变量；本次未修改这些说明或形式化。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。完整 umbrella supplement 在正式 Stage 2 初始交接时已提供，所有模块核清。

前两阶段由不同全新上下文完成；第三阶段为 Stage 2 冻结后同一审计者继续，父代理检查问题及阅读时序已披露。模型均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。全部材料仅在 non-P38，未 git-track、stage、commit、push；未改 Lean、PaperMap、registry。Overview 与完整 umbrella 定向构建均通过，无警告；未运行全仓构建。新反例和修复均为非形式化数学核查，未作证明步骤审查或新增人类认证。
