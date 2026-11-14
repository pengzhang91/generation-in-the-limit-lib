# P17 LLM 审计摘要

结论：13 个目标的核心语义对应基本成立，但整篇形式化仍 partial。裁决修正了两项既有说明：c=1 端点并不需要额外的真实观察前提；B.3 的 critical equality 可用有限 marker 构造修复。相反，源文 7.7 的字面参数没有合法输入流，registry 所称 p=0 的无限零密度 witness 实际为空。这些分别属于源文／说明问题，不能混同为 Lean 已证明命题错误。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留原有未提交工作。审计 13 个目标声明及完整 71 页源文、40 模块 umbrella；全部 20 个 paper 子模块已纳入。[arXiv:2511.07417v1](https://arxiv.org/abs/2511.07417v1) 本次官方 PDF SHA-256 是 `6a791bc54891ba447fbf391db9f84927dbe20231a310cfee821760f7aafa9760`。历史登记哈希 `e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9` 的本地 annotated 副本确实存在；逐页标准化正文相同，注释未作为审计数学证据。[源文身份](../stage2/source-identity.json)

| 目标组 | 最终裁决 |
|---|---|
| 5.1、5.4、6.1、6.5、6.11 | 主要语义生成／密度／刻画结果对应，保留 family-wide witness、噪声和遗漏模型及正确的密度方向。named Algorithm Four/Five 等支撑比 Overview 更完整。 |
| 6.4 | 0<c<1 的具体无限 floor-increment witness 及密度对应；端点需单独处理，不能把空集合当无限零密度目标。 |
| 6.14 | native 仅覆盖 0<c<1。c=1 在源文条件下可由 growing-prefix intersections 证明，属于尚未形式化的端点，不是有依据的额外数据限制。 |
| 6.15、6.16 | 语义转换和正参数 named witness 存在。沿运行条件可作不依赖目标的全域 totalization；rho=0／非正 loss 可由已有生成 helper 和非负密度组装，尚无统一包装。Algorithm 8 是调度变体，未主张逐轮相同。 |
| 6.18 | finite-expansion 条件性转移正确；compatible expansion orders 数学上可构造，但 builder、全 countable-family 包装及重复流前提仍须正式处理。 |
| 7.4、7.5、7.8 | subset displacement、上下密度换算和 bounded-adversary 正结果对应。Algorithm 9 的 raw core／finite-deleted fresh output 有明确支撑，finite deletion 保持密度。 |

c=1 的核查：任何有限组无限语言都可共享一个完整枚举其并集的 injective 流，噪声不超过 1；Condition 3 因而要求每个有限交集在每个成员中都至少 rho-dense，并且无限。生成器输出前 n 个语言的交集去掉已观察有限样本，即可在包含真实目标索引后正确且保持密度。此论证不需要有信息的观察，是非形式化检查；没有因此新增 Lean 端点。

B.3 的修复也核对了 exact prefix 而非仅 limsup：正自然数上取 F={1,…,k}，L_r=F∪{n:n mod k≠r}，k≥2，使用 canonical stream。每个前缀对所有目标的坏点数均不超过 n/k；语言均无限、共同交集恰为已观察的有限 F，故不能最终 fresh 生成。它修复 equality witness，但不是已有 native Appendix B 定理。

源文 7.7 的 M=c=1/k 则有更强问题。严格按一基 canonical rank、exact eventual displacement/noise 和 distinct stream 计算，所有早期有限例外最终被增长的 rank window 吸收，因此 validCount(n)≤floor(Mn)，而噪声条件要求 validCount(n)≥ceil((1−c)n)。k>2 时增长率冲突，k=2 时所有充分大的奇数前缀冲突。故根本没有合法流，字面“不可生成”不成立。较大 factor 配合修复后的 marker family 可支持 intended obstruction；只改 factor 仍不能修复原例的有限语言及噪声问题。

registry 6.21 的 p=0 floor-increment 集合要求 0=1，实际为空；其无限性定理也明确要求 p>0。仍需真实的无限零密度目标及完整 element-density impossibility 组装。real M 的上界 witness 可用 ceil(Mj) 和 M=1 的单独分支处理，旧 integer 限定只是一个特例。

仍缺 membership-only 可计算 corollary、6.19／6.20 的完整数值前提与包装、6.21、部分 Section 7 下界、repetition reduction 及 Appendix B 算法。7.10 和若干 upper-density necessity 已有可组合数学成分，不应记成整个结果毫无支撑。所有新增 endpoint／normalization／order／residue／scaling 论证均标为非 Lean 检查，本次未改源代码或 registry。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果校验](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。完整 umbrella supplement 的 1282 个声明与旧 census 相同，补充记录核清全部模块；原输入未改写。

前两阶段由不同新上下文完成，第三阶段为 Stage 2 冻结后同一审计者继续；父代理候选论证及复核来源明确披露，均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。材料仅在 non-P38，未 git-track、stage、commit、push；未改 Lean、PaperMap、registry。Overview 与完整 umbrella 定向构建均成功；P17 的 4 条既有 unnecessarySimpa 警告在两份日志中重放，未发现构建失败。未运行全仓构建，未作证明步骤审查或新增人类认证。
