# P19 LLM 审计摘要

结论：四个主结论在论文约定下对应良好；完整的无限语言分离见证在 native 中存在。确认一项具体问题：扫描使用比论文更强的拒绝条件，因而现有“精确语义转写 Algorithm 1”的说明不成立。这个更保守的替代构造仍可支持同一分离定理；不是主定理被反驳。

对象为当前 `work/non-p38` 字节快照，HEAD `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`，保留既存未提交工作。4 个目标声明完成三步审计，另盘点完整 17 页论文、33 模块 native umbrella。控制源是 [arXiv:2601.21237v2](https://arxiv.org/abs/2601.21237v2)，实际官方 PDF SHA-256 为 `91a94905872920a960e6686cc5f13c18911c718f25f02507ab42fda54aa9a9cd`。与旧 registry 字节预期的差异已披露，不声称取得或验证不可用的旧哈希文件。[源文身份记录](../stage2/source-identity.json)

| 目标 | 裁决 |
|---|---|
| `theorem_2_16` | 所有正有限噪声等级与 level 1 等价，uniform／nonuniform 两部分及阈值量词均对应；不包含 level 0 collapse。 |
| `theorem_2_17` | 同一类的 noiseless uniform 正例与 one-noise nonuniform 失败对应。确切的非空列并语言类及无限性已有命名声明；Algorithm 1 的精确转移说法需要修正。 |
| `theorem_2_18` | 有限 level-1 dimension、所有正噪声 uniform 生成、单一 noise-dependent generator 的三方等价及 zero/one 分离均对应。dimension 用有限 witness 有界性表达。 |
| `theorem_2_19` | 递增、穷尽、每层 dimension 有限的 cover 与两种 nonuniform 条件及分离对应。阈值可依赖目标，生成器不依赖目标；registry 的 target-dependent-generator 措辞应改正。 |

Algorithm 1 的差异有满足全部分支前提的反例。native 块 B_j 只含列坐标 `(j,k)` 中 k<j+1 的部分，但 `algorithmForbidden` 在任何过去输出的第一坐标为 j 时都禁止块 j，即使该输出不属于 B_j。取总生成器 `G(n,xs)=((n,n+2),0)`：所有测试输出都不属于任何块，outside indices 为全体自然数，每个 hit set 为空。选块 0 后，源文按实际集合不相交判断会接受块 1；native 因此前输出第一坐标 1 而拒绝它。保留 rejected iterations 并不能消除这个差异。

裁决同时检查了替代构造的有效性：更强测试仍防止新旧块与输出互相冲突；有限已选集合仅产生有限 forbidden set，因而无限候选中会接受无限多块。它们形成合法无限目标，并在任意晚的完整可延伸前缀上给出错误输出。这是非形式化论证，支持同一分离结论；未新增 Lean 证明或审查原证明步骤。最小修复是把文档改为“保留更强 native 测试下的拒绝轮次”；若要求字面转写，应另行修改实现及验证。本次未做该修改。

其余限定：数值 dimension 及空 witness 的数值约定没有直接 API，但 `k²` witness→`k` witness 转移包含 square-root 界的实质内容，不能把该引理整体算成缺失。P06 的 occurrence-noise／重复流模型和 P19 的 injective／完整流模型不同，已有 forward bridges 与 native necessity 路径可支持被引用结论，仍缺若干 exact P19 组装入口。不能仅凭 import 就认作同一命题。未承诺普通可计算实现、运行时间或统计保证。

证据：[盲重建](code-only-reconstruction.md)、[独立源文对照](source-comparison.md)、[差异裁决](adjudication.md)、[总记录](audit-run-record.json)、[父代理验证](parent-validation.json)、[结果清单](SHA256SUMS)。阶段 provenance：[Stage 1](stage1-run.json)、[Stage 2](stage2-run.json)、[裁决](adjudication-run.json)。

前两阶段由不同全新上下文完成，第三阶段在 Stage 2 冻结后由同一审计者继续；均为 gpt-6.1-sol / xhigh，后端 revision 未暴露。所有新增材料仅在 non-P38，未 git-track、stage、commit 或 push；未改库中 Lean、PaperMap、registry。准备阶段 Overview 定向构建通过（1385 jobs），日志无警告；未新增全仓构建、证明步骤审计或人类认证。
