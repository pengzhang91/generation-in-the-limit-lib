# P03：按 workflow v2 作出的差异裁决

裁决结果：P03 的核心语义数学与已明示的 oracle 构造总体对应良好；3.6 的误差方向应归为“有依据的源文修正”，无限目标假设归为“符合源文上下文”，计算模型归为“已披露、仍有适用条件的对应”，其中源文的普通／相对计算约定仍有未决部分。不能仅因这三项把 Lean 判错，也不能由此把十三个完整声明标为无条件逐字等价。

这是在冻结两阶段报告之后，由同一会话协调者阅读已有说明作出的知情裁决，不是第三次独立盲审，也没有重新执行前两阶段。原六份报告／运行记录字节保持不变。源文仍为 arXiv:2411.09642v3（2025-10-14），PDF SHA-256 `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`；被审计 Lean 仍是 96 项输入清单所固定的当前 non-P38 字节。适用方法为 [workflow v2](../../workflow-v2/README.md)。本文并非新增人类审计或 Lean 证明认证。

## 一、十三个目标的最终处置

下表承接 [冻结的第二阶段报告](source-comparison.md) 的全部 28 个比较单元；不删除其中的字面差异、额外结论或遗漏。下界覆盖任意 PMF 学习器、固定指数常数、命名见证等额外内容仍按原表分别解释。

| 目标 | 纳入已有说明和源文修正后的处置 | 保留的适用边界 |
|---|---|---|
| 3.1 | 语义 dichotomy、有限 tell-tale 条件与下界的核心对应成立；oracle 构造作为已说明的独立加强理解。 | 编号 Overview 接口本身没有普通或相对可计算 learner 字段。`Results.Additional` 的具体 oracle 构造是辅助证据，不冒充编号接口已有该字段；源文允许哪些固定 oracle 仍需明确。 |
| 3.2 | 无限目标 regime 符合源文上下文；显式确定性 membership 搜索见证及统计上下界对应良好。 | 普通可计算性以可计算 membership 为已列明的充分条件。全局编码及相邻“无限多互异输出”内容的范围保留原说明。 |
| 3.3 | 在已声明语义／oracle 模型下，负向 support 障碍与正向构造有实质对应；更强速率是有意的派生加强。 | 不能据 oracle MOP 推出无条件 ordinary MOP，也不能从语义识别性推出普通采样器。泛化存在接口的单输出风险／support 风险区别仍保留。 |
| 3.4 | 忠实的编码机器版本，具有普通可计算的完整终止词支持判定器。 | 每条随机带的局部终止、EOS 编码和一般机器／字串运输义务必须明确。 |
| 3.5 | 已披露的无限目标、fresh／允许重复两种 PMF 支持约定和 oracle 正向构造可接受。 | ordinary MOP、统一训练／采样的证书条件照原接口保留；没有把条件删掉后宣称无条件算法等价。 |
| 3.6 | **有依据的源文修正**：失败 loss 更符合 Definition 8 和 error-rate 目标；下文反例直接否定字面 success-loss 版本的不可能性。 | 非字面等价；该局部裁决不消除共同的语义／有效 nonidentifiability 解释问题，也不证明修正后整条定理的全部证明。 |
| 3.7 | 概率无关的 support／stability 命题在语义 nonidentifiability 下对应良好。 | 不升级为所有 effectively nonidentifiable 语言族的无条件结论；冻结 Stage 1 的一句全称／存在措辞误差仍由 Stage 2 更正。 |
| 3.8 | Equation (6) 的失败事件和正 limsup 对应；替代有限样本论证不因不同于源文证明而构成声明错误。 | 语义 nonidentifiability 与源文计算约定的边界保留；没有新增 proof-step correspondence 结论。 |
| 3.9 | 在线 approximate-breadth support 命题对应；pointwise MOP 被明确保留。 | 语义模型与有效模型不同；后者单独给出的 uniform MOP 条件不能暗中代入前者。 |
| 3.10 | 忠实的 membership＋subset-oracle 构造／加强，未给 learner 偷加目标信息。 | 普通计算性为两个 oracle 可计算时的明确特例；没有把辅助在线 appendix 结论计为已覆盖。 |
| 3.11 | 有限语言族的统计结论及有限查询命名见证对应良好。 | “有限”指集合族的 range；允许个别语言无限；ordinary 计算证书有 membership 条件。 |
| 3.12 | 统计定理对应；替换印刷 least-consistent 构造应理解为有记录的源文构造修正。 | 该来源说明与 `leastConsistent_counterexample` 已存在，裁决未重新运行该 Lean 命题，也不主张构造步骤逐步一致。 |
| 3.13 | 标签 law、指数上界和更强随机化下界的核心对应良好。 | 命名程序的普通计算证书有 membership 条件；替代证明与源文证明不是逐步对应。 |

本次不能诚实压缩为“13 项全部通过”或“若干项 Lean 错误”的单一计数。合适的总体标签是：**核心语义／oracle 形式化大体忠实，包含有依据的源文修正，算法计算模型的完整对应仍有条件／未决。**

## 二、3.6：从差异记录到有依据的源文修正

Definition 8（印刷 p.32 / PDF 35）的成功事件是 `U(S,K)`：支持集 `S` 与真实语言 `K` 的对称差，严格小于它与每个不同候选语言的对称差。紧接着的显示公式却定义 `er = 1{U}`；同页速率条件要求期望 `er` 被趋零速率上界控制。这会要求成功概率趋于零。

实际 Lean：`UnambiguousAt`（Definitions.lean:69）保存该成功条件；`printedUnambiguousError`（UnambiguousModel.lean:56）保存成功概率；`unambiguousError`（同文件:50）使用失败概率；`unambiguousError_eq_one_sub_printed`（:60）的声明明确二者互补。Overview.lean:141 的注释明说修正了印刷公式，:147 的目标结论实际引用失败 loss。已有 [PaperMap 说明快照](adjudication-inputs/Paper03_PaperMap.md) 第 221–227 行也明确限定只形式化预期 failure-loss，没有验证反向的字面 objective。因此这是预先披露的修正，不是本次才加入的改变。

下面是本会话在原 Stage 2 示例之后提出并逐项复查的、更简单的反例。它是**非 Lean 形式化的数学论证**，不是新生成的 kernel 证书：

1. 令 `E={0,2,4,...}`。语言族为所有 `C_F=E\F`，其中 `F` 遍历 `E` 的有限子集。有限子集可用自然数二进制编码，故这是可数、可统一判定 membership 的 indexed family；每个语言无限。
2. 对任意有限 `T⊆C_F`，选 `a∈C_F\T`。另一成员 `C_(F∪{a})` 是 `C_F` 的真子集且仍包含 `T`。因此没有有限 tell-tale，按既有语义 Angluin 字符化不可识别；限制为计算学习器也不会恢复可识别性。这使用源文及 Lean 共同的预期有限 tell-tale 意义，不把“有限字符串的集合”误当成已经明确的有限基数文字。
3. 生成器忽略所有训练历史，确定性地输出奇数 `1`。它的支持恒为 `{1}`，所以沿每条合法正数据流稳定。MOP 由 `x=1` 判定，普通且统一可计算；常量采样器也普通可计算。3.6 不需要 finite-intersection generation nontriviality，因此不向例子强加这个额外条件。
4. 对每个无限 `C_F⊆E`，`|{1}△C_F|=∞`。它与所有不同候选语言的距离均打平，严格比较 `U` 永远为假。
5. 每个语言都有 full-support 有效 law，例如按其递增枚举分配正几何质量。无论选择哪个有效 law、哪个训练样本和样本量（包括零），印刷 success-loss 恒为 0，Lean failure-loss 恒为 1。因此该生成器对印刷 loss 满足任意非负趋零速率的上界，直接违背字面“不存在任何速率”的结论。这里不存在没有有效分布导致的空真，也不依赖非计算生成器或非统一 MOP。

最小源文修正是把 `1{U}` 换成 `1{not U}`（包括严格比较打平时的失败），等价于取 `1-1{U}`。Lean 实现的恰是此处修正。局部数学证据强于“通常 error 应计失败”的语感，但它仍不证明作者本人确认了勘误，不认证源文全部证明，也不独自证明修正后的完整不可能性定理。故最终处置是“有依据的源文修正”，并保留字面非等价。

## 三、无限目标：上下文一致

PaperMap 第 269–274 行已经引用源文 Section 1 p.2（PDF 5）的无限目标要求，并解释 finite-target exhaustion。实际 `Core/OracleFamily.lean:19` 的字段正是 `forall i, Infinite (language i)`。源文在引言把无限目标作为 fresh generation 可定义的背景；承诺对每个族成员生成时，全族无限是对应的 regime。不能孤立读取局部“所有可数集合族”的标题而忽略这段。

据此不把 3.2、3.3、3.5 的 infinitude 列为无依据的新限制。有限目标识别（3.11、3.12）与允许训练重复的 relaxation 仍按各自实际类型处理，不把无限假设擅自加到它们身上。Stage 2 最终稿已经改正初稿遗漏，本文确认该处置。

## 四、计算模型：接受已披露的限定，保留尚未建立的桥梁

源文印刷 p.21 / PDF 24 明确授予按 `(index,string)` 查询的 family membership oracle；Definition 11（p.22 / PDF 25）另给 tell-tale enumeration oracle，并强调它对算法的重要性。p.25 / PDF 28 又称学习器为 computable 映射序列。综合这些语境，不能要求所有 oracle 都无条件普通可计算，再把 Lean 相对程序误判为错误。

已有 PaperMap 第 301–315、350–358、656–692 行和 StatisticalBreadth.lean:12、OnlineBreadthConstruction.lean:86，明确把 semantic `ConditionTwo`、tell-tale oracle、pointwise ordinary MOP、uniform MOP 和 ordinary sampler 分开。实际 `CertifiedBreadthPositiveBranch`（StatisticalBreadth.lean:32）与 `CertifiedOnlineBreadthPositiveBranch`（OnlineBreadthConstruction.lean:90）也确实分别列出了这些证书，不仅仅是注释声称存在。

裁决认可：在明确提供 membership／tell-tale oracle 的解释下，正向构造有真实的程序接口；加入显示的 oracle 可计算充分条件，确有相应 ordinary 证书。3.3 的同一见证精确指数上界是有意的语义／oracle 加强。Definition 6 的逐个训练历史 decidability 与 Lean `DecidableMOP` 字面一致，不把 uniformity 自动塞进源文。

仍不能认可的升级：从语义存在直接推出普通 computable learner；从 `OracleMOP` 直接推出 ordinary MOP；从 pointwise decider 推出统一 selector；把没有 ordinary sampler 字段的存在量词读成普通采样算法。源文对这些约定、尤其固定可用 oracle 及跨样本量统一性的表述仍有解释空间。已有文档不能自行证明这些不同命题等价。

3.1 的额外 oracle 构造在 `Results.Additional.oracle_exponential_identification`（:45）有明确接口，可作为有意区分的证据；它未被重复计算为本次 Overview 编号 scope 中已有的计算性 conjunct。保留“语义核心对应＋算法解释有限定”的混合结果，而非一刀切判为 Lean 错误或全部通过。 该 Additional 模块不在原 Overview 的冻结 import closure 中；本次另存其当前版本为 `adjudication-inputs/Results_Additional.lean`，只用作外围接口解释，不追溯加入原两阶段输入。

## 五、验证与后续

本裁决只新增本地说明及 provenance，更新协调者摘要与哈希清单；没有修改编号声明、定义、证明、PaperMap 或 registry。完整输入仍由原 manifest 约束，原六份报告／运行记录仍按冻结 SHA-256 核验。新增 PaperMap 副本记录裁决实际使用的说明版本；它不进入历史盲审输入。原准备阶段曾通过 Overview 定向构建，本次没有运行新定向或全仓构建。

需要后续解决的是：为公开对应声明选定明确的 oracle／ordinary 计算模型，并在需要时补充精确桥接接口；若要主张引言 support-risk 版本，则明确确定性见证的连接；若要把上述反例升级为 Lean 证据，则另行形式化。现有材料足以支持 3.6 的修正裁决，尚未消除这些独立的范围问题。运行记录见 [adjudication-run.json](adjudication-run.json)。
