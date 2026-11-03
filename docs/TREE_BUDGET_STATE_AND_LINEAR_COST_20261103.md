# 树预算：状态分离、旅行费用编码与文献对照

日期：2026-11-03（Asia/Tokyo）。本次实施附件建议的前三项完成线：同输入状态分离、任意有理父边费用编码、旅行费用回归与固定流总费用恒等式。基地拆分仍列为后续工作。

后续更新：同日继续实施 Issue #18 第一小包，缓存契约与本批次一同提交；接口、回归和独立的本轮验证记录见 [缓存状态说明](TREE_BUDGET_MEMO_STATE_STATUS.md)。以下保留前一阶段的构建记录。

## 仓库基线与新增内容

通过 GitHub 插件读取仓库和 [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18)，核对其代码基线 `2466e0b4b91744045618c78fdb61ecc986863b39`。远端研究分支在本次查询时为 [499ed3f](https://github.com/huam54925-cpu/uav-routing-certification/commit/499ed3f01f7f078a4610c8c90886c2de1b655e23)，最后修改为文献说明的 Markdown 格式修正。已阅读该版本的 [文献比较](https://github.com/huam54925-cpu/uav-routing-certification/blob/499ed3f01f7f078a4610c8c90886c2de1b655e23/docs/TREE_BUDGET_LITERATURE_REVIEW_20261103.md)。

本地实际位于 JSP 工程分支 `codex/case1-local-validation-20261018`，HEAD 为 `2d3781e`，大量 UAV 扩展为既有未跟踪文件。远端跟踪引用原先停在 `e04db4c`；本次 `git fetch` 连接失败，之后通过在线固定提交页面完成文档核对。没有将这个工作区声称为远端最新提交的干净检出。实现依托本地既有 UAV 源码和缓存，未切换分支、覆盖既有代码、提交或推送。

新增三个模块：

| 模块 | 本次结果 |
| --- | --- |
| [TreeBudgetStateSeparationExamples.lean](../LeanCompletion/UAV/TreeBudgetStateSeparationExamples.lean) | 同输入合法前缀、相同摘要、相反剩余可行性，以及摘要判定器不存在 |
| [TreeBudgetLinearCost.lean](../LeanCompletion/UAV/TreeBudgetLinearCost.lean) | 可执行虚拟服务费、费用恒等式、路线/矩阵/原证书检查器等价、固定流总费用 |
| [TreeBudgetLinearCostExamples.lean](../LeanCompletion/UAV/TreeBudgetLinearCostExamples.lean) | 非对称有理旅行费、负虚拟费、基地忽略、预算边界、旧搜索与检查器复用 |

既有 `HubSpokePacking`、三个费用 6 的任务不能放入两条预算 10 路线的例子、`residualWitness_rootCount` 和 `transition_invariants` 都是复用基础，不计为本次新增结果。

## 1. 状态反例：明确排除一种压缩键

使用既有 `hubTree`，坐标顺序是 `(o,v,a,b,c)`，而非附件省略基地的四坐标写法。固定原输入 `H=(0,4,2,3,2)`，服务费 `(999,0,3,4,5)`，预算 10；基地服务费不计。

`reachable_prefixes` 核验各前缀行满足原输入的 `RowValid`、每一步坐标减法有保护，以及两次扣除后的精确剩余量。从四条路线开始：

| 前缀 | 剩余向量 | 剩余路线数 | 费用 | 卫星访问数 | 全部非基地访问数 | 正支持 |
| --- | --- | --- | --- | --- | --- | --- |
| B、B | `(0,2,2,1,2)` | 2 | 20 | 5 | 12 | `{v,a,b,c}` |
| A、C | `(0,2,1,3,1)` | 2 | 20 | 5 | 12 | `{v,a,b,c}` |

`good_search` 与 `bad_search` 用 `decide +kernel` 检查完整 `searchRows`。随后通过 `searchRows_correct` 得到语义命题 `good_feasible` 与 `bad_infeasible`；不是只记录 `#eval` 的输出。前者可分成 `5+5` 与 `3+3+4`；后者不存在总费用恰好 10 的子多重集。

`no_summary_decider` 进一步证明：不存在只读取上述五项摘要、却能同时正确判断这两个状态的谓词。因此即使缓存只用于同一固定输入、合法到达的状态，也不能把它们合并为同一个答案。

这没有证明完整向量是最小充分状态，没有排除保留更多信息的压缩，也没有给出一般复杂度下界。`k=rootCount(r)` 的既有不变量可支持受限接口去掉 k，但一般 `(k,r)` 接口依旧需要区分同 r 不同 k。

## 2. 费用编码及检查器复用

定义 `linearCost R p w = Σ(v≠o) w(v)p(v)`。可执行函数 `virtualService` 沿父链递归：

```text
σ(o) = 0
σ(v) = w(v) - σ(parent(v))  (v ≠ o)
```

仓库的 `rank` 朝父节点增大，因此终止度量采用 `Σ rank - rank(v)`。`virtualService_edge` 和 `rowCost_virtualService` 证明

```text
σ(v) + σ(parent(v)) = w(v)  (v ≠ o)
rowCost R p σ = linearCost R p w
```

第二式对任意自然数向量 p 成立，无需连通性、根度为 1、非负费用或合法路线假设，根坐标任意。`exists_virtualService` 给出存在性；`linearMatrix_iff` 保持同一矩阵见证，只改写预算表达式。

对于逐次访问服务费 s 与逐次有向边旅行费 c，定义

```text
w(v) = s(v) + (parent(v)≠o 时的 s(parent(v)))
       + c(parent(v),v) + c(v,parent(v)).
```

`flowTravel_edgeFlow` 证明双向费用求和；`combined_rowCost` 合并服务和旅行；`routeCost_eq_virtual` 对实际使用树边的合法路线证明费用相等。没有假设 c 对称。

`travelExact_iff_virtual` 保持同一族实际路线及精确访问/流条件。`travelExact_iff_matrix` 在 `HasDegrees` 前提下接入旧矩阵定理；`travelExact_iff_certificate` 进一步证明真实服务加旅行预算可行，当且仅当存在经原 `checkCertificate` 接受的虚拟服务费证书。证书格式、模式搜索、根分支接口均可沿该等价复用。

回归使用 `pathFour` 的前三个点，最后一条边重数为零：`c(0,1)=4, c(1,0)=6, c(1,2)=1/2, c(2,1)=3/2`，真实非基地服务费全为零。虚拟费为 `σ(1)=10, σ(2)=-8`，精确费用 12。根输入坐标 99、基地服务费 999 均不影响结果。预算 12 接受、11 拒绝；旧剩余搜索在 12 返回可检查证书，在 11 返回不可行。

负 σ 是精确编码系数，不是物理负时间。不得直接使用需要 `s≥0` 的拆分定理或部分费用单调剪枝。即使物理费用均非负，也要分别证明相应剪枝对转换后的边系数成立。当前覆盖的是有理数可加费用；无理欧氏距离、时间窗、等待、充电与顺序相关费用并未因此自动获得精确模型。

## 3. 固定精确流的总费用

`total_cost_fixed` 对任意有限图、任意有限合法路线族证明：

```text
Σ_i routeCost(r_i,s,c)
  = Σ_(v≠o) s(v)d(v) + Σ_u Σ_v c(u,v)x(u,v).
```

前提是精确访问次数 d 与精确有向流 x；无需树假设。证明交换有限求和并使用精确计数等式。树上的既有流唯一性使固定树、需求和机数进一步固定相容流。因此这个分解层适合研究逐路线预算、最大路线费用与分配；固定 x 后最小化总费用不能区分不同分解。若外层允许改变 x，这个结论不消除外层总费用优化。

## 4. 三份实际论文的比较

本次读取用户提供的三个 PDF 全文提取结果，重点核对以下模型、定理与状态定义，并渲染查看 IPEC 第 13 页、Dias 第 5 页和 Xu 第 7 页的公式。页码按 PDF 页序；IPEC 同时标印刷页 10:n，Dias 第 5 页为期刊页 1149。未把论文的所有证明重新形式化。

| 论文及定位 | 已有内容 | 与本次工作的关系和限制 |
| --- | --- | --- |
| Xu、Zhang、Hu、Guo (2021)，[DOI](https://doi.org/10.1155/2021/6648044)，第 1–4 页模型与流状态，第 7 页定理 1 | 固定 k 的多基地容量路由；可拆需求转单位客户；非负无向距离；最小总距离；网络流动态规划，定理 1 为 `O(n Q^(3k))` | 已有内部子树流组合先例。本仓库按每次到访精确计数且禁止中途回库；旅行编码并未消除这些语义差异。固定精确流的总费用恒等式解释了为何本次分解不能直接用其总距离目标衡量改进。 |
| Döring 等 (IPEC 2025)，[DOI](https://doi.org/10.4230/LIPIcs.IPEC.2025.10)，定义 2.3–2.8，第 10 页定理 4.8，第 13–16 页定义 4.18、4.21、4.22 及定理 4.24/推论 4.25 | 客户分配与 walk 经过分离；至多 k 辆；载荷/路长容量；已有树上装箱困难性、端点/资源/基地指纹和多维装箱合并；给出相应参数组合的 XP 结论 | 本次反例仅否定粗摘要，不否定其更精细的计数状态。该论文允许一个车辆组合多个基地分支的构造，不能直接作为本模型禁止内部基地访问的归约。本模型固定精确访问与边重数，不能直接使用删去多余遍历的规范化，也不能照搬容量有限状态界到任意有符号有理费用。 |
| Dias、Williams、Mumey、Tomescu (2025)，[DOI](https://doi.org/10.1007/s10898-025-01556-8)，第 4–5 页定义 1–3，第 3 节 ILP | 有向图上固定整数流的加权分解，区分 path/cycle、trail、walk；正整数权重；最小化加权分解元素数 k | 最接近固定流精确分解，但 k 与实际路线数 m 不同；本次没有证明其 ILP 或完整模型等价。需要拆分基地、保持访问/费用、限制合法 walk 后才能转换外部证书。 |

特别注意 Xu 的流变量描述客户流，而本仓库 x 记录实际有向边遍历次数。两者名称相似，不代表“固定流”的假设相同。IPEC 的 Definition 4.21 保留 `(端点,载荷,路长)` 各类片段的多重计数，比本次被否定的总量摘要精细得多。

本次增加的是具体模型中的可核验分离和费用/证书接口。装箱思想、一般树动态规划、加权流分解和缓存本身均有文献基础。未证明数学优先权、最小反例、最小充分状态、优于已有算法或新的 FPT/XP 复杂度结论。

## 5. 下一步计划怎样调整

1. **Issue #18 第一小包已接续实施。** 保留固定 R,H,s,T 下的完整 `(k,r)` 键；实现 `AnswerValid`/`CacheValid`、查询和替换插入，并纳入 good/bad、miss、已证失败与成功空见证回归。详见 [缓存状态说明](TREE_BUDGET_MEMO_STATE_STATUS.md)。
2. **再完成记忆化递归并测量。** 成功/失败都以剩余语义证明；候选后缀失败不能缓存为整个状态失败。旅行输入先转换 σ，额外保留本次负虚拟费回归。测量候选生成、冷缓存展开、命中、查找和见证存储；本次没有性能实验。
3. **内部子树接口先证明充分性。** 从高度二/三树出发，参考 IPEC 的片段端点、资源和基地标记，但加入精确重数和访问计数、路线配对、边界服务费用计账。证明提取与重建两个方向后，才研究在所有外部补全下保持可行性的状态等价及压缩。
4. **基地拆分作为独立后续桥梁。** 构造 `o→v₁→…→vℓ→o` 与 `s→v₁→…→vℓ→t` 的双向转换，保留内部非空、无内部基地和无连续自环；证明访问、边流、逐路线费用保持。对权重 αᵢ 的源点出流求和可望得到 `Σαᵢ=m`，还须处理正流支撑、零机队和孤立点，使 Dias 的网络假设明确。该转换及权重和尚未在本批 Lean 中实现。

## 6. 验证与复现

从本地工程根目录运行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetStateSeparationExamples LeanCompletion.UAV.TreeBudgetLinearCostExamples
```

2026-11-03 最终命令退出码 0，Lake 报告 `Build completed successfully (8348 jobs)`。三个新增模块均已在本次工作中编译；最终命令重编译线性费用主模块和例子模块，复用此前已成功且源码未变的状态反例模块缓存。20 项新增关键入口公理报告仅包含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；三个新源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`，新增模块无 linter 警告。既有依赖重放了原有非致命警告。

83 个既有 UAV Lean 文件的逐文件 SHA-256 与本阶段修改前快照一致；当时受跟踪文件无差异。根导入、冻结目标、工具链和依赖锁文件未改。本阶段验证结束时新增内容尚未提交；随后按用户要求与缓存第一小包一同准备发布，发布不构成额外历史验证。

本次实际验证使用既有 Lean 4.30.0-rc2、锁定依赖和构建缓存，不是全新环境重建、独立复核或远端 CI。原始开发日志、PDF 文本/页面、哈希快照均仅存于 ignored `verification/runs/state-linear-cost-20261103/`。失败开发运行不计 PASS，历史模块缓存重放也不计为新的历史成果证明。
