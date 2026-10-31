# UAV Routing Certification · 多无人机巡检严格验证

整理原论文、问题一至三程序、后续 ALNS 研究及 Case1 的数学证明。当前研究分支聚焦重复访问下的资源受限精确路线分解、支持与边重数的区别，以及局部证书的表示等价；原应用证明作为历史基线保留。

## Case1 结论（2026-10-18 验证基线）

对于本仓库固定的 Case1 坐标、精确巡检次数、合法路线及九小时时限：

| 结论 | 证据 | 边界 |
| --- | --- | --- |
| 少于四架不可能完成任务 | Lean 形式化下界，包含具体证书数值和 0–3 架排除 | 原验证环境中的编译、公理审计已通过 |
| 四架存在可行方案 | Python 独立验证器，整数平方根距离上界、精确时间比较 | 2026-10-18 历史 PASS，退出码 0 |
| 最小参与机队规模为四架 | 上述下界与可行见证结合 | 混合验证；四机可行性尚未成为 Lean 定理 |
| 四机最短完工时间 | 当前只有可行上界 | 未证明全局最优 |

最终 Lean 入口为 [`UAVProof.Case1Infeasible.feasible_fleet_card_ge_four`](LeanCompletion/UAV/Case1Infeasible.lean)。三机距离下界为 **1158.3991045 km**，超过九小时预算允许的 **1155 km**。四机见证覆盖 52 个点、72 次巡检，总距离处于 **[1559.493156, 1559.493220] km**。

这是对原论文问题一的后续研究。原论文中的候选状态是当时的记录，不代表今天仍未证明三机不可行。结论限定于当前模型，详见[模型对照](docs/MODEL_CORRESPONDENCE.md)。

## 服务费用模型的研究进展（2026-10-31）

研究分支 `research/structural-service-cuts-20261023` 已完成访问副本提升
与预算可行精确分解的等价定理，并将全部副本容量割精确重组为轮廓最小割约束。
现已给出轮廓的明确整数范围、固定副本流上的可执行最小割枚举与容量割
检查器，以及可读违规报告和预算 4 的内核认证。

在同一个四节点固定物理流上，预算 3 时不存在任何预算可行精确分解
（既有 `no_budget_exact_family`）；预算 4 时则存在精确分解
（新增 `exact_decomposition_four`）。指定提升的违规轮廓为
`(0,2,1,0)`，满足 `kappa = 1 < ceil(4/3) = 2`。
这里的 3、4 是逐路线服务费用预算，路线数为 2，不是 Case1 的机队规模。

检查器采用指数规模枚举，仍依赖给定副本流；尚无通用提升搜索或高效轮廓
最小化算法。完整服务提升还需要结构条件，不能仅凭容量割检查为真推出。
结果与验证来源分别见[分解接口](docs/COPY_PROFILE_DECOMPOSITION_STATUS.md)、
[轮廓割](docs/COPY_PROFILE_CUTS_STATUS.md)、
[枚举与检查](docs/COPY_PROFILE_CHECKER_STATUS.md)和
[违规报告与预算 4 认证](docs/COPY_PROFILE_REPORT_STATUS.md)。
各阶段的本地检查、缓存重放和公理报告分别记录，不把历史输出算作本次新验证。

本阶段仅计服务费用、不含飞行费用，不改变上述 Case1 混合验证结论，
也不表示已完成独立工程的干净重建。
当前主线是重复访问下的资源受限精确分解及其信息需求。已完成：

- 支持可行与精确可行的比较、严格单枢纽条件等价，以及同一允许支持图内的严格分离（[总览 #12](https://github.com/huam54925-cpu/uav-routing-certification/issues/12)）。
- 局部配对、递减秩与费用势推出预算可行精确分解；全部副本容量割由证书推导。
- [46be65c](https://github.com/huam54925-cpu/uav-routing-certification/commit/46be65c20534bfdd537c270ecdb596bf43d9120c) 新增逆向构造及两个最终 iff：
  在物理无自环、服务费用非负、T>0 下，
  `ExactFeasible o x d m s T ↔ m = outFlow univ x o ∧ HasLocalCertificate o d x s T`。
  允许零路线数、零需求、零费用及非相邻重复访问。

完整接口和证据见[局部证书充要刻画状态](docs/LOCAL_VISIT_PAIRING_COMPLETENESS_STATUS.md)。
用户 10 月 30 日的局部构建记录为新模块 Built（25s）、16 项依赖 Replayed、
退出码 0、22 项公理报告无 sorryAx；远端源码哈希与记录一致。
本次仅同步文档，没有重新运行 Lean，也没有新增独立工程干净重建结论。

现已完成 [next 单指针表示、prev 冗余消除及有界完整证书](docs/BOUNDED_NEXT_CERTIFICATE_STATUS.md)：
同一组证书见证满足基地秩为零、任务秩在 1…N、全部费用势在 0…T，
并与上述精确可行性等价，固定 m 时仍保留基地出流等式。
四个新模块此前本地构建均为 Built、退出码 0，57 项公理报告无 sorryAx；
本次阶段发布没有重新编译或完成独立工程干净重建。
后续模块 `LocalVisitPairingPotentialGrid` 已证明规范后缀势的公共分母与整数网格，
此前本地构建 Built（23s）、退出码 0，9 项公理报告无 sorryAx。
下一步是最终有限编码证书与位复杂度（[Issue #13](https://github.com/huam54925-cpu/uav-routing-certification/issues/13)）。
充要刻画不意味着证书最小、搜索高效或已有多项式算法。
[具体预算阈值与显式路线（#11）](https://github.com/huam54925-cpu/uav-routing-certification/issues/11)仍为辅助整理。

## 阅读入口

| 材料 | 位置 |
| --- | --- |
| 原论文及附录、图件 | [paper/original](paper/original/README.md) |
| 重复巡检下界修正稿 | [paper/revised](paper/revised/README.md) |
| 题目、输入表格和结果模板 | [source_materials/problem_A](source_materials/problem_A/README.md) |
| 问题一至三程序及已发表的结果附件 | [submission_package](submission_package/README.md) |
| ALNS、连通性割、精确证书及研究记录 | [research](research/README.md) |
| 13 个冻结 Case1 模块、后续研究扩展及证书验证工具 | [LeanCompletion/UAV](LeanCompletion/UAV/README.md) |
| 研究过程与贡献对应 | [研究时间线](docs/RESEARCH_TIMELINE.md)、[阶段报告提纲](docs/REPORT_PLAN.md) |
| 版本来源和所有原分支 | [材料来源](docs/SOURCES.md) |
| 固定版本与核验命令 | [复现说明](docs/REPRODUCIBILITY.md) |

## 证明与复现状态

十三个 Lean 模块保留原证明提交 `0d4466cbfacf3fe01ca98494663742f9a612b645` 的源码。原有本地编译及公理审计结果见[数值闭合记录](docs/CASE1_KERNEL_CLOSURE_STATUS.md)。新仓库补充独立 Lake 入口，沿用 Lean `4.30.0-rc2` 和同一 mathlib 提交。

**迁移期间没有重新运行 Lean 编译、求解器或已通过的证书检查，也没有完成新仓库的干净环境重建。** 迁移时的检查范围是来源与文件完整性、配置和文档。历史文档中的“本轮”“今天”指文档原来的工作阶段。

原仓库的全部九个分支已核对，相关代码和精选材料按主题汇集；没有合并旧仓库全部 Git 历史。原始日志、队列快照、聊天记录、构建缓存及下载依赖不随迁移上传。原仓库固定提交作为历史档案保留。

仓库保留创建时的 [Apache-2.0 LICENSE](LICENSE)。题目及第三方材料保持原来源与署名；其来源说明不构成对第三方材料的重新授权。
