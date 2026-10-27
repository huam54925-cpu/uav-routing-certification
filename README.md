# UAV Routing Certification · 多无人机巡检严格验证

整理原论文、问题一至三程序、后续 ALNS 研究及 Case1 的数学证明。研究重点从寻找候选路线发展为：在固定模型下证明最小机队规模。

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

## 服务费用模型的研究进展（2026-10-27）

研究分支 `research/structural-service-cuts-20261023` 已完成访问副本提升
与预算可行精确分解的等价定理，并将全部副本容量割精确重组为轮廓最小割约束。
新增结果给出轮廓的明确整数范围、完整分解接口，以及四节点指定提升中
`kappa = 1 < ceil(4/3) = 2` 的违规轮廓见证。

本阶段只计服务费用，不含飞行费用；结果仍依赖副本流，尚未提供可执行的
通用提升搜索或最小割算法。用户分三轮提供本地验证成功及 14 项无
`sorryAx` 的公理报告。详见[结果与验证范围](docs/COPY_PROFILE_DECOMPOSITION_STATUS.md)
和[副本障碍与轮廓割](docs/COPY_PROFILE_CUTS_STATUS.md)；这些研究扩展不改变上述
Case1 混合验证结论，也不表示已完成独立工程的干净重建。

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
