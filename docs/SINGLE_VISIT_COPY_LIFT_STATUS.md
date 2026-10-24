# 单次访问基准与访问副本提升：实现及验证记录

日期：2026-10-24（Asia/Tokyo）。发布目标：
`huam54925-cpu/uav-routing-certification` 的
`research/structural-service-cuts-20261023` 分支。
本次增量基于 `628b72f94ac3d21493c7c40c98ce8b82c6772729`。

## 1. 本次文件与结论

新增两个独立 Lean 模块：

- [SingleVisitDecomposition.lean](../LeanCompletion/UAV/SingleVisitDecomposition.lean)：
  单次访问精确分解及全部取整服务容量割的双向等价。
- [VisitCopyLift.lean](../LeanCompletion/UAV/VisitCopyLift.lean)：
  访问副本、物理节点投影、边流聚合投影、同物理节点副本间零流量，
  以及支持路线的合法投影。

两个源文件按检查通过的本地快照原样发布；发布整理没有改写证明。
其余修改仅为本记录、Lean 模块导读和原研究计划的进度链接。
冻结 Case1 模块、实例、证书、工具链和依赖锁定文件均保持不变。

## 2. 单次访问基准的正式表述

主定理：
`UAVProof.SingleVisitDecomposition.rounded_service_cuts_iff_exact_decomposition`。

固定有限节点类型 V、基地 o 和自然数边流 x。假设：

1. 每个非基地节点的入流和出流均为 1；
2. 每个非空且不含基地的节点集合 S 满足出割流量至少为 1；
3. 所有物理自环流量为零；
4. 服务费用 s 为非负有理数，预算 T 为正有理数。

则下面两项等价：

- 对所有非空、不含基地的 S，
  `ceil((∑ v ∈ S, s v) / T) ≤ outCutFlow S x`；
- 存在合法基地往返路线族，每个任务恰好访问一次，
  全部路线的边流逐项精确恢复 x，且每条路线的服务费用不超过 T。

路线索引是基地正出流邻点的子类型。
更强的正向定理
`exists_budget_feasible_singleVisit_decomposition`
同时给出各路线访问列表无重复，以及路线数量等于基地总出流。
反向定理 `rounded_service_cuts_of_exact_family`
适用于任意有限路线索引类型，并覆盖空集合的容量割。

这是服务费用预算的结论，不含飞行费用。
连通性假设单独保留：零费用允许存在，容量割本身不能代替正出割假设。
正向预算证明不需要服务费用非负；双向等价中的非负条件用于反向证明，
保证任务子集上的服务费用不超过整条路线费用。
结论不附带独立指定的机队上界；路线数量由给定流决定。

证明主线：单位入出度确定前驱和后继，正出割排除不经过基地的闭环；
基地正出边生成互不重复、覆盖全部任务且精确恢复边流的路线。
每条路线自己的任务集合出割等于 1，容量割因此给出逐路线预算。
反向由精确覆盖、路线服务预算及已有 ResourceCuts 容量链得到。

## 3. 本轮副本基础对象

命名空间：`UAVProof.VisitCopyLift`。

| 对象或定理 | 含义 |
| --- | --- |
| `VisitCopy depot required` | 一个独立基地副本，加上每个非基地节点 v 的 `Fin (required v)` 个访问副本 |
| `project` | 基地副本投影到基地，任务副本投影到对应物理节点 |
| `project_eq_depot_iff` | 只有独立基地副本投影到基地 |
| `copyService`、`copyService_nonneg` | 每个任务副本继承原服务费用；基地副本费用为零；非负性保留 |
| `projectFlow π y u v` | 对两端分别投影到 u、v 的所有副本边流求和 |
| `entry_le_projectFlow` | 每条副本边流不超过对应物理边的聚合流 |
| `zero_of_same_projection` | 精确投影到无自环物理流时，同一物理节点的副本之间流量为零 |
| `lift_no_self_loops` | 副本流自身也无自环 |

副本流取值为自然数，非负性由类型保证。聚合投影定义适用于任意有限
副本类型 W 和投影 π，不要求 π 单射。
`required depot` 不用于生成任务副本；零需求任务自然没有访问副本。

关键推论的假设恰好是：
`projectFlow π y u v = x u v`、`x v v = 0` 和 `π a = π b`。
因为
`y a b ≤ projectFlow π y (π a) (π b) = x (π a) (π a) = 0`，
所以 `y a b = 0`。因此禁止同物理节点副本之间的正流量是推论，
无须额外加入一个独立的“禁止此类边”假设。

## 4. 已包含的路线投影补充

当前副本文件还包含：

- `mapLegalRoute`：在基地投影纤维唯一、相邻投影节点不同的条件下映射合法路线。
- `mapLegalRoute_vertices`：完整路线节点序列（包括两端基地）等于原序列的逐点投影。
- `projection_separates_supported_route`：路线每条边在副本流上为正时，
  精确投影和物理无自环自动推出相邻投影节点不同。
- `projectSupportedCopyRoute`：将上述结论与具体访问副本类型接起来，
  得到合法物理路线；允许不相邻位置重复访问同一物理节点。

这里的路线支持条件仍是显式输入。没有额外假设同物理节点副本间无边。

## 5. 本次实际验证及边界

在现有本地 JSP 扩展工程中实际执行：

```powershell
lake build LeanCompletion.UAV.SingleVisitDecomposition LeanCompletion.UAV.VisitCopyLift
```

最终本次调用退出码为 0。SingleVisitDecomposition 的构建记录被 Lake 重放，
VisitCopyLift 的最终快照从源文件构建成功。
两文件检查时与发布快照的 SHA-256 一致。
使用 Lean `4.30.0-rc2`，mathlib 固定提交为
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

两个文件的 `#print axioms` 报告均不含 `sorryAx`，
所列公理仅为 `propext`、`Classical.choice`、`Quot.sound` 或其子集。
有格式/未使用假设等 linter 警告，不能称为无警告构建。
早先副本草稿曾因 `Finset.single_le_sum` 推断失败而构建失败；
最终发布的是后来通过检查的显式参数版本，早先失败不计为 PASS。

本次复用既有依赖与构建缓存。导入链 ResourceCuts、Connectivity、
TotalFlow、RouteToFlow、Flow 的本地 Git 内容哈希与目标分支相同。
本次不是独立 UAV 仓库的干净环境重建，也不是完整仓库回归检查。
原始输出只保存在本地忽略目录 `verification/runs/`，不上传。

目标仓库准备好锁定依赖后，可使用同一条显式模块构建命令复现；
本次没有改动默认 Lake 入口。

## 6. 后续接续点

单次访问基准已完成，不必重写。后续在副本提升模块中继续证明：

1. 路线投影与访问次数、聚合边流、服务费用的对应关系；
2. 满足指定物理边重数的副本流存在性，以及相应度约束和连通性；
3. 将单次访问基准用于副本层，并证明预算可行分解之间的完整映射。

当前文件尚未证明任意重复访问物理流都存在合适提升，也未证明物理层的
全部容量割自动推出副本层的全部容量割。不能把本轮结果表述为一般重复
访问模型的完整充分性定理。历史反例和文献新颖性边界继续有效。
