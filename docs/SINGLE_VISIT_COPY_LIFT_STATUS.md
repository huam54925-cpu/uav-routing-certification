# 单次访问基准与访问副本提升：实现及验证记录

日期：2026-10-24（Asia/Tokyo）。发布目标：
`huam54925-cpu/uav-routing-certification` 的
`research/structural-service-cuts-20261023` 分支。
首次发布增量基于 `628b72f94ac3d21493c7c40c98ce8b82c6772729`。
2026-10-24 后续暂停快照基于 `7334c7df9e729f75a1d1b8ff932d6b820352db36`；
后续 22 项审计补充基于 `37edad4d9ddfef571c1307ad5d1ffc809106e62b`；
本次新增内容和证据边界见第 7 节及第 8 节。

## 当前状态补记（2026-10-27）

下文第 1–8 节保留 2026-10-24 的历史快照与当时验证范围。
其中“尚未完成”“暂停”等表述只描述当时状态，不代表当前源码。

- [f7147cf](https://github.com/huam54925-cpu/uav-routing-certification/commit/f7147cf13d043537fc1a2f2d361eee251b3685e6)
  已补齐提升充分性、从物理访问位置构造副本提升的反方向，并汇总
  `UAVProof.VisitCopyLift.serviceCopyLift_iff_exact_decomposition`。
  用户报告的本地编译及最终定理公理检查见
  [Issue #10](https://github.com/huam54925-cpu/uav-routing-certification/issues/10)。
- [8eca910](https://github.com/huam54925-cpu/uav-routing-certification/commit/8eca910242c8479647bc0214e59fabf07f33bfde)
  补充副本障碍、数量轮廓的表达限制及全部轮廓割等价性；
  见[对应状态记录](COPY_PROFILE_CUTS_STATUS.md)。
- [d2ee575](https://github.com/huam54925-cpu/uav-routing-certification/commit/d2ee5751dc6a01589bee5f99514f63076ef6406e)
  补充明确轮廓范围、完整分解接口和固定提升的精确最小割见证；
  见[三轮本地验证记录](COPY_PROFILE_DECOMPOSITION_STATUS.md)。

完整等价仍限于非负服务费用和正服务预算、无自环物理流等明确假设。
没有证明任意物理流都有合格提升，没有加入飞行费用，也未提供高效搜索算法。
本次仅同步说明，未重跑 Lean，未完成独立工程的干净重建。

## 1. 首次发布文件与结论

首次发布新增两个独立 Lean 模块：

- [SingleVisitDecomposition.lean](../LeanCompletion/UAV/SingleVisitDecomposition.lean)：
  单次访问精确分解及全部取整服务容量割的双向等价。
- [VisitCopyLift.lean](../LeanCompletion/UAV/VisitCopyLift.lean)：
  访问副本、物理节点投影、边流聚合投影、同物理节点副本间零流量，
  以及支持路线的合法投影。

首次发布时，两个源文件按当时检查通过的本地快照原样发布；发布整理没有改写证明。
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

首次发布时副本文件还包含：

- `mapLegalRoute`：在基地投影纤维唯一、相邻投影节点不同的条件下映射合法路线。
- `mapLegalRoute_vertices`：完整路线节点序列（包括两端基地）等于原序列的逐点投影。
- `projection_separates_supported_route`：路线每条边在副本流上为正时，
  精确投影和物理无自环自动推出相邻投影节点不同。
- `projectSupportedCopyRoute`：将上述结论与具体访问副本类型接起来，
  得到合法物理路线；允许不相邻位置重复访问同一物理节点。

这里的路线支持条件仍是显式输入。没有额外假设同物理节点副本间无边。

## 5. 首次发布的历史验证及边界

本节保留首次发布记录，不代表第 7 节扩展快照已经重新执行相同检查。

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

## 6. 暂停位置与后续接续点

单次访问基准已完成，不必重写。副本模块现在已有投影合法性、计数、
需求覆盖、精确边流和服务费用保持的源码，具体证据范围见第 7、8 节。
暂停时尚待完成：

1. 将副本层的单位度数、连通性和全部容量割，与单次访问预算分解定理组合，
   从副本流构造满足原需求和预算的物理精确分解；不得把已有副本路线族作为
   本应构造的对象直接假设掉。
2. 从物理路线的每次访问位置建立与规范访问副本的双射，构造提升流，
   证明副本度数、精确投影、连通性及非负服务费用下的容量割。
3. 汇总两个方向的完整副本提升等价定理，并再次核对路线数、服务规则、
   禁止相邻同物理点和途中不回基地的规则。

当前源码没有汇总上述提升充分性总定理，也没有完成从物理路线到副本流
的构造方向，因此不能宣布完整副本提升等价已经完成。
更不能声称任意重复访问物理流都有预算可行提升，或物理层容量割自动
推出所有副本子集的容量割。服务预算仍不含飞行费用；历史反例和文献
新颖性边界继续有效。

## 7. 2026-10-24 后续暂停快照：计数、边流和服务投影

本节记录此前 19 项输出的历史快照；最新补充见第 8 节。

本轮按用户上传的 `VisitCopyLift.lean` 原样更新源码，没有新增或改写证明，
没有给源文件补加审计命令。附件共 900 行、26153 字节，SHA-256 为：

```text
af49e247612aa97cd11a882545f94d18a854a9c42d12bc7e41b310250506777c
```

相对本轮基线新增 13 个命名声明：

| 分组 | 声明 | 含义 |
| --- | --- | --- |
| 访问计数 | `count_map_eq_fiber_sum`、`totalVisitCount_mapLegalRoute`、`mapped_count_eq_fiber_card` | 非单射投影下按纤维累加访问次数 |
| 规范副本与需求 | `taskFiberEquivFin`、`taskFiber_card`、`projected_copy_routes_cover` | 非基地节点的副本数量等于需求；副本各覆盖一次给出原需求覆盖 |
| 精确边流 | `routeFlow_map`、`projectFlow_sum`、`totalRouteFlow_mapLegalRoute`、`projected_copy_routes_exact` | 边计数和有限路线求和与投影交换；已有副本精确分解投影后精确恢复物理流 |
| 服务费用 | `routeServiceIn_mapLegalRoute`、`projected_copy_route_service`、`projected_copy_route_budget` | 按访问次数收费时，投影保持服务费用和给定路线预算 |

这些投影定理使用已有的副本路线或路线族，并按各自签名要求支持关系、
副本覆盖或副本精确分解。它们尚未构造满足全部条件的副本流或整族副本路线。

本轮还保留了两项实例兼容修复：计数引理显式接受 `BEq` 与 `LawfulBEq`，
以兼容端点对的相等判定；服务投影的基地分支显式统一
`instBEqOfDecidableEq`。数学计数规则没有改变。

### 验证证据的范围

- 用户提供的本地命令为 `lake env lean .\\LeanCompletion\\UAV\\VisitCopyLift.lean`，
  并报告 `LeanExitCode=0`。这是用户报告的本地结果，不是本次上传时重新运行的结果。
- 上传附件和用户日志均列出 19 个 `#print axioms` 声明，最后一个为
  `projected_copy_routes_exact`。这些输出均无 `sorryAx`，
  公理仅为 `propext`、`Classical.choice`、`Quot.sound` 或其子集；
  `taskFiberEquivFin` 报告不依赖任何公理。
- 附件还包含三个服务费用声明及基地分支的最新修复，但文件末尾及所贴日志
  未单独打印这三个声明的公理依赖。不得将现有 19 项审计输出说成这三项的独立审计。
  用户未提供本地已编译文件的哈希，因而未独立确认其与上传附件逐字节一致。
- 上传前进行了源码差异、导入依赖、命名声明和显式占位符静态检查；
  未发现 `sorry`、`admit`、`sorryAx`、新增 `axiom` 或 `unsafe` 标记。
  静态检查不能替代 Lean 编译或内核审计。
- 本次上传环境没有 Lean/Lake 可执行程序，未重新编译，也未进行干净环境重建。
  原始终端日志不提交；仅保存本节的整理记录。

当时尚待补充的三个声明如下；第 8 节已记录其后续输出：

```lean
#print axioms UAVProof.VisitCopyLift.routeServiceIn_mapLegalRoute
#print axioms UAVProof.VisitCopyLift.projected_copy_route_service
#print axioms UAVProof.VisitCopyLift.projected_copy_route_budget
```

本轮保留 `SingleVisitDecomposition.lean`、冻结 Case1 模块、数据、
证书、依赖锁定和默认构建入口不变。

## 8. 2026-10-24 审计补充：22 项输出齐全

按用户新上传的 `VisitCopyLift(1).lean` 原样更新仓库中的
`LeanCompletion/UAV/VisitCopyLift.lean`。与第 7 节源码逐字节比较，
唯一变化是文件末尾增加上述三个服务声明的 `#print axioms` 命令；
没有改写任何定义、定理陈述或证明。

新附件共 903 行、26350 字节，SHA-256 为：

```text
3c06c3cdf1167b2d89c2297ea0912a303d21f55aa33d4a27e9f565e08bd08d42
```

用户随后提供的本地执行结果报告 `LeanExitCode=0`，并列出全部 22 项
公理检查，包括 `routeServiceIn_mapLegalRoute`、
`projected_copy_route_service` 和 `projected_copy_route_budget`。
全部输出不含 `sorryAx`；依赖仅为 `propext`、`Classical.choice`、
`Quot.sound` 或其子集，`taskFiberEquivFin` 不依赖任何公理。

因此，服务费用和预算保持的三项独立公理输出现已补齐。
以上仍是用户报告的本地编译及审计结果；本次同步没有重新运行 Lean。
附件哈希用于标识发布源码，用户未提供本地编译文件哈希，
不将其表述为已经完成本地编译文件与附件的哈希绑定。

研究保持暂停。完整提升充分性总定理及从物理路线构造副本流的反向证明
仍未完成；此更新仅补齐审计命令和验证记录，不扩大数学结论。
