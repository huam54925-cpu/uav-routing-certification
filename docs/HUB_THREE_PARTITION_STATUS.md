# Issue #23：严格单枢纽三划分语义包

> 当前导航（2026-11-07）：本文件保留 `dcc3db8` 语义包的历史验收与发布记录。后续 `86993ec` 的编码/复杂度仍属[纸面结果](HUB_THREE_PARTITION_ENCODING.tex)；本批检查器、编号模型及数学 A/B 的实际新验证见 [HUB_INTERFACES_STATUS.md](HUB_INTERFACES_STATUS.md)，公开有限检查入口见[复跑说明](REPRODUCING_BOUNDED_CHECKS.md)。下文“下一批”是原包完成时的安排，不是当前未完成状态。

日期：2026-11-07（Asia/Tokyo）。本批完成三个有限算术步骤及其与既有路线—矩阵定理的组合，已在现有本地环境执行定向构建和公理审计。完成范围是语义 iff，不是整个 #23；没有修改远端议题、提交或推送。

以上及下文验收段描述开发完成时的状态；随后按用户要求进行的发布核对另记于文末。

## 模型与主结论

[HubThreePartition.lean](../LeanCompletion/UAV/HubThreePartition.lean) 的命名空间为 `UAVProof.HubThreePartition`。源项目类型是 `Item m = Fin (3 * m)`，权重 `a` 和预算 `B` 为自然数。`ValidInput a B` 要求：

```text
0 < B
∀ i, B < 4 * a i ∧ 2 * a i < B
Σ i, a i = m * B
```

`input_item_pos` 证明权重为正；`strict_bounds_iff` 证明这两个整数不等式恰好等价于有理数中的 `B/4 < a_i < B/2`，没有使用截断的自然数除法。

`ThreePartition a B` 是一个分配函数 `Item m → Fin m`，其每个纤维恰有三个项目、总重量恰为 `B`。`groups_disjoint` 和 `item_in_unique_group` 明确证明分组互不相交、每项恰属一组；相同重量的不同项目仍是不同元素。

目标直接使用既有 `HubSpokeSupportExact.Node`、`canonicalFlow` 和 `required`：基地—枢纽边每方向重数为 `m`，每条叶边每方向重数为 1，叶需求为 1，枢纽需求为 `4*m`。基地与枢纽服务费为零，叶服务费是 `a_i` 的有理数解释，逐路线预算为 `B`，路线数为 `m`。完整路线仍服从原来的非空任务、无中途基地、重复访问按次计费语义。

主定理是：

```lean
theorem exact_iff_threePartition {m : ℕ} (a : Item m → ℕ) (B : ℕ)
    (h : ValidInput a B) :
    RoutingFeasible a B ↔ ThreePartition a B
```

`RoutingFeasible` 展开后就是上述规范单枢纽输入的 `SupportExactFeasibility.ExactFeasible`。证明复用 `HubSpokePacking.exact_iff_matrix`，没有重新实现路线构造或树分解。包含 `m=0` 的空路线族；没有引入空的单条路线。

## 交付文件与证明结构

| 文件 | 新增定理 | 内容 |
| --- | ---: | --- |
| [HubThreePartitionArithmetic.lean](../LeanCompletion/UAV/HubThreePartitionArithmetic.lean) | 4 | 单位列唯一行、单位列分配函数、逐行预算饱和、饱和组恰为三项。对通用有限类型证明。 |
| [HubThreePartition.lean](../LeanCompletion/UAV/HubThreePartition.lean) | 13 | 源实例、分组、规范目标与自然数矩阵定义；严格界换算、纤维性质、枢纽需求、矩阵桥及最终 iff。 |
| [HubThreePartitionExamples.lean](../LeanCompletion/UAV/HubThreePartitionExamples.lean) | 16 | 具体输入、端到端可行/不可行、空族、严格边界和总重假设回归。 |

四个算术入口是 `unit_column_unique`、`unit_column_assignment`、`row_loads_saturate`、`card_eq_three_of_sum_eq`。单位列使矩阵成为一个分配函数的指示矩阵；总重量等于总容量且每行不超预算，使每行都饱和；双侧严格界再把组基数限定为三。

`matrix_iff_unitMatrix` 在有理服务费与自然数负载之间作精确转换。`routing_iff_unitMatrix` 不需要源实例有效性；`threePartition_implies_unitMatrix` 也不需要严格界或总重假设。只有从任意预算可行矩阵推出三划分的方向使用这些假设。零叶行没有被矩阵定义排除，而是由饱和和正预算排除。

## 回归范围

- 有效有解：`m=2, B=30, a=[9,10,11,9,10,11]`，用显式分配得到三划分，再由主定理得到精确路线可行性。
- 有效无解：`m=2, B=30, a=[9,9,9,13,10,10]`。全部源假设成立，但没有三划分，因此没有目标精确可行路线族。
- 空族：`m=0, B=1`，空权重函数、空分配与空路线族。
- 上界等号：两项各 15、预算 30，满足严格下界及弱上界，饱和组基数为 2。
- 下界等号：四项各 8、预算 32，满足弱下界及严格上界，饱和组基数为 4。
- 精确结构：`m=2` 时枢纽需求 8、每叶需求 1、基地边每方向重数 2、叶边每方向重数 1。
- 总重必要性：`m=2, B=15, a≡4` 满足逐项严格界，路线可行，但总重仅 24，不能三划分成每组重量 15。该回归明确证明 `¬ValidInput`，没有把它称为有效源实例。

具体有限决策使用 `decide +kernel`；未枚举完整路线、未使用 `native_decide`。正反实例通过同一个一般语义 iff 接到原有路线模型。

## 本次实际验证

在现有开发项目根目录、锁定工具链 `leanprover/lean4:v4.30.0-rc2` 下执行：

```powershell
lake build LeanCompletion.UAV.HubThreePartitionArithmetic
lake build LeanCompletion.UAV.HubThreePartition
lake build LeanCompletion.UAV.HubThreePartitionExamples
lake env lean verification/runs/issue23-semantic-20261107/Audit.lean
```

上述最终命令均退出 0。三个新模块实际编译，构建分别报告 8321、8322、8323 jobs；已有依赖缓存及前一步已构建模块按需复用。这不是全新环境构建、独立发布工作区构建或远端 CI。

统一审计重新导入已构建模块，对全部 **44 个新增声明**逐项执行 `#print axioms`：包括 **33 个定理和 11 个定义/缩写**。结果均不依赖公理，或仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集；没有 `sorryAx`。源码检查没有 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。

算术模块保留一条非致命 `unusedDecidableInType` 提示：`unit_column_unique` 的 `DecidableEq R` 可移入证明中的 `classical`。组合模块与回归模块没有新增警告。旧依赖回放的提示没有被误算成新模块问题。

算术首轮有局部类型推断/改写错误；回归首轮有空类型依赖量化的消去写法错误。均已修复。失败检查、两个提前停止的声明探测及其输出不计为通过；只有上列最终成功构建和统一审计支持本记录。首次导入既有 Mathlib 依赖较慢，不将这段等待作为算法性能数据。

所有 **122 个快照内的既有文件**经前后 SHA-256 核对保持不变：包括既有 Lean 源码、根导入、工具链、Lake 配置、依赖锁定、冻结验证输入以及 #19 的单次游程文稿。未改动历史验证结论、README 或旧文稿的历史状态说明。

原始日志、审计输入/辅助脚本、哈希快照和生成结果仅在 ignored `verification/runs/issue23-semantic-20261107/`。最终成功记录是 `arithmetic-build.log`、`core-build-1.log`、`examples-build-2.log`、`audit-final.log`；自动核对结果是 `audit-results.json`。这些运行产物不纳入源码交付。

## 停止点与后续

本批完成 #23 的有限语义包。二进制输入/输出编码、构造规模与时间界、强 NP 困难性来源及适配、NP 成员性均未由本包证明，不关闭整个 #23。

下一批可先固定二进制表示并证明变换规模，再决定复杂度证明的接口和外部来源；不因语义 iff 成立就预先声明多项式归约。#19 按本轮指令保持在 [单次内部游程数学规格](TREE_BUDGET_SINGLE_EXCURSION_CONTRACT.tex)，未新增其 Lean 模块或一般树 DP。#22 的完整搜索模拟与位成本仍独立保留。

## 发布核对 — 2026-11-07

按用户要求发布到 `huam54925-cpu/uav-routing-certification` 的既有 `research/structural-service-cuts-20261023` 分支。独立发布工作区从 `135cdef388c4d091aac78c9dd41cefddd57f202e` 建立，网络访问明确使用当前系统代理 `http://127.0.0.1:7897`。发布内容限于三个新 Lean 模块、本验收说明、#19 单次游程 LaTeX 契约及 README 状态/导航同步，共六个文件。

三个新 Lean 文件与开发验收版本逐字节相同。其 `LeanCompletion` 导入闭包共 11 个模块，其中 8 个既有模块与发布目标在忽略换行及行尾空白后全部一致，没有证明代码差异。外部导入只有 `Mathlib` 与 `Mathlib.Tactic`。目标的工具链、9 个依赖的仓库 URL/锁定版本及 Lean 选项与开发环境一致；开发环境另有 `Prim`、`LeanArchitect`、`repl`，不复制到目标项目。

本次发布复用前述成功构建和公理审计，没有再次执行 Lean 构建、远端 CI 或 LaTeX 编译，也不称为独立重建。原始比较输出、检查脚本、运行记录及构建产物保持在 ignored `verification/runs/`。没有修改旧证明、冻结输入、工具链或依赖锁定，没有关闭议题或改变仓库可见性。
