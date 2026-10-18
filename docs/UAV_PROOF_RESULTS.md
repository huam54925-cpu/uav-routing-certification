> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/0d4466cbfacf3fe01ca98494663742f9a612b645/docs/UAV_PROOF_RESULTS.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# UAV 合法机队、连通性割与有理数弱对偶：证明结果

更新日期：2026-10-18。本文区分各阶段实际执行的验证。本次发布汇总此前本地完成的检查，不将发布操作表述为新执行的 Lean 编译。

本分支收录十三个证明模块：[WeakDuality.lean](../LeanCompletion/UAV/WeakDuality.lean)、[Flow.lean](../LeanCompletion/UAV/Flow.lean)、[RouteToFlow.lean](../LeanCompletion/UAV/RouteToFlow.lean)、[TotalFlow.lean](../LeanCompletion/UAV/TotalFlow.lean)、[Connectivity.lean](../LeanCompletion/UAV/Connectivity.lean)、[LPBridge.lean](../LeanCompletion/UAV/LPBridge.lean)、[Case1Data.lean](../LeanCompletion/UAV/Case1Data.lean)、[Case1Distance.lean](../LeanCompletion/UAV/Case1Distance.lean)、[Case1Budget.lean](../LeanCompletion/UAV/Case1Budget.lean)、[Case1Certificate.lean](../LeanCompletion/UAV/Case1Certificate.lean)、[Case1Numerics.lean](../LeanCompletion/UAV/Case1Numerics.lean)、[Case1Fleet.lean](../LeanCompletion/UAV/Case1Fleet.lean)、[Case1Infeasible.lean](../LeanCompletion/UAV/Case1Infeasible.lean)。均使用 `UAVProof` 及其子命名空间，复用固定版本的 Mathlib。

已完成任意有限机队的访问次数、基地出入次数、流量守恒、无自环、容量、连通性割，以及自然数边流到有理数 LP 的结构性衔接。`UAVProof.Case1Data.three_routes_weak_duality` 用固定 Case1 数据调用 `LPBridge.legalFleet_weak_duality`，得到具体有理数表达式的路线成本下界。新增模块将该成本连接到真实欧氏距离，并从逐机工作时间推出 1155 公里预算。此前 `Case1Budget.three_routes_infeasible_of_certificate` 的数值前提现已由 `Case1Certificate.certificate_value` 闭合。最终入口 `Case1Infeasible.feasible_fleet_card_ge_four` 不再需要数值假设，并统一排除 0–3 架；详见 [证书数值闭合与至多三机排除](CASE1_KERNEL_CLOSURE_STATUS.md)。

## 已证明的结果

### 最新阶段：数值闭合与至少四机

`Case1Certificate.certificate_value` 在 Lean 内核中证明具体证书等于 `2316798209 / 2` 个百万分之一公里，即 1158.3991045 公里。`Case1Fleet` 证明车辆数减少时的保守下界，`Case1Infeasible` 将其与逐机九小时时限比较，证明当前模型下至少四架。四个新模块及十个关键定理的传递公理审计已在原验证环境通过，依赖仅有 `propext`、`Classical.choice`、`Quot.sound`；发布时只核对源码与记录，没有重跑检查。

用户于 2026-10-18 提供的四机独立 Python 可行性验证为 PASS、`FeasibleExitCode=0`。结合 Lean 下界，可得指定模型下最少四架的混合验证结论；四机可行见证尚未在 Lean 内核中形式化。

### 通用有限维弱对偶

`WeakDuality.lean` 包含四个已完成的定理：

| 定理 | 结论 |
| --- | --- |
| `bounded_reduced_cost` | 若 `0 ≤ x ≤ u`，则 `u * min 0 q ≤ q * x`。 |
| `bounded_reduced_cost_sum` | 将上述不等式推广到有限指标集上的求和。 |
| `weak_duality_from_decomposition` | 从目标函数分解推导带变量上界修正的弱对偶下界。 |
| `finite_weak_duality` | 对有理数系数、有限指标集、变量界、等式约束和下界不等式约束，证明通用弱对偶不等式。 |

最后一个定理假设 `0 ≤ x(e) ≤ u(e)`、`Σ A(i,e)x(e) = b(i)`、`Σ C(k,e)x(e) ≥ 1`，以及割乘子 `z(k) ≤ 0`。令

```text
q(e) = c(e) - Σ_i y(i) A(i,e) + Σ_k z(k) C(k,e),
```

则证明

```text
Σ_i y(i)b(i) - Σ_k z(k) + Σ_e u(e) min(0, q(e)) ≤ Σ_e c(e)x(e).
```

这些是通用数学定理，不含 Case1 的具体数据或数值下界。

### 路线端点计数与流量守恒

`routeFlow route i j` 定义为相邻顶点对 `(i,j)` 在 `route.zip route.tail` 中出现的次数；重复经过同一条边按次数计数。`outFlow` 和 `inFlow` 分别对终点、起点求和。

| 定理 | 结论 |
| --- | --- |
| `outFlow_eq_source_count` | 在有限顶点类型上，出流等于路线边起点列表的出现次数。 |
| `inFlow_eq_target_count` | 在有限顶点类型上，入流等于路线边终点列表的出现次数。 |
| `route_endpoint_count_balance` | 边起点计数加路线末端计数，等于边终点计数加路线首端计数。 |
| `closed_route_flow_balance` | 若 `route.head? = route.getLast?`，则每个顶点的总出流等于总入流。 |

端点计数使用 `Option.toList.count`，因此空路线也有明确语义。归纳证明中的 `hsingle` 显式将单元素列表计数化为对应的 0/1 指示函数，再由 `omega` 使用归纳假设。闭合路线定理直接利用端点恒等式和首尾相等条件消去端点项，没有额外假设流量守恒。

`Flow.lean` 的流量求和包括所有顶点。后续模块证明合法路线及其总边流的对角项均为零；`LPBridge.lean` 据此证明仅对非自环弧求和与完整顶点对求和一致。

### 单条合法路线：RouteToFlow.lean

`LegalRoute depot` 保存巡检列表 `visits`，要求任务非空、内部不含基地，以及完整路线 `(depot :: visits) ++ [depot]` 的相邻节点不同。没有 `Nodup` 条件，允许 `A → B → A`，也允许重复经过同一条有向边。

该文件包含 11 个已证明的定理；除第一项外，下表名称均位于 `UAVProof.LegalRoute` 命名空间。

| 定理 | 结论 |
| --- | --- |
| `UAVProof.route_edge_ne_of_isChain` | 相邻节点不同的列表中，每条相邻边的端点不同。 |
| `closed` | 合法路线的首尾都是基地，满足已有守恒定理的闭合条件。 |
| `inFlow_eq_visits_add_depot` | 入流等于内部巡检计数加返回基地的指示项。 |
| `inFlow_eq_visit_count`、`outFlow_eq_visit_count` | 非基地节点的出入流等于实际巡检次数。 |
| `inFlow_depot_eq_one`、`outFlow_depot_eq_one` | 每条合法路线返回基地一次、离开基地一次。 |
| `routeFlow_self_eq_zero` | 所有自环计数为零，不要求顶点类型有限。 |
| `inFlow_eq_degree`、`outFlow_eq_degree` | 出入流都等于 `degree`：基地为 1，其他节点为实际巡检次数。 |
| `routeFlow_bounds` | 单条路线满足 `0 ≤ x(i,j) ≤ min(degree(i), degree(j))`。 |

单机访问次数和基地计数来自列表定义与已证明的计数引理，不是作为额外流量约束假设输入。

### 任意有限机队：TotalFlow.lean

`ks : Finset ι` 是无人机编号集合，`routes : ι → LegalRoute depot` 是合法路线映射。`totalRouteFlow ks routes i j` 对选中的编号求和，而不是将路线列表去重；两架无人机执行相同路线仍计为两条路线。`totalVisitCount` 是对应巡检列表出现次数的总和。

该文件包含以下 15 个定理，均位于 `UAVProof` 命名空间：

| 定理 | 结论 |
| --- | --- |
| `total_no_diagonal` | 从各条路线的合法性推出总边流无自环。 |
| `total_outFlow_eq_sum`、`total_inFlow_eq_sum` | 总出入流分别等于各路线出入流之和。 |
| `total_outFlow_eq_sum_degree`、`total_inFlow_eq_sum_degree` | 总出入流等于各路线实际节点度之和。 |
| `total_flow_balance` | 总边流在所有节点守恒。 |
| `total_outFlow_eq_visit_count`、`total_inFlow_eq_visit_count` | 非基地节点的总出入流等于实际总巡检次数。 |
| `total_outFlow_depot_eq_card`、`total_inFlow_depot_eq_card` | 基地总出入流均为 `ks.card`。 |
| `total_outFlow_eq_fleetDegree`、`total_inFlow_eq_fleetDegree` | 实际巡检次数符合规定次数时，总出入度符合规定度。 |
| `flow_bounds_of_degrees` | 通用自然数边流满足给定出入度时，每条弧不超过两端度的最小值。 |
| `total_routeFlow_bounds` | 将通用容量定理应用于实际合法机队，得到非负性与规定容量上界。 |
| `totalFlow_constraints` | 汇总规定出度、规定入度、无自环和容量约束。 |

具体地，输入覆盖条件是巡检列表的事实：

```text
∀ i ≠ depot, totalVisitCount ks routes i = required(i).
```

定义 `b(i) = if i = depot then ks.card else required(i)`，即可得到：

```text
outFlow(totalRouteFlow)(i) = inFlow(totalRouteFlow)(i) = b(i),
totalRouteFlow(i,i) = 0,
0 ≤ totalRouteFlow(i,j) ≤ min(b(i), b(j)).
```

总度和容量没有作为机队入口定理的假设传入；它们由合法路线与实际覆盖条件推出。通用辅助定理 `flow_bounds_of_degrees` 的度假设在机队应用时由前面的定理逐项提供。

取 `ι = Fin m`、`ks = Finset.univ` 就得到任意 `m` 的版本，三机取 `m = 3`。空机队也被覆盖。这里 `m` 表示执行非空任务的路线数量，不包括空闲无人机；覆盖条件要求次数恰好相等，不能仅凭“至少访问规定次数”使用规定度结论。

### 连通性割：Connectivity.lean

该模块包含七个定理。出割只计起点属于集合、终点在集合外的有向边。

| 定理 | 结论 |
| --- | --- |
| `route_exit_exists` | 有限列表访问集合且终点在集合外，则存在离开集合的相邻边；无需起点在集合外。 |
| `route_exit_flow_pos` | 所见证的离开边计数至少为 1。 |
| `arc_le_outCutFlow` | 任一跨割自然数边流不超过整个出割流量。 |
| `LegalRoute.outCutFlow_ge_one` | 合法路线实际访问不含基地的集合，则出割流至少为 1。 |
| `total_outCutFlow_ge_one_of_visit` | 有限机队中有一条选中路线访问集合，即可得到总出割下界。 |
| `total_outCutFlow_ge_one_of_positive_visit` | 集合内某点的实际访问次数为正，即可提供访问路线见证。 |
| `total_outCutFlow_ge_one` | 精确覆盖且非空集合各点需求为正、集合不含基地时，总出割流至少为 1。 |

非空集合本身不足以推出割下界；实际访问或正需求见证不可省略。后续 LP 接口采用集合内至少一个正需求节点的条件，不要求集合内每个节点的需求都为正。

### 有理数 LP 衔接：LPBridge.lean

九个定理完成非自环弧求和、出入度矩阵、割矩阵、自然数到有理数的容量转换、目标函数与实际路线按边计费之和的等式，并实际应用 `finite_weak_duality`。完整定义、定理清单和前提见 [LPBridge 说明](LP_BRIDGE_STATUS.md)。

最终结论为 `certifiedBound ≤ routeCost`。容量、度和割约束由合法路线及精确访问覆盖推导，没有作为额外 LP 可行性假设传入。成本仍是抽象有理数，不能自动解释为 Case1 的真实欧氏距离。

### 固定 Case1 数据：Case1Data.lean

固定 53 个节点、72 次巡检、三条非空路线、106 个等式对偶系数及 32 个割与割乘子。行索引双射明确将 `Sum.inl i` 对应到 `eq_dual[i]`，将 `Sum.inr i` 对应到 `eq_dual[53+i]`。非自环弧集合的数量证明为 2756。模块逐个证明割的正需求见证、基地排除及乘子非正，然后实际调用通用机队弱对偶。

17 个定理的完整列表、输入哈希、成本单位与复现步骤见 [Case1Data 报告](CASE1_DATA_STATUS.md)。JSON 与 Lean 字面量的对应由外部 Python 精确解析和生成区逐字核对，未将 JSON 解析本身形式化。成本函数采用整数平方距离及 `Nat.sqrt`；与真实欧氏距离的比较由下面的新模块完成。

### 物理距离与工作时间：Case1Distance.lean、Case1Budget.lean

六个距离定理证明整数平方根成本保守、自然数平方距离与实数坐标公式一致，以及逐弧比较在机队求和后仍成立。固定证书表达式因此不超过真实路线总距离，单位换算明确为百万分之一公里到公里。

七个预算定理从合法路线和精确覆盖推出 72 次巡检，再从每机九小时、55 公里/小时及每次五分钟服务推出 `D ≤ 55 * (9 * m - 6)`。至多三条路线的预算上界为 1155 公里。最终条件性定理连接已有弱对偶、物理距离比较和预算，但保留 `(2316798209 : ℚ) / 2 ≤ certificateBoundUnits` 这一数值前提。

新增 [独立成本核对脚本](../LeanCompletion/UAV/certificates/verify_case1_costs.py) 对全部 2756 条非自环弧逐一核对原 JSON 与固定 Lean 源码公式的坐标、顺序、单位和精确整数平方根。该检查不是 Lean 运行时导出，也不是内核中的 2756 个数值等式证明。定理与核对方法详见 [专门报告](CASE1_PHYSICAL_BUDGET_STATUS.md)。

## 实际验证与公理审计

### 首轮记录（提交 01a1250c 的基础结果）

以下八个定理的编译与审计在此前步骤实际执行。本轮未将其重新表述为新执行的检查，也未修改这两个基础源文件。

| 检查 | 首轮结果 |
| --- | --- |
| 对原始 `Flow.lean` 执行 `lake env lean LeanCompletion/UAV/Flow.lean` | 退出码 0，无警告。 |
| 在 `Flow.lean` 的完整源码副本后追加四个 `#print axioms` 并编译 | 退出码 0；已确认副本的源码前缀与此次上传的源文件一致。 |
| 在 `WeakDuality.lean` 的完整源码副本后追加四个 `#print axioms` 并编译 | 退出码 0，无警告。 |
| 两个文件的八个定理 | 没有 `sorryAx` 依赖；源码没有 `sorry` 或 `admit`。 |

`route_endpoint_count_balance` 的公理依赖为 `propext`、`Quot.sound`。其余七个定理的公理依赖均为 `propext`、`Classical.choice`、`Quot.sound`，没有额外自定义公理依赖。

### 单机与总边流阶段记录（提交 bf1b2362 的结果）

| 检查 | 实际结果 |
| --- | --- |
| 编译 `RouteToFlow.lean` 并生成供新模块导入的 `.olean` | 退出码 0，无警告；源码与上一小步通过审计的版本一致。 |
| 编译最终 `TotalFlow.lean` | 退出码 0，无警告。 |
| 在 `TotalFlow.lean` 的完整源码副本后追加公理审计和边界例子并编译 | 退出码 0，无警告；检查了本文件 15 个定理和导入的 `RouteToFlow.lean` 11 个定理。 |
| 26 个定理的公理审计 | 无 `sorryAx`，无额外自定义公理依赖。 |
| 边界例子 | 三架执行相同路线仍分别计数；相同有向边合计 6 次；编号子集只计选中路线；基地出入流为 3；未访问点边流为 0；空机队总流为 0；任意 `Fin m` 机队的基地出入流均为 `m`。 |

新增模块的精确公理依赖分类如下：`route_edge_ne_of_isChain`、`LegalRoute.closed` 仅依赖 `propext`；`LegalRoute.routeFlow_self_eq_zero`、`total_no_diagonal` 依赖 `propext` 和 `Quot.sound`；其余 22 个定理依赖 `propext`、`Classical.choice`、`Quot.sound`。

检查使用已有工程和 Mathlib 缓存，没有重新编译 Mathlib，也不是全新环境或 GitHub CI 验证。本轮原始输出、审计副本与例子保留在本地忽略目录 `verification/runs/total-flow-20261018-134843/`。发布内容只含证明源码和整理后的结果说明，不含原始日志、`.olean` 或缓存。

### 连通性割与 LPBridge 阶段记录（提交 2e7df928 的结果）

| 检查 | 实际结果 |
| --- | --- |
| 最终 `Connectivity.lean` 编译及完整源码副本审计 | 均退出码 0，无警告；七个定理公理检查与十个边界例子通过。 |
| 最终 `LPBridge.lean` 编译及完整源码副本审计 | 均退出码 0，无警告；九个定理公理检查、15 个例子及覆盖条件证明通过。 |
| 新增 16 个定理的公理依赖 | 均仅为 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或自定义公理。 |
| 发布前源码一致性 | 两个新增模块与各自最终审计副本的源码前缀一致；此前四个已发布模块未修改。 |

连通性割例子覆盖重复访问、相同路线分别计数，以及遗漏条件时的反例。LPBridge 的两节点例子使用非对称成本、非零对偶乘子和负剩余成本修正，通过入口定理取得下界 9，实际路线成本为 10。

检查使用原工程与现有 Mathlib 缓存，未做全新环境或 GitHub CI 重放。原始记录分别保留在本地忽略目录 `verification/runs/connectivity-20261018-140331/` 和 `verification/runs/lp-bridge-20261018-141656/`，不随本次发布上传。

### 固定 Case1 实例阶段记录（提交 37e9f21b 的结果）

| 检查 | 实际结果 |
| --- | --- |
| 最终 `Case1Data.lean` 编译及导入产物生成 | 均退出码 0，无警告。 |
| 对该产物中的 17 个定理执行公理审计 | 退出码 0，依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或自定义公理。 |
| 原 JSON 与生成字面量核对 | 退出码 0，覆盖坐标、需求、106 个等式系数、32 个割与乘子及割见证。 |
| 两条方向相反的成本样例 | Lean 和 Python 均得到 `80613274` 个百万分之一公里单位。 |
| 发布前源码核对 | 新源码和脚本与验收哈希一致，六个前序 Lean 模块保持不变。 |

本次发布没有重跑 Lean，也没有重新计算证书下界。附加批量运行时导出已中止，不计为 PASS。原始记录保留在本地忽略目录 `verification/runs/case1-data-20261018/`，未上传。

### 距离与预算阶段记录（提交 419c0df 的结果）

| 检查 | 实际结果 |
| --- | --- |
| 最终 `Case1Distance.lean` 和 `Case1Budget.lean` 编译 | 均退出码 0，无警告。 |
| 全部 13 个新定理的公理审计 | 退出码 0，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或自定义公理。 |
| 独立 Python 成本核对 | 退出码 0；全部 2756 条弧、对称性及模型预算常数检查通过。 |
| 发布前一致性核对 | 两个新增模块和脚本与最终验收哈希一致；此前七个 Lean 模块未修改。 |

本次发布复用上述已执行记录，没有重跑 Lean、重新求解或重新计算对偶下界。检查使用已有 Mathlib 缓存，不是全新环境或 GitHub CI 重放。原始编译、公理审计和 Python 输出留在本地忽略目录 `verification/runs/physical-budget-20261018/`，不上传。

## 验证环境与复现

- Lean：`leanprover/lean4:v4.30.0-rc2`，Windows x86_64；Lean 提交 `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`。
- Mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`，已核对本地依赖的 HEAD。
- 原验证工程：[jsp-001022-lean-extension](https://github.com/huam54925-cpu/jsp-001022-lean-extension/tree/e04a61f1be1219c27f43c0bf3182794654b57f99)。其 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 与该提交一致。十三个 UAV 源文件以本分支收录的版本为准。
- 原工程的 Prim 依赖固定为 `a303f6bd23bb8f29a833d1d70327528359180995`；这十三个源文件没有直接导入 Prim。

本分支没有另建 Lake 工程。复现时，使用上述固定版本的原验证工程并准备对应依赖与 Mathlib 编译缓存，将十三个源文件复制到其 `LeanCompletion/UAV/` 目录，在该工程根目录执行以下命令。先生成导入所需的 `.olean`，避免只检查源文件却缺少下游模块可用的编译产物：

```powershell
New-Item -ItemType Directory -Force .lake/build/lib/lean/LeanCompletion/UAV | Out-Null
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/WeakDuality.olean LeanCompletion/UAV/WeakDuality.lean
if ($LASTEXITCODE -ne 0) { throw 'WeakDuality compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Flow.olean LeanCompletion/UAV/Flow.lean
if ($LASTEXITCODE -ne 0) { throw 'Flow compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/RouteToFlow.olean LeanCompletion/UAV/RouteToFlow.lean
if ($LASTEXITCODE -ne 0) { throw 'RouteToFlow compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/TotalFlow.olean LeanCompletion/UAV/TotalFlow.lean
if ($LASTEXITCODE -ne 0) { throw 'TotalFlow compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Connectivity.olean LeanCompletion/UAV/Connectivity.lean
if ($LASTEXITCODE -ne 0) { throw 'Connectivity compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/LPBridge.olean LeanCompletion/UAV/LPBridge.lean
if ($LASTEXITCODE -ne 0) { throw 'LPBridge compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Data.olean LeanCompletion/UAV/Case1Data.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Data compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Distance.olean LeanCompletion/UAV/Case1Distance.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Distance compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Budget.olean LeanCompletion/UAV/Case1Budget.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Budget compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Certificate.olean LeanCompletion/UAV/Case1Certificate.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Certificate compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Numerics.olean LeanCompletion/UAV/Case1Numerics.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Numerics compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Fleet.olean LeanCompletion/UAV/Case1Fleet.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Fleet compilation failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Infeasible.olean LeanCompletion/UAV/Case1Infeasible.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Infeasible compilation failed' }
```

公理审计可在各文件的临时副本末尾追加对应定理的 `#print axioms UAVProof.<定理名>`，再执行 `lake env lean <副本路径>`。`LegalRoute` 下的定理需要使用 `UAVProof.LegalRoute.<定理名>`。全部定理名在上表列出；临时副本和输出应放在忽略目录中。示例核心审计指令为：

```lean
#print axioms UAVProof.LegalRoute.routeFlow_self_eq_zero
#print axioms UAVProof.total_outFlow_eq_fleetDegree
#print axioms UAVProof.total_inFlow_eq_fleetDegree
#print axioms UAVProof.total_no_diagonal
#print axioms UAVProof.total_routeFlow_bounds
#print axioms UAVProof.totalFlow_constraints
#print axioms UAVProof.total_outCutFlow_ge_one
#print axioms UAVProof.LPBridge.legalFleet_weak_duality
#print axioms UAVProof.Case1Data.three_routes_weak_duality
#print axioms UAVProof.Case1Distance.costUnits_km_le_distance
#print axioms UAVProof.Case1Budget.three_routes_distance_budget
#print axioms UAVProof.Case1Budget.three_routes_infeasible_of_certificate
#print axioms UAVProof.Case1Certificate.certificate_value
#print axioms UAVProof.Case1Infeasible.at_most_three_infeasible
#print axioms UAVProof.Case1Infeasible.feasible_fleet_card_ge_four
```

## 结论与尚未完成的形式化

当前固定实例及路线/时间模型下，Lean 已证明至多三架不可能满足要求，即至少需要四架。此前用户提供的独立 Python 四机可行见证验证给出至多四架；两者构成最少四架的混合验证结果。本次发布未重新运行这些检查，早期中止的运行时导出仍不计为 PASS。

剩余边界是四机可行见证尚未在 Lean 内核中形式化、JSON 与源码字面量的对应仍使用先前外部绑定检查，以及当前合法路线和精确覆盖条件与原题完整运行规则的对应。因此不将结果表述为全部原题规则下的纯 Lean `N_min = 4` 定理。
