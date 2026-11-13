# #19：可执行压缩状态 DP 与完整精化

日期：2026-11-13。基于提交 `3c8da01ef3a9c63675a43dd0d4a4db3431ff225a`
已经证明的 `CompactRep` 与压缩合并定理，实现精确判定器。
保持原有矩阵语义及压缩状态语义不变；费用使用精确的带符号有理数。

## 公开接口

命名空间为 `UAVProof.TreeBudgetSubtreeExecutable`，顶点限定为 `Fin N`。
输入 `R : RootedTree (Fin N)` 包含合法树结构及严格下降的孩子 rank。
`H : Fin N → ℕ` 为边重数，`s : Fin N → ℚ` 为服务费用，`m` 为路线数。

```lean
computeCompact R H s m v : List (ExecCompactState m)
checkCompact R H s m T : Bool
```

核心定理：

```lean
computeCompact_spec ... (hv : v ≠ R.root) (e : ExecCompactState m) :
  e ∈ computeCompact R H s m v ↔
    CompactRep R H m s v (decodeState e)

checkCompact_eq_true_iff ... :
  checkCompact R H s m T = true ↔ MatrixFeasible R H m s T

checkCompact_eq_false_iff ... :
  checkCompact R H s m T = false ↔ ¬ MatrixFeasible R H m s T
```

`computeCompact` 的语义定理只用于非根顶点；整个实例使用 `checkCompact`。
`checkCompact_exact_iff` 进一步接通原路线语义，并保留 `HasDegrees` 假设。
失败完备性不意味着输出独立的不可行性证书。

## 实现及证明分层

| 文件 | 作用与对应证明 |
| --- | --- |
| [TreeBudgetSubtreeExecutable.lean](../LeanCompletion/UAV/TreeBudgetSubtreeExecutable.lean) | 显式 `childrenList`、无重复及求和桥接；`ExecCompactState` 的 `Vector Bool m` / `Vector ℚ m` 表示；编码解码往返。 |
| [TreeBudgetSubtreeCandidates.lean](../LeanCompletion/UAV/TreeBudgetSubtreeCandidates.lean) | 按剩余总量递归枚举列，`compositionsV_spec` 证明成员关系恰为列和条件；`localCandidates_spec` 只为根的直接孩子增加顶边次数上限。 |
| [TreeBudgetSubtreeFold.lean](../LeanCompletion/UAV/TreeBudgetSubtreeFold.lean) | 内部与根的逐孩子合并，以及 `insideCosts_spec`、`rootFold_spec` 的双向不变量；无重复孩子列表上的选择与全局标签函数之间的对应。 |
| [TreeBudgetSubtreeDP.lean](../LeanCompletion/UAV/TreeBudgetSubtreeDP.lean) | 按 `R.rank` 终止的递归、`nodeTable_spec`、表成员精化及最终 true／false 判定等价。 |
| [TreeBudgetSubtreeDPExamples.lean](../LeanCompletion/UAV/TreeBudgetSubtreeDPExamples.lean) | 直接执行新 Lean 判定器的 21 项回归。 |

执行路径没有调用非计算的 `R.children`、`Classical.decEq` 或存在性选择。
证明可以使用 `classical`；可执行代码采用有限枚举、向量及具体可判定比较。
现有完整路线候选检查器没有用于生成局部列。

每个节点先把孩子的完整结果表存入一个列表，再进入局部次数向量循环。
孩子表不会随着每个局部 `q` 重新递归计算。
内部折叠固定 `A = support q`，从费用 `a(v) q` 开始逐孩子相加，
只保留孩子活跃集合包含于 `A` 的组合。父活跃集合不会替换为孩子集合的并。
`insideCosts_spec` 对任意孩子表列表给出选择合法性与精确费用和，
再由 `nodeTable_spec` 接上已有 `compactRep_merge_iff`。

程序使用右折叠，因此先合并列表尾部，再逐个加入前面的孩子。
不变量对任意已处理列表成立，不要求特定枚举顺序。
每一步按完整累计状态相等去重；固定内部活跃集合时只需对费用向量去重，
节点最终再对活跃集合和费用向量一起去重。

根单独处理，没有局部次数枚举或根服务费用。
`ExecRootState.used : Vector ℕ m` 是已分配集合的 0/1 表示；
`rootFold_spec` 证明每个返回坐标至多为一，且等于已选孩子活跃指示量之和。
因此超过一的合并恰对应重复分配，可以立即拒绝。
最终要求每个坐标为一，并检查逐路线费用上界。
内部或根的中间费用均不按预算剪枝。

## 验证及复现

在现有缓存环境中，从仓库根目录执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSubtreeDPExamples
lake env lean verification/AuditTreeBudgetSubtreeDP.lean
python tools/check_tree_budget_subtree_states.py
```

本轮最终模块构建通过；`#eval runEvaluationCases` 实际运行通过全部 21 项回归。
审计源 [AuditTreeBudgetSubtreeDP.lean](../verification/AuditTreeBudgetSubtreeDP.lean)
覆盖全部 32 个公开定理及 6 个执行入口，最终审计通过。
所有审计项的公理依赖均包含于 `propext`、`Classical.choice`、`Quot.sound`，
没有 `sorryAx` 或新增公理。执行定义的公理输出可能包含证明参数的依赖，
不表示运行时调用经典选择；上述新执行器已经由 Lean 实际求值。

Lean 回归包含：零路线、只有根、零重数子树、孩子次数大于父次数、
负费用抵消、非整数有理费用的临界预算、根孩子重叠和未覆盖、
根孩子次数超过一、父活跃但没有活跃孩子，以及压缩碰撞去重。
碰撞例中四个列和候选得到三个压缩状态；另有整树接受结果检查。
根初始费用为零而预算为负的可行例，保护根折叠不做费用剪枝。

已有 Python 5,500 组独立矩阵枚举回归也在本次重新运行通过。
它是公式层面的额外参照，不能替代上述新 Lean 执行器回归。
原始输出仅保留在忽略的 `verification/runs/issue19-dp-20261113/`。
复用现有工具链与依赖缓存，没有安装新环境、编译 TeX，或声称全新环境复现。
验证在现有 `jsp001022extension` 工作区进行，发布目标使用独立的
`uavroutingcertification` 包配置。新增模块所需的 23 个既有 Lean 模块已与发布基线比对：
除换行及两个文件末尾空行外一致。两边的 Lean `v4.30.0-rc2` 与 mathlib 固定提交
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` 一致。

## 后续范围

本包交付可运行且有正确完备性证明的基准实现。
见证回溯、输出路线、状态数量界、性能统计、整数缩放与 #23 的机器成本均留待后续。
未证明压缩一定使运行时间更短，也未把失败布尔值称为简短不可行性证书。
