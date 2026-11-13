# #19：子树状态、精确合并与支持集压缩

日期：2026-11-13。本包依据用户提供的
`issue19_today_plan_proofs_20261113_zh.tex` 实现独立矩阵语义及其递推契约。
未编译 TeX，未安装或重建 Lean 环境，未涉及 #23 的机器成本实现。

## 定义与定理

核心定义及主定理位于命名空间 `UAVProof.TreeBudgetSubtreeState`。

| 文件 | 内容 |
| --- | --- |
| [TreeBudgetSubtreeState.lean](../LeanCompletion/UAV/TreeBudgetSubtreeState.lean) | `InSubtree`、孩子子树不交分解、有限和分解、`PartialValid`、`BoundaryState`、`PartialRep`；坐标上界及顶边为零时整行归零。 |
| [TreeBudgetSubtreeMerge.lean](../LeanCompletion/UAV/TreeBudgetSubtreeMerge.lean) | 限制与拼接矩阵、费用恒等式、`partialRep_leaf_iff`、`partialRep_merge_iff`。 |
| [TreeBudgetSubtreeRoot.lean](../LeanCompletion/UAV/TreeBudgetSubtreeRoot.lean) | 根子树费用分解、`rootAccept_iff_matrixFeasible`、带显式 `HasDegrees` 假设的 `rootAccept_iff_exactFeasible`。 |
| [TreeBudgetSubtreeCompact.lean](../LeanCompletion/UAV/TreeBudgetSubtreeCompact.lean) | `subtreeLinearCost_eq`、`compactRep_iff_partialRep`、`compactRep_merge_iff`、`compactRootAccept_iff_matrixFeasible`。 |
| [TreeBudgetSubtreeExamples.lean](../LeanCompletion/UAV/TreeBudgetSubtreeExamples.lean) | 重复穿越、负费用抵消、根顶边上限、零路线与只有根的边界例子。 |

`PartialValid R H m v n` 独立于递推定义：矩阵 `n : Fin m → V → ℕ`
在子树外为零；子树内每列之和为 `H x`；除顶点 `v` 外，正坐标要求父坐标为正。
`PartialRep` 量化这样的矩阵，并要求顶列等于 `q`、逐路线子树费用等于 `cost`。
它没有局部预算约束，也没有把内部顶点改作新仓库。

完整状态合并严格使用

\[
q_i^u>0\Longrightarrow q_i>0,\qquad
c_i=s(v)\left(q_i+\sum_u q_i^u\right)+\sum_u c_i^u.
\]

没有加入 `qᵘ ≤ q`。正向限制矩阵到每个孩子子树；反向把顶列和任意合法孩子矩阵拼接。
不交分解保证每列恰覆盖一次，`subtreeCost_glue` 保证费用完全相等。

根接受要求每个路线标签的根孩子次数之和恰为一、孩子费用之和不超过预算。
它与原有 `MatrixFeasible` 双向等价，无须额外的费用非负假设。
根费用始终被忽略；返回原路线语义时仍明确要求已有桥接定理的 `HasDegrees`。

## 哪些次数可以删除

令 `β(v)` 在父节点为根时为零，否则为 `s(parent v)`，令 `a(v)=s(v)+β(v)`。
`subtreeLinearCost_eq` 对任意非根子树的局部行证明

\[
b_i=\sum_{x\in V_v}a(x)n_i(x)=c_i+\beta(v)q_i.
\]

`CompactRep` 独立量化合法矩阵，只保存带标签的活跃集合 `A={i:q_i>0}` 和线性费用 `b`。
父层仅检查孩子活跃集合包含于 `A`，并使用
`bᵢ = a(v) qᵢ + ∑ᵤ bᵘᵢ`。局部向量 `q` 仍作为生成状态时的存在量出现，
但不保存在压缩后的孩子状态中。

根的直接孩子另有 `RootChildCap`：每条路线顶边次数至多一。
`capped_eq_indicator` 把这时的次数转换为活跃集合指示量。
压缩根条件要求每个路线标签恰出现在一个孩子活跃集合中，并检查总费用；
即活跃集合两两不交且覆盖全部标签。未把此上限施加到更深的内部边。

这是当前树矩阵模型中带标签、存在性状态的充分性结果。
没有独立排序费用，没有对任意外部游走拼接作额外推广，也没有声称状态最小。

## 验证与复现

在仓库根目录、现有固定 Lean `v4.30.0-rc2` 与依赖缓存下执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSubtreeExamples
lake env lean verification/AuditTreeBudgetSubtree.lean
python tools/check_tree_budget_subtree_states.py
```

本次最终文件的定向模块构建通过，45 项公开定理公理审计全部通过。
依赖不超出 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。
审计源为 [AuditTreeBudgetSubtree.lean](../verification/AuditTreeBudgetSubtree.lean)。

[有限回归脚本](../tools/check_tree_budget_subtree_states.py) 改编自附件，
增加完整状态根费用集合的独立比对。本次实际重新运行 5,500 组参数全部通过：
顶点数 1–4、路线数 0–3、非根重数 0–2、费用 −1 或 2，根费用故意取 99。
每个非根顶点 `v` 的父节点从 `0,…,v−1` 枚举。
每棵子树比较完整递推表与矩阵枚举、压缩递推表与独立投影；
根处比较两种状态产生的费用集合与独立全局矩阵枚举。
这是有限回归，不是一般性证明或性能测量。

原始日志及临时联合校验文件只位于忽略的 `verification/runs/issue19-subtree-20261113/`。
既有依赖构建信息标为 replay；本包不把历史 PASS 改称新验证，也不声称全新环境复现。
验证使用现有 `jsp001022extension` 工作区的缓存环境；发布分支使用独立的
`uavroutingcertification` 包配置。已比对新增模块所需的 19 个既有 Lean 模块：
除换行及两个文件末尾空行外一致；Lean 版本和 mathlib 固定提交
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` 一致。
发布基线为研究分支的 `9b1093f9059d8c2e1674139b7402b6f0290d5283`。

## 下一步边界

本包没有实现可执行 DP 表、去重、回溯输出路线或操作计数。
下一步可用 `partialRep_merge_iff` / `compactRep_merge_iff` 证明表成员关系恰等于对应语义，
再分别统计局部次数枚举、孩子组合、集合比较、有理数运算与去重。
固定总费用、状态数界、对称性商等尚未在本包形式化。
带符号费用下不得直接按局部超预算删除状态。
这不完成 #19 的全部文献比较及接口研究，也不提供 #23 的标准机器时间证明。

后续可执行实现及其精化证明见
[可执行压缩状态 DP 状态说明](TREE_BUDGET_SUBTREE_DP_STATUS.md)。
