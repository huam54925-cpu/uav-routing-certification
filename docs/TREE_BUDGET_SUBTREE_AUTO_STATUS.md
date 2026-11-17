# 自动整数输入与完整证书精化（F0–F4）

> 当前导航（2026-11-17）：本页保留原批次的证明与验证记录。子树 A–E、[F0–F4](TREE_BUDGET_SUBTREE_AUTO_STATUS.md)、[G0–G4](TREE_BUDGET_SUBTREE_RESOURCES_STATUS.md)、[H0–H4 预检/预处理](TREE_BUDGET_SUBTREE_PREPROCESSING_STATUS.md) 与 [I0–I4 统一标量执行](TREE_BUDGET_SUBTREE_SCALAR_STATUS.md) 均已交付，I 包证明提交为 [66bcf08](https://github.com/huam54925-cpu/uav-routing-certification/commit/66bcf082189e3b368693af93a5008a213e7ddaba)。H/I 已建立共同位宽下的算术费用界；对象表示、真实地址、分配、共享和控制帧仍是独立后续层。当前任务见 [#19](https://github.com/huam54925-cpu/uav-routing-certification/issues/19)；此次导航同步没有重跑验证。

2026-11-15 本地验证。目标上游是
`huam54925-cpu/uav-routing-certification` 的
`research/structural-service-cuts-20261023` 分支，基线为
`dad8a845267e5eecdace00432ffdee2b4a9dca3f`。
本次在已有开发工程 `jsp_001022_extension` 中执行，复用现有依赖缓存；
IntegerDP、WitnessDP、Stats 的修改前源码已与该上游基线逐文件核对一致。
验证阶段未更新依赖。发布沿用本次已完成的本地验证；发布工作树与开发工程的
证明和回归源码一致，不将复制、提交或推送另记为一次构建。

## 已完成的接口

`LeanCompletion.UAV.TreeBudgetSubtreeAutoScaleSeed` 证明自动预处理与整数判定：

- `denLCM_pos`、`den_dvd_denLCM`、`denLCM_le_product`。
- `scaleNum_spec`、`prepare_pos`、`prepare_weight`、`prepare_root`、`prepare_budget`。
- `checkAuto_eq`、`check_scale_independent`。

根权重规范为零，故根分母为 1；其他坐标采用
`linearWeight R s v` 的分母 LCM。整数系数先做精确自然数除法，再乘有符号分子。
预算采用 `floorBudget D T`，允许负有理预算；正确性复用既有 `lift_budget`。
调用者无需提供缩放系数或缩放证明。

`LeanCompletion.UAV.TreeBudgetSubtreeIntegerWitnessSeed` 实现实际整数费用的见证 DP，
并证明以下完整列表等式链：

`dedupKey_natural → inside_lift_eq → node_lift_eq → compute_lift_eq → roots_lift_eq
→ solve_lift_eq → solveAuto_eq`。

```lean
theorem solveAuto_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    solveAuto R H s m T = TreeBudgetSubtreeWitness.solve R H s m T
```

此等式比较整个 `Option Certificate`，保持首次接受项、矩阵坐标、行顺序及重数。
去重保持右侧代表，且提升携带其矩阵与 picks；实际整数求解路径不调用有理提升函数。
已经继承 `solveAuto_sound`、`solveAuto_none_iff`、`solveAuto_size`、
`solveAuto_exact_iff`。路线语义桥仍显式要求 `HasDegrees`。
另有 `solve_scale_independent`，证明任意两种合法正缩放返回同一证书。
模块保留附件的 `Seed` 名称以维持导入兼容性；本次文件已编译通过。

F0 在 `Integer.inside`、`Integer.rootFold`、`Witness.inside`、`Witness.roots`
中将递归尾表显式绑定在回调外。四个 `*_cons_eq` 定理以 `rfl` 给出原有序递推式。
IntegerStats 的统计擦除和 WitnessDP 的键表投影证明重新构建通过。
没有据此声称已测得加速或完成机器成本证明。

## 本次验证与证据边界

工具链仍为 Lean `v4.30.0-rc2`，Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

| 检查 | 本次结果 |
| --- | --- |
| AutoScaleSeed 定向构建 | 通过，`checkAuto_eq` 已验证 |
| IntegerWitnessSeed 定向构建 | 通过，完整 `solveAuto_eq` 已验证 |
| 新增内核数值/边界例子 | 11 个通过（4 个预处理、7 个 AutoExamples） |
| AutoExamples 执行回归 | 603 组通过 |
| 受影响 BoundsExamples 执行回归 | 本次重新执行 483 组，加原有 21 组 DP 用例，通过 |
| AutoAudit 公理审计 | 63 个命名声明通过，仅标准公理子集，无 `sorryAx` |
| 独立 Python 模型 | 3,680 组表、11,040 组缩放表比较、66,240 次证书相等检查通过 |

63 个审计声明包括 52 个新模块中的命名声明、4 个 F0 递推式定理以及 7 个既有
擦除/键投影定理；匿名例子另行计数。新回归比较完整证书、根表及 picks、根孩子节点表
和矩阵载荷，并检查第二种合法缩放及旧证书检查器。覆盖零路线、仅根树、负预算、
带符号分数费用、不同分母、重复键和右侧矩阵代表。

Python 脚本来自附件，保存为 `tools/check_subtree_auto_cert.py`，使用标准库独立
枚举模型和矩阵可行性；它不是 Lean 的执行或内核证明。
这些数值来自本次执行，不是转记历史 PASS。未做全仓库冷构建、性能测量或 TeX 编译。
原始日志、附件解压内容和旧源码备份留在忽略目录 `verification/runs/subtree-auto/`。

## 复现

从包含 `lakefile.toml` 的工程根目录运行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSubtreeAutoScaleSeed
lake build LeanCompletion.UAV.TreeBudgetSubtreeAutoAudit LeanCompletion.UAV.TreeBudgetSubtreeBoundsExamples
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeAutoAudit.lean
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeAutoExamples.lean
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeBoundsExamples.lean
python -B tools/check_subtree_auto_cert.py
```

Lake 缓存的 `Replayed` 信息不能视为再次执行；需要重新执行用例时使用上述
`lake env lean` 命令。输出重定向到 `verification/runs/`，不纳入提交。

本包没有扩大 #21/#22/#23 的原有范围，不增加位成本或机器执行成本结论，
不展开逐顶点游走，也不声称预算变化后返回证书不变。
