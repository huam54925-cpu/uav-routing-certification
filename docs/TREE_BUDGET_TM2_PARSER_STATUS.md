# A4：保留数据的 TM2 拆帧与首字段解析

基线为研究分支提交 `e43441d`。本批推进具体标准机器，不把参考工作量改称 TM2 时间。
完整验证器的机器实例和无条件 NP 成员性仍未完成。

## 同一台机器中的两次调用

[TreeBudgetFrameRoutineTM2](../LeanCompletion/UAV/TreeBudgetFrameRoutineTM2.lean)
给出可由调用者指定返回标签的 TM2 子程序。三个不同的布尔栈分别是源、临时、目标；其他栈不变。
扫描时把载荷压入临时栈，再逐位转移到目标栈，恢复原顺序。成功保留源栈中的后缀；失败清空临时栈。
规范模式只增加有限状态检查：空载荷表示零，非空载荷的最后一位必须为 `true`。

[TreeBudgetFrameRunsTM2](../LeanCompletion/UAV/TreeBudgetFrameRunsTM2.lean)
证明实际 `TM2.step` 的单步等式和 `StateTransition.EvalsToInTime` 执行证据。
任意完整帧、任意后缀和任意已积累载荷都有界；不假设解析出的数值小或实例可行。
[TreeBudgetCanonicalDigits](../LeanCompletion/UAV/TreeBudgetCanonicalDigits.lean)
证明有限状态规范性检查等价于既有 `(value xs).bits = xs`。

[TreeBudgetPairNatTM2](../LeanCompletion/UAV/TreeBudgetPairNatTM2.lean)
实例化四个布尔栈、十个标签和六种内部状态的具体 `FinTM2`。
第一次调用拆开 `pairWire (x,y) = word x ++ y`，返回标签直接进入第二次调用，解析 x 的首个规范自然数。
没有使用 mathlib 的未完成组合接口 `TM2ComputableInPolyTime.comp`。

| 入口与结果 | 实际 TM2 转移上界 |
| --- | --- |
| `split_run x y`：原样恢复 x，保留 y（允许空 y） | `3 * |x| + 2` |
| `split_truncated wire`：外层缺少终止标记或载荷，返回失败配置 | `2 * |wire| + 2` |
| `nat_success n rest y`：读取 `encodeNat n`，保留 rest 和 y | `3 * Nat.size n + 2` |
| `nat_run x y`：任意 x，含非规范、截断拒绝 | `2 * |x| + 2` |
| `pair_nat_run x y`：同一程序实际顺序调用 | `5 * |x| + 4` |
| `frontend_halts wire`：任意外层位串，最终停机 | `3 * |wire| + 5` |

成功返回时，栈 0 是证书 y，栈 1 是未读实例后缀，栈 2 为空，栈 3 是 n 的规范小端二进制位。
失败返回标签为 9；完整但非规范的整数保留其后缀，截断整数的实例栈为空；两者均保留证书栈并清空临时栈。
标签 8/9 的下一次转移分别设置成功/失败状态并停机。末尾这个转移计入 `frontend_halts`。

`nat_result` 给出读回值等于原 `parseNat`；`nat_refines_executor` 进一步等于既有 `parseNatD` 的 `.value`。
`certificate_preserved` 和 `scratch_cleared` 对所有解析结果成立。
这里是前端首字段组件，尚未读取完整实例、证书条目或做路由检查，也不是 `StandardVerifier verify`。

## 同一短证书的十二次参考工作量界

[TreeBudgetSparseWitnessWork](../LeanCompletion/UAV/TreeBudgetSparseWitnessWork.lean)
将 A3 的短见证和 A4 的无条件总工作量界组合为：

```text
x ∈ language ↔ ∃ y,
  |y| ≤ |x| * (|x| / 2 + 1) ∧ verify x y = true ∧
  work (verifyD x y) ≤ 4194304 * (|x| + 1)^12
```

同一个 y 同时满足三项条件。证明使用 `|x|+|y|+1 ≤ (|x|+1)^2`。
此处 `work` 仍为参考模型的步数加分配量；它与上表的真实 TM2 转移计数是不同结论。

## 验收范围

2026-11-19，本批六个新模块独立编译通过，最终编译无警告。48 个具名定理，其中 12 项为实际机器的内核求值回归；
[独立公理审计](../verification/AuditTreeBudgetPairNatTM2.lean)覆盖 92 项显式具名声明，
包括携带步数的执行证据定义。审计退出 0，仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或其他非标准公理；源码扫描无占位证明或新增公理。
回归检查空证书、非对称载荷的位序、两个后缀的保留、外层和内层各类截断、
非规范零、高位冗余零以及内部零位，并执行实际机器而非仅计算抽象解析器。

复现入口：

```text
lake build LeanCompletion.UAV.TreeBudgetPairNatExamples LeanCompletion.UAV.TreeBudgetSparseWitnessWork
lake env lean verification/AuditTreeBudgetPairNatTM2.lean
```

保持 Lean `4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 及冻结源码不变。
复用已验收依赖缓存；不是全新环境全仓重建，未运行远端 CI。原始日志和源码哈希仅存于忽略目录
`verification/runs/package-a4-tm2/`。此前批次的历史验收不计入本次。

剩余工作包括有符号整数与计数列表解析、算术及其存储约定、父数组/根流/费用缩放/行列检查，
以及完整机器的结果精化和多项式转移界。只有这些连接完成后，才能消去 NP 转接中的机器假设。
