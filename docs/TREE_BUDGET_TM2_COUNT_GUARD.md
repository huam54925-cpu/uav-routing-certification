# 计数列表的 TM2 入口

基线为研究分支的 `1b6600b`。设 s 是任意位串，ctx 是调用者保存的上下文。[预检程序](../LeanCompletion/UAV/TreeBudgetListGuardTM2.lean)先调用规范自然数解析子程序。若头部给出计数 k 和后缀 r，预检恰在 k ≤ |r| 时把控制交给成功返回标签。截断头、非规范头和过大计数均返回标签 10。

成功返回标签为 9。栈 0 原样保存 r，栈 4 保存 k 枚 `true` 标记，每个元素调用可弹出一枚。栈 1、2、3 均为空。栈 5 在成功和拒绝时均保留 ctx。过大计数的拒绝配置可以留有未用计数字和已移走的后缀前缀。

预检逐次借位递减二进制计数。每成功扣除一个单位，就从 r 移一位至保存栈。如果再也扣不出一个单位，机器按原序还原保存的输入，并为每一位压入一枚循环标记。如果扣除后没有输入位可移，机器立即进入拒绝标签。这样每次尝试的代价受头部位宽约束，尝试次数至多 |r|+1。[循环证明](../LeanCompletion/UAV/TreeBudgetListGuardRuns.lean)

`precheck_run` 从带 ctx 的配置出发，在至多 **8(|s|+1)² 次实际 TM2 转移**内到达返回配置。`precheck_from_init` 给出标准空上下文初态的相同结论。`precheck_refines` 证明读回结果与原始分支相等。`precheck_parseNatsD` 在成功返回值上接语义函数 `parseMany`，得到与 `parseNatsD` 的值相等的结果。该次转移界覆盖读头、借位、移动后缀及归还循环计数。逐项读取、输出列表和整体验证还需要各自的机器执行证明。[入口与精化](../LeanCompletion/UAV/TreeBudgetCountHeaderTM2.lean)

[边界验证](../LeanCompletion/UAV/TreeBudgetCountGuardExamples.lean)包含 k=0 且后缀非空、计数恰等于后缀长度、超出一项、截断和非规范头。对 k=2⁸⁰ 且后缀仅三位，`huge_short` 同时给出实际有界执行和拒绝标签。当前预检程序在返回之前没有元素解析调用。

复现时构建 `LeanCompletion.UAV.TreeBudgetCountGuardExamples`，然后运行 `lake env lean verification/AuditTreeBudgetCountGuard.lean`。[公理审计入口](../verification/AuditTreeBudgetCountGuard.lean)

四个新模块在固定依赖缓存上独立编译通过，最终无警告。审计覆盖 62 项具名声明，仅依赖标准公理。
