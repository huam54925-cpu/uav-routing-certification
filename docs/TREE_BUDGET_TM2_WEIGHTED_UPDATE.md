# A4 二进制乘法与一次加权列更新

四个数据栈分别保存乘数 x、移位后的乘数 h、累加器 a 和复制中的 h。另有一个反向和栈和一个独立的上下文栈。所有栈的符号都是布尔位。操作数已按小端顺序装栈，任意长度和高位补零均可。[具体 TM2](../LeanCompletion/UAV/TreeBudgetWeightedTM2.lean)

机器每轮从 x 弹出一位。零位只需把 h 左移一位。一位为真时，逐位执行已有加法器的 `digit`、`carry` 和 `mix`，同时保存 h 的副本，随后还原 h 并移位，把反向和搬回累加器。结束时清空移位操作数。输入 x 和 h 均被消费，调用者的上下文原样保留。

设 N 为三个操作数的实际总位长。`update_halts` 给出从装栈配置到停机配置的至多 **16(N+1)²+1 次 TM2 转移**。输出栈 2 的数值等于 a+xh。`weighted_refines_executor` 将这个结果连接到 `addNatD` 和 `mulNatD`。取空累加器即得乘法的 `product_run` 和 `product_refines`。上界依据输入长度，且允许中间表示保留高位零。[执行和数值证明](../LeanCompletion/UAV/TreeBudgetWeightedRuns.lean)

`add_width` 证明一次加法的输出长度至多比两个操作数的最大位宽多一位。移位也只增加一位。这个共同的位宽界用于对所有乘数位求和，搬运副本、反转结果和最终清理均包含在转移界内。

复现入口为 `lake build LeanCompletion.UAV.TreeBudgetWeightedExamples` 和 `lake env lean verification/AuditTreeBudgetWeightedTM2.lean`。[机器回归](../LeanCompletion/UAV/TreeBudgetWeightedExamples.lean) · [公理审计](../verification/AuditTreeBudgetWeightedTM2.lean)

本批三个模块在固定依赖缓存上独立编译通过，五项机器回归覆盖补零、长进位、稀疏乘数与空操作数。46 项具名声明的公理审计仅含标准公理。
