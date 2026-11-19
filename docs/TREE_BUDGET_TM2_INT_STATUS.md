# A4：规范有符号整数的具体 TM2 解析器

本批接续 `20788a8`，在已有可调用帧/自然数解析器上增加符号位读取与负零拒绝。
[TreeBudgetIntTM2](../LeanCompletion/UAV/TreeBudgetIntTM2.lean) 是五个布尔栈、七个标签、
六种内部状态的具体有限字母表机器。

符号位先保存在独立的单格栈中，然后程序跳转调用已有规范自然数子程序。
返回时用 `peek` 检查符号和数值栈是否为空；负零拒绝，其余规范数值按符号解释。
机器没有把无界整数或字列表放入内部状态，也没有单位成本整数运算。

## 结果和转移数

对任意输入位串 s 和任意上下文栈 context：

```text
readResult (intOutcome s context) = (parseIntD s).value
integer_run s context : EvalsToInTime ... (2 * |s| + 2)
```

`integer_from_init` 从该 `FinTM2` 的实际 `initList` 出发，给出同一线性界；
`outcome_terminal` 证明到达的配置确实停机。
结果精化经过原始 `parseInt`，故正数、负数、零、截断、非规范幅值和负零的行为均与既有执行器一致。

停机时，栈 0 保留未读后缀，栈 1（临时栈）为空，栈 2 保存成功解析的规范幅值，
栈 3 保存已读符号，栈 4 保留上下文。成功/失败标志存在有限状态中；
`readResult` 只在成功时返回整数与后缀。非规范幅值在失败时被清空；负零拒绝时幅值本来为空。
上下文栈对任意长度均原样保留，无需扫描；其长度不参与当前子程序的转移界。

此接口保留后缀以便继续解析其他字段，不要求 EOF。
它构造的是一个具体标量解析组件，尚未完成计数列表、整个实例/证书解析或完整验证器组合。

## 验收范围

2026-11-19，两个模块独立编译通过且最终无警告；23 个具名定理，其中十项实际机器的内核求值回归。
[独立公理审计](../verification/AuditTreeBudgetIntTM2.lean)覆盖 42 项显式具名声明，退出 0，仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或非标准公理。源码扫描无占位证明或新增公理。
回归包括正负数的非对称位序、后缀及上下文保留、零、负零、空输入、单符号位、
缺少载荷、缺少终止标记以及正负两种非规范高位零；同时检查临时栈清空。

```text
lake build LeanCompletion.UAV.TreeBudgetIntExamples
lake env lean verification/AuditTreeBudgetIntTM2.lean
```

复用既有依赖缓存，工具链和 mathlib 固定版本未改动；不是全新环境全仓重建，未运行远端 CI。
原始日志和最终源码哈希仅存于忽略目录 `verification/runs/package-a4-tm2/`。

完整 `StandardVerifier verify` 仍需计数列表与记录存储、乘法等剩余算术、父数组/根流/费用缩放/行列检查，
以及全程序模拟与实际多项式转移界。NP 转接的完整机器假设仍保留；本批不关闭 #24。
