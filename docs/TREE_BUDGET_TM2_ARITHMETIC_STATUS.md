# A4：二进制加法与比较的具体 TM2

本批接续 `cdde14b` 的拆帧/自然数解析组件，构造两个具体有限字母表机器。
它们从两个已装入指定栈的小端二进制字读取操作数；本批不把两操作数的装载/解析成本隐含进算术界。
所有栈符号都是 `Bool`，有限状态仅保存当前位和进位/比较标志；机器代码不对无界自然数做单位成本算术。

## 加法

[TreeBudgetAddWordsTM2](../LeanCompletion/UAV/TreeBudgetAddWordsTM2.lean) 的程序先逐位读取两个源栈，
由三个布尔位计算和位及进位，把和位压入临时栈，再逐位反转到输出栈。
输入耗尽后的最终进位也计入执行，源栈和临时栈均清空，返回后再执行停机指令。

对任意原始位字 a、b，包括不同长度、空字和高位补零：

```text
value (addWords a b false) = (addNatD (value a) (value b)).value
addition_halts a b : EvalsToInTime ... (2 * (|a| + |b|) + 4)
```

中间表示允许高位零，数值等价并不宣称每个输出字都是 `Nat.bits` 的规范编码。
例如两个补零零字相加仍可产生补零零字；若后续接口需要规范线编码，必须另行规范化或采用允许补零的内部存储接口。

## 比较

[TreeBudgetLeWordsTM2](../LeanCompletion/UAV/TreeBudgetLeWordsTM2.lean) 从低位开始读取，
遇到更高的不同位时更新比较标志。高位一致时保留低位比较结果。输入耗尽后输出一个布尔位并停机。

```text
leWords a b true = (leNatD (value a) (value b)).value
comparison_run a b : EvalsToInTime ... (|a| + |b| + 1)
```

此界对所有字成立，包含返回 `false` 的分支；不要求 a、b 满足任何目标上界或接受条件。
两个源栈和临时栈在终态为空。进位传播、左右长度不等、双方全零和补零表示均被一般证明覆盖。

## 验收与范围

2026-11-19，四个模块独立编译通过且最终无警告，共 48 个具名定理，其中 18 项实际机器内核求值回归。
[独立公理审计](../verification/AuditTreeBudgetArithmeticTM2.lean)覆盖 73 项显式具名声明，
包括实际执行步数证据与具体机器。审计退出 0，仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或非标准公理；源码扫描无占位证明或新增公理。
回归执行实际 `machine.step`，检查最终输出和源/临时栈清空；包括长进位、位序、补零、
不等长、相等、比较真假两分支及高位覆盖低位比较。

```text
lake build LeanCompletion.UAV.TreeBudgetAddWordsExamples LeanCompletion.UAV.TreeBudgetLeWordsExamples
lake env lean verification/AuditTreeBudgetArithmeticTM2.lean
```

复用既有依赖缓存，工具链和依赖固定版本不变；不是全新环境全仓重建，未运行远端 CI。
原始运行输出、最终哈希和失败迭代仅存于忽略目录 `verification/runs/package-a4-tm2/`。

这些是加法和比较的栈接口契约。乘法、减法、字存储与读取、计数列表解析和完整验证控制流仍需继续构造并组合；
本批没有构造 `StandardVerifier verify`，不消去 NP 定理的完整机器假设，也不关闭 #24。
