# A4 第一批：任意位串解析与列累加成本

> **2026-11-22 更新：** 下文保留当时的验收范围。A0–A4 已闭合，
> 标准 TM2 验证器、无条件 NP 定理与终态验收见 [A4 总记录](TREE_BUDGET_TM2_VERIFIER.md)。

本地基线为 `be0b415`（A3 检查精化和实际证书长度），其父提交为
`87cb4e0`（A0–A2）。本批对应 [#24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24)
的解析与字段位宽阶段。本批按用户要求独立提交，并连同 A0–A3 的依赖提交发布到
`research/structural-service-cuts-20261023`；不修改远端议题。
发布复用 2026-11-19 的已验收源码和日志，提交前重新核对全部源码哈希，不把此核对记作新 Lean 构建。

**范围：本批证明解析器和列执行器的局部成本，另给出带显式机器假设的 NP 转接。
完整验证器的总位时间和无条件 NP 成员性仍未完成。** `Costed` 的计数是仓库现有二进制字参考模型；
不是 Lean 编译后程序的运行时间，也尚未证明等于标准机器的运行步数。

## 已消耗字段与中间位宽

[TreeBudgetSparsePrefixBounds](../LeanCompletion/UAV/TreeBudgetSparsePrefixBounds.lean)
用 `Occupies wire xs` 表达 `wire = before ++ flatMap encodeEntry xs ++ after`。
解析器的规范性给出这条分解，因此各字段占据连续且互不重叠的位串区间。
`after` 可以包含截断、非规范字段或任何非法后续数据，不要求整份证书解码成功。

令 `W = wire.length`。`occupied_field_bits` 证明所有已读重数和全部行坐标的
`Nat.size` 之和至多 `W / 2`；`occupied_entry_count` 证明已读条目数至多 `W`。
`certificate_prefix_occupies` 直接连接证书头和 `parseMany` 的成功前缀，
`occupies_take` 则允许取任意更短的条目前缀。

`weightedSum_size` 证明对任意非负整数对列表：

\[
 b\!\left(\sum_i c_i p_i\right)\le\sum_i(b(c_i)+b(p_i)).
\]

证明使用 `a+b+1 ≤ (a+1)(b+1)`、`a+1 ≤ 2^{b(a)}` 和位长刻画，
不依赖最终列和等于输入目标。`every_partial_accumulator_width` 因而给出
每一个前缀列累加器的精确上界 `W / 2`，包括空前缀。
缺失坐标在此位宽辅助函数中取零；公开证书解码器仍严格拒绝行长度错误。

## 执行器及无条件局部成本

[TreeBudgetSparseCostedParsing](../LeanCompletion/UAV/TreeBudgetSparseCostedParsing.lean)
复用真实扫描、长度计算、二进制比较和计数递减循环，新增条目解析及压缩列表解析。
`parseRawD_value` 对任意位串与 A3 的 `parseRaw` 相等，`parseSpecifiedD_value`
与带独立路线数的 `parseSpecifiedRaw` 相等。两个工作量界均没有解析成功假设：

\[
\begin{aligned}
\operatorname{work}(\mathrm{parseRawD}(y))&\le6144(W+1)^3+4,\\
\operatorname{work}(\mathrm{parseSpecifiedD}(x))&\le132096(L+1)^2.
\end{aligned}
\]

这里 `work = steps + allocations`。计数头只有在不超过已扫描的剩余位数时才进入循环；
巨大的二进制条目数、行长、非规范整数、尾随位和截断均包含在上述界中。
这两个入口只负责语法、旧输入形状与 EOF；父数组语义验证、正分母和根流预检还需接入完整执行器。

[TreeBudgetSparseWeightedCost](../LeanCompletion/UAV/TreeBudgetSparseWeightedCost.lean)
实现逐行顺序读取 `coordinateD`、列对抽取 `extractD`、二进制乘加 `accumulateD`
和完整单列执行 `columnD`。不存在按重数数值展开的循环，行读取也不按免费随机访问计费。
对 `Occupies y xs`、`1 ≤ B` 和 `Nat.size v ≤ B`，`occupied_column_work` 给出：

\[
\operatorname{work}(\mathrm{columnD}(xs,v))
\le164W(B+1)+320W(\lfloor W/2\rfloor+1)^2+3.
\]

`decoded_column_work` 同时证明结果等于原 `Certificate` 的加权列和，且满足上述成本界。
它仅要求证书可解码；不要求 `Valid`、目标列和、预算、正重数或不同的行。

更强的 `decoded_column_wire_work` 消去了索引位宽参数。非空证书至少含一行，
每行的 `n` 个坐标本身占据至少 `n` 位，因此 `n ≤ W`；空证书则不扫描行，单独处理。
于是对任意可解码的证书及其中任何顶点，单列读取、乘法和累加满足：

\[
\boxed{\operatorname{work}(\mathrm{columnD}(\mathrm{toRaw}(C),v))\le512(W+1)^3.}
\]

这个界只依赖证书自身位长，既不依赖目标重数/列和，也不需要输入合法性或证书语义合法性。
全部顶点的循环次数、其他验证阶段及标准机器开销仍不包含在这个单列界中。

## 标准模型连接的精确边界

[TreeBudgetSparseNPBridge](../LeanCompletion/UAV/TreeBudgetSparseNPBridge.lean)
采用固定依赖中的 `Turing.TM2ComputableInPolyTime`。输入对编码为 `word x ++ y`，
编码单射且长度为 `2L+1+W`，输出为一个布尔位。`StandardVerifier` 还要求每个内部栈的字母表有限，
配合 `FinTM2` 的有限栈数、控制状态与标签，排除把任意自然数或验证函数塞进免费机器状态的做法。

`InNP` 使用标准的多项式确定性验证器/多项式见证长度刻画。
`language_iff_polynomial_witness` 将 A3 的更紧界放宽为普通自然系数多项式 `L(L+1)`。
`language_inNP_of_standard_verifier` 以及 `language_inNP_of_equivalent_executor`
完成**条件式**转接：给定具体标准机器和其对所有输入对的多项式步数证明，即得到同一个位串语言的成员性。

目前没有构造这个 `StandardVerifier verify`，也没有消去该假设。
对这两个转接定理作公理审计不能消除显式参数；不能把它们报道为无条件的 NP 成员性定理。

## 验证与复现

2026-11-19，五个新增模块已按实际导入关系独立编译，均退出 0，最终编译无警告。
共 74 个具名定理，其中 22 个是回归，包括可解析但远超目标的重数和列值、
首条目完整而下一条目截断、超大条目数/行长头、非法零重数行、非规范字段和尾随位。
回归使用 `decide +kernel` 或已证明的一般定理；没有使用 `native_decide`。
[独立公理审计](../verification/AuditTreeBudgetSparseA4.lean)退出 0，完整覆盖 97 项显式具名声明，
仅使用 `propext`、`Classical.choice`、`Quot.sound` 的子集；没有 `sorryAx` 或其他非标准公理。
新增源码扫描无 `sorry`、`admit`、`native_decide` 或新增公理。审计明确包含带机器参数的条件式
NP 转接定理，不把参数误记成已构造的机器。

工具链仍为 Lean `4.30.0-rc2`，mathlib 提交仍为
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。复用先前本地缓存；新增导入的
`TreeBudgetCostedParsing` 及其 23 个闭包模块（含自身）均与原环境源码逐项比较后才复用构建缓存。
其余 A0–A3 依赖沿用已验收版本。本批不是全新环境全仓构建，也未执行远端 CI。

原始输出、失败后修复的中间检查、临时合并检查源及最终源码哈希仅保存在忽略目录
`verification/runs/package-a4/`；A0–A3 历史测试不计作本轮新测试。

正常 Lake 环境的定向入口：

```text
lake build LeanCompletion.UAV.TreeBudgetSparseA4Examples LeanCompletion.UAV.TreeBudgetSparseNPBridge
lake env lean verification/AuditTreeBudgetSparseA4.lean
```

## 剩余工作

以下是本批验收时的剩余项。后续[完整参考字工作量记录](TREE_BUDGET_SPARSE_TOTAL_WORK_STATUS.md)
已交付第 1 项在既有参考字模型内的组合，并构造首个 TM2 帧识别组件；第 2–3 项中的完整机器仍待完成。

1. 将解码后的父数组验证、正分母、根流预检、费用缩放、每行检查、重数总和及全部列检查组合，
   证明对任意 `x,y` 的执行值等于 `verify x y`，总成本至多一个固定的 `Q(L+W)`。
   行检查仍必须覆盖零重数行；有符号中间费用须由绝对值和控制，不能只约束最终抵消结果。
2. 在所选有限字母表 TM2 中实现/模拟这个执行器，给出表示保持、终止和实际转换步数的多项式界。
   既有地址成本放大函数不是这项机器模拟证明。
3. 用具体机器消去 `language_inNP_of_standard_verifier` 的假设，届时才完成一般 NP 成员性。
   本批不关闭 #24，也不改写 #23 的独立归约机器成本状态。
