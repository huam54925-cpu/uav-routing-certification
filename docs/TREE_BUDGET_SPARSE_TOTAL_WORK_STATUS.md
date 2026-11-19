# A4：完整参考字工作量与首个 TM2 组件

基线为已发布的 `981a07c6ef238e9899010d75d1424eccec6cdd49`，包含 A0–A3 和
[A4 第一批](TREE_BUDGET_SPARSE_BITCOST_STATUS.md)。本批继续
[#24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24)。

**完整验证器的参考字工作量已闭合；完整验证器的 TM2 机器和无条件 NP 成员性尚未闭合。**
本批同时给出第一个具有真实 TM2 转移步数证明的组件，但该组件只识别帧前缀，不能替代完整验证器。

## 任意两条位串的总成本

令 `L = input.length`、`W = wire.length`、`N = L+W`。
[TreeBudgetSparseTotalWork](../LeanCompletion/UAV/TreeBudgetSparseTotalWork.lean)
中的 `verifyD_refines_and_polynomial` 对任意 `input, wire` 证明：

\[
\begin{aligned}
 (\mathrm{verifyD}(input,wire)).value &= \mathrm{verify}(input,wire),\\
 \operatorname{work}(\mathrm{verifyD}(input,wire)) &\le 4194304\,(L+W+1)^6.
\end{aligned}
\]

`work` 是既有 `Costed` 模型的 `steps + allocations`，常数和次数均不依赖实例。
主定理没有解析成功、输入有效、证书合法、目标相符或验证接受的假设。
内部阶段只在相应分支确实成功解析之后使用字段范围，失败分支也有无条件成本界。

执行入口依次覆盖指定路线数与原输入解析、父数组和正分母验证、根流预检、证书解析及行长检查、
费用缩放、全部行检查、总重数比较及全部加权列比较。没有按路线数或重数数值展开的循环。
零重数行仍进入行检查；超大重数、坐标和有符号费用同样计费。

| 阶段 | 已证明的参考字界 | 前提来源 |
| --- | --- | --- |
| 输入解析、输入验证、根流预检 | `262144 * (L+1)^3` | 任意输入位串，包括形状错误、坏树、零分母和路线数不匹配 |
| 证书解析、全部行长检查 | `16384 * (N+1)^3` | 顶点数不超过 N，由已解析输入获得；证书位串任意 |
| 解码后的完整证书检查 | `2097152 * (N+1)^6` | 输入和证书确实解码成功；不要求证书语义有效 |
| 完整入口与分支控制 | `4194304 * (N+1)^6` | 任意输入和证书位串 |

## 中间位宽与实现

[TreeBudgetSparseExecutionWidths](../LeanCompletion/UAV/TreeBudgetSparseExecutionWidths.lean)
从实际读入字段建立范围。对任意解码行，坐标位宽至多 W；重数位宽和条目数也由 W 控制。
一般求和使用 `size(sum xs) ≤ sum(map size xs)`。若费用位宽至多 F、行坐标位宽至多 B，
则行费用各项的**绝对值之和**的位宽至多 `n*(2F+B)`，而非只界定可能抵消后的最终费用。

输入费用缩放后的位宽至多 `2L+1`。取共同位宽 `6*(N+1)^2` 即覆盖根流、重数累加、
有符号行费用的所有中间和；单行工作量至多 `524288*(N+1)^5`，再乘至多 W 个条目得到六次界。

[TreeBudgetSparseCostedCheck](../LeanCompletion/UAV/TreeBudgetSparseCostedCheck.lean)
实现证书表物化、二进制索引枚举、逐行复制/检查、重数累加、逐列读取/乘加/比较。
[TreeBudgetSparseCheckBounds](../LeanCompletion/UAV/TreeBudgetSparseCheckBounds.lean)
把实际编码长度连接到这些执行循环；
[TreeBudgetSparseCostedFrontend](../LeanCompletion/UAV/TreeBudgetSparseCostedFrontend.lean)
把成功与拒绝分支接成完整 `verifyD`，并证明结果等于 A3 的公开入口。

这里沿用既有参考模型的列表、数组和有限函数视图，使用 `copyCells`、`copyVector`、
二进制 `rangeFrom`、动态算术和各阶段循环计费。Fin 索引是已生成自然数索引的证明细化视图。
这不是 Lean 编译器运行时的测速，也不是堆地址访问或标准 TM2 转移次数的精化定理。
将这些视图落实到有限字母表存储并证明模拟开销，是剩余机器阶段的工作。

## 已构造的标准机器组件

[TreeBudgetFramingTM2](../LeanCompletion/UAV/TreeBudgetFramingTM2.lean) 构造具体 `Turing.FinTM2`：
两个布尔栈、三个标签、`Option Bool × Bool` 六种内部状态，所有栈字母表均有限。
它读取标记位和载荷位；发现终止标记、空输入或截断后，清空剩余输入，在输出栈留下一个布尔位，
复位内部状态并停机。

`computer` 是一个实际的 `Turing.TM2ComputableInPolyTime` 对象。
对**每一条**输入位串 s，它在至多 `|s|+2` 次真实 TM2 转移内输出：

```text
(TreeBudgetBinaryCodec.parseWord s).isSome
```

证明包含单步配置等式、清空循环、帧扫描循环和 `TM2OutputsInTime`。
此组件识别是否存在完整的帧前缀；不验证自然数规范性、不返回解析载荷，也不检查 EOF。
它不是 `StandardVerifier verify`，没有消去 NP 转接定理的机器参数。

固定 mathlib 版本的 `Computability/TuringMachine/Computable.lean` 中，
`TM2ComputableInPolyTime.comp` 仍是 `proof_wanted`，本批不使用它。
后续必须提供经过验证的组合/编译或直接机器构造，不能把未完成的库接口当作闭合证明。

## 验收与发布

2026-11-19，七个新模块已按实际导入关系独立编译通过，最终编译无警告。
共 64 个具名定理，其中 14 个为[端到端回归](../LeanCompletion/UAV/TreeBudgetSparseTotalExamples.lean)。
机器执行证据还包含携带步数的 `EvalsToInTime` 定义，纳入全部具名声明审计。
[独立公理审计](../verification/AuditTreeBudgetSparseTotal.lean)退出 0，完整覆盖 96 项显式具名声明，
仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx` 或其他非标准公理。
源码扫描无 `sorry`、`admit`、`native_decide` 或新增公理。标准机器对象 `computer` 和其实际步数证据也在审计范围内。
本批以独立提交继续同步到原研究分支；不修改远端议题，不关闭 #24。

回归覆盖正常接受、重复行、合法和非法零重数行、巨大重数/列值、巨大指定路线数、
后续截断、错误行长、父数组循环、零分母、空输入、超大顶点数字段、巨大正负费用和空机队单点根。
回归使用 `decide +kernel` 或一般定理，不把 A0–A4 第一批的历史测试重新计为本批新运行。

Lean `4.30.0-rc2` 和 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 保持不变。
新增基线导入闭包的 70 个既有模块逐项比对源码后复用本地缓存，其余依赖来自已验收 A0–A4 第一批。
本次不是全新环境全仓重建，未运行远端 CI。日志、中间失败检查和最终源码哈希均仅保存在忽略目录
`verification/runs/package-a4-total/`。

```text
lake build LeanCompletion.UAV.TreeBudgetSparseTotalExamples LeanCompletion.UAV.TreeBudgetFramingTM2
lake env lean verification/AuditTreeBudgetSparseTotal.lean
```

## 仍未完成的目标

完整验证器仍需有限字母表的输入/证书存储、规范解析、树与根流检查、整数乘加、费用缩放、
行/列检查及控制组合的 TM2 实现与精化；需要对完整执行给出实际转移次数的固定多项式界。
之后才能构造 `StandardVerifier verify`，消去
`language_inNP_of_standard_verifier` 的机器假设。本批不关闭 #24，不声明一般 NP 成员性已形式化完成。
