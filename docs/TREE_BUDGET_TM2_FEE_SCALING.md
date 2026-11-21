# A4：两遍整数费用缩放 TM2

基线：`b083efc56ecf5b4f96f2e5b06134d1ed05806351`。日期：2026-11-21。

本批把已保存的有符号费用和预算缩放为整数，精确对应现有
`scaleFees`、`scaleBudget`。它是 #24 A4 的独立交付。
逐行合法性、总重数、非根列和、标准单比特输出及语言 NP 桥接继续开放。

## 实际入口与输出

[`from_paired_success`](../LeanCompletion/UAV/TreeBudgetFeeScalingTotal.lean)
从组合机器中配对解析器的实际返回配置 `after p` 开始，不需要调用者预装维数或费用。
令原始实例长度 L=|x|，缩放及其入口分支、返回停机共至多
`8192*(L+2)^3+2` 次实际 TM2 转移。该界不依赖证书长度、记录数或重数的数值。

`Scaled I out` 给出两个逐位等式：

- `out.stk (wr .fees) = (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList.flatMap encodeInt`；
- `out.stk (wr .budget) = encodeInt (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)`。

费用表体不另加计数头，按原顶点顺序保存。所有输出整数使用规范数字载荷和符号；
零的载荷为空，符号非负。工作寄存器和乘法寄存器清空，两个输出栈保留。

同一定理还证明 `∀ k, out.stk (old k)=p.stk k`，保留配对解析器的全部 78 个栈。
因此 m、n、r、父表、H、原费用与预算字段、证书记录标记、原序记录表体以及空游标均可继续读回。
相同行不同重数仍分别保留；零重数记录也保留，供下一阶段逐行检查。

[`scaled_from_init`](../LeanCompletion/UAV/TreeBudgetFeeScalingTotal.lean)
从 `initList machine (pairWire (x,y))` 出发，在
`131072*(|x|+|y|+2)^4` 次转移内停机。结果位仍为：

```lean
(parseInstance x).any fun I =>
  (decodeCertificate I.data.n y).isSome
```

成功时同时满足旧的 `A4PairedParser.Saved` 和新的 `Scaled`。
`scaled_wire_from_init` 覆盖任意原始外层串 s，包括截断帧，以
`131072*(|s|+2)^4` 计费。解析失败时直接拒绝。

这些结果是解析与预处理合同；尚未声称结果位等于完整公开验证器 `verify`，
也尚未将该位写成标准输出栈上的单个位。

## 两遍算法与费用规格

正向扫描每个顶点的费用分子、分母，维护 P，初始为 1。
每轮把分子幅值、分母、当前 P 分别压入三个逆序表，并保存符号，随后计算 P←P*b。
正向结束后，预算写为 a_T*P；逆向扫描从 U=b_T 开始，每轮计算

```text
factor = P_i * U
A_i    = a_i * factor
U      = b_i * U
```

规范编码的 A_i 前插到费用输出栈，最终恢复原顶点顺序。
预算用一次乘法；每个顶点正向一次、逆向三次，共 4n+1 次乘法。

[`formula_scaleFees`](../LeanCompletion/UAV/TreeBudgetFeeScalingSpec.lean)
通过已有 `cofactorCost_value` 连接按位置略去分母的乘积与整数除法规格。
`budget_scaleBudget` 连接预算规格。重复分母、未约分分数、有符号分子和零分子都受覆盖。

[`TreeBudgetRegisterTM2`](../LeanCompletion/UAV/TreeBudgetRegisterTM2.lean)
把有限条寄存器指令展开为物理栈操作、帧读取、既有二进制乘法以及新符号输出子程序；
实际程序不调用高层解析器或 `scaleFees` 来替代计算。
[`TreeBudgetRegisterRuns`](../LeanCompletion/UAV/TreeBudgetRegisterRuns.lean)
把每条指令的装载和返回计入运行费用。

## 物理字长与实际转移界

[`weighted_length`](../LeanCompletion/UAV/TreeBudgetWeightedWidth.lean) 对任意字证明

```text
|weighted u h a| ≤ |u| + max |h| |a|
|mulWord u h|    ≤ |u| + |h|
```

这控制栈上实际位数，允许高位补零。`history_fits` 对任意初始前缀字证明逆向扫描的宽度不变量，
每次乘法的输入总长受不重叠的原始字段载荷控制。
[`instance_bounds`](../LeanCompletion/UAV/TreeBudgetFeeScalingBounds.lean)
从 `parseInstance x=some I` 恢复原始编码，证明坐标数、载荷宽度和四组复制源长度均受 L 控制。

[`TreeBudgetSignedWordTM2`](../LeanCompletion/UAV/TreeBudgetSignedWordTM2.lean)
先反转幅值、去掉高位零，再写出规范带符号编码。
`write_run` 对任意带补零字给出 `2*|s|+2` 的实际费用；
调用指令另计一个转移。零不继承负号。

取 B=L+1，实际运行引理的组合如下：

| 部分 | 已证明的转移上界 |
| --- | --- |
| 四组字段复制及前缀初始化 | `8*L+13` |
| 正向扫描，包括最后的空表检测 | `512*n*(B+1)^2+1` |
| 预算输出及预算分母装入 U | `512*(B+1)^2` |
| 逆向扫描、清理与核心停机 | `1024*n*(B+1)^2+B+4` |
| 缩放核心总界 | `8192*(L+2)^3` |
| 配对返回分支与外层返回停机 | `2` |

`core_run` 合并上述实际运行，`total_bound` 再接既有配对解析四次界。
常数是保守上界，不是最小转移数或编译器运行时间估计。

## 回归与复现

[`TreeBudgetFeeScalingExamples`](../LeanCompletion/UAV/TreeBudgetFeeScalingExamples.lean)
包含 10 项实际机器的内核 `rfl` 回归。两项主要期望值为：

| 费用分子 | 分母 | 预算 | 精确读回 A | 精确读回 A_T |
| --- | --- | --- | --- | --- |
| (-2,0) | (4,3) | -3/6 | (-36,0) | -36 |
| (-2,0,3) | (2,3,2) | -2/4 | (-48,0,72) | -24 |

另含完整进位、正费用、规范零、完整实例与证书读回、相同行不同重数、零重数记录保留、
第二条截断、实例拒绝及外层截断。零重数行在本阶段仍通过解析与缩放；
已有公开验证器会拒绝单点根的 (0,[0]) 行，逐行机器检查属于下一批。

```powershell
lake build +LeanCompletion.UAV.TreeBudgetFeeScalingTotal +LeanCompletion.UAV.TreeBudgetFeeScalingExamples
python tools/check_tree_budget_fee_scaling.py --repo . --no-build
```

检查脚本以独立编码器生成 355 个输入。成功例的数值答案由 Python `Fraction` 和全部原分母的乘积给出，
再与实际 TM2 的逐位输出核对；同时检查全部实例字段、证书原序及重数、工作区清理。
它另从实际配对返回配置运行缩放，使用实例长度专属燃料，并逐栈核对全部保留区。
燃料为对应已证明界加一，最后一单位用于观察停机。

[显式公理审计](../verification/AuditTreeBudgetFeeScaling.lean) 覆盖本批 158 项声明，
包括携带运行证据的 `def`，不只审计以 `theorem` 命名的条目。

2026-11-21 本批 15 个新 Lean 模块已定向编译，包含 60 项具名 theorem，其中 10 项为上述内核机器回归。
355 例实际机器对照和 158 项声明公理审计全部通过，统一验收最终退出码为 0，无失败项。
公理集合仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或新增公理。
本次实际使用 `lake env lean -o ...` 按依赖顺序定向编译，随后执行上述 Python 检查命令的 `--no-build` 模式。

本批使用固定本地依赖缓存、Lean `v4.30.0-rc2`、mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` 和 Python `3.13.4`。
未执行全仓冷构建或远端 CI。原始日志和生成语料仅存于忽略的 `verification/runs/`。
本批统计独立于此前配对解析、证书解析和根流重验。

[用户提供的中文推导源码](TREE_BUDGET_FEE_SCALING_ZH.tex) 原样保留，未编译 PDF。
它固定在 b083efc，记录实现前的算法和乘法小计；完整程序的已证明界与验收以本文及 Lean 源码为准。

下一步顺序：**费用缩放（本批）→ 逐行合法性、总重数与非根列和 → 标准单比特输出及语言 NP 桥接**。
