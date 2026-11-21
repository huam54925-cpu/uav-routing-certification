# A4：原始实例与压缩证书的组合 TM2 入口

本批接在证书记录解析提交 `44e024b63efffe6c181ddf6836a56d7b7591b4b6` 之后。
完整实例解析和任意条记录解析的程序及运行证明保持不变；新机器负责拆帧、调用、
维数字的实际复制和返回。以下结果仍是解析阶段，费用缩放和行列可行性检查属于下一批。

## 从标准初始配置出发

[`paired_from_init`](../LeanCompletion/UAV/TreeBudgetPairedParserTotal.lean) 对任意位串 x、y
证明：从 `initList machine (pairWire (x,y))` 出发，机器在
`65614*(|x|+|y|+1)^4` 次实际 TM2 转移内停机，结果位恰为

```lean
(parseInstance x).any fun I => (decodeCertificate I.data.n y).isSome
```

维数没有预装假设。实例成功配置中的规范数字经过逐位复制，成为证书解析器使用的维数。
[`parsed_fields`](../LeanCompletion/UAV/TreeBudgetPairedParserSpec.lean) 将该字段连接到实际
`parseInstance x = some I`，并证明 `I.data.n.bits.length ≤ x.length`。

[`wire_from_init`](../LeanCompletion/UAV/TreeBudgetPairedParserTotal.lean) 进一步覆盖任意原始
位串 s，包括外层缺少终止标记或载荷的情况。其结果位为
`(parseWord s).any (fun p => accepted p.1 p.2)`，转移至多 `65614*(|s|+1)^4`。
机器结果保存在配置的布尔位中；完整验证器的单比特输出整理和标准机器 NP 桥接仍待后续组合。

## 成功后的数据接口

[`Saved`](../LeanCompletion/UAV/TreeBudgetPairedParserTM2.lean) 同时保留两边的接口：

- 实例侧的 `SavedInstance`：路线数、维数、根、父表、H、有符号费用分子、正分母、
  预算分子和分母，以及为空的实例游标。
- 实例解析成功时，即使证书随后拒绝，全部实例字段仍保留，两个维数栈均等于 `I.data.n.bits`。
- 证书解析成功时，保存每条记录一枚标记及 `xs.flatMap encodeEntry` 的原序表体，证书游标为空。
  表体包含各自的重数、行长头和坐标，重复行及零重数行均保留。

实例和证书占据不相交的栈组。拆帧直接把 x 放入实例输入栈，把 y 留在证书输入栈；
实例调用期间证书栈不变，证书调用期间实例栈不变。只有规范维数字需要跨组复制。
实例失败分支直接停机，证书原串保持。完整布局和真实返回转移由
[`TreeBudgetPairedParserRuns`](../LeanCompletion/UAV/TreeBudgetPairedParserRuns.lean) 证明。

新机器有 78 个布尔栈、552 个标签、6 个有限状态。连线仅选择固定栈和标签，
不以高层 `parseInstance` 或 `decodeCertificate` 代替机器执行。

## 转移数分解

令 L=|x|、W=|y|、N=L+W，成功解析实例后令 D=|I.data.n.bits|≤L。

| 阶段 | 实际转移上界 |
| --- | --- |
| 拆开 `pairWire (x,y)` | `3*L+2` |
| 完整实例调用 | `65536*(L+1)^4` |
| 实例返回后的分支 | `1` |
| 保留源字的维数复制 | `2*D+2` |
| 任意条证书记录调用 | `Q(W,D)` |
| 证书返回后的停机 | `1` |

保留原证书界 `Q(W,D)=8*(W+1)^2+24*W*(W+1)^2+64*(W+1)*(W+D+1)`。
[`recordBound_cubic`](../LeanCompletion/UAV/TreeBudgetPairedParserSpec.lean) 证明
`Q(W,D) ≤ 72*(N+1)^3`，`combined_bound` 再合并上述各项。
拆帧、复制、分支及最后停机合计至多 `3*L+2*D+6 ≤ 6*(N+1)`；
因此常数为 `65536+72+6=65614`。实例失败分支不调用证书解析器，也不需要引入 D。
外层截断输入的拆帧清理与拒绝合计至多 `2*|s|+3`，同样包含于原始位串的四次界。

## 零重数的跨阶段回归

固定单点根、路线数 0、H=[0]、费用和预算均为 0、两个分母均为 1：

| 证书 | 组合解析器 | 现有公开 `verify` |
| --- | --- | --- |
| 空记录列表 | 接受 | 接受 |
| 一条 `(0,[0])` 记录 | 接受 | 拒绝 |

第二行的记录长度合法、总重数为 0，但该行从根出发的次数为 0，违反合法行必须出发一次的要求。
[`TreeBudgetPairedParserExamples`](../LeanCompletion/UAV/TreeBudgetPairedParserExamples.lean)
分别执行组合机器和公开验证器；两个语义断言使用 `decide +kernel`，实际机器断言使用 `rfl`。
这组检查不表示逐行检查已由新 TM2 实现。

## 2026-11-21 验收与复现

5 个新 Lean 模块已定向编译，含 30 项具名 theorem，其中 12 项为内核回归
（10 项实际机器、2 项公开验证器语义）。回归还覆盖两组字段完整读回、相同行不同重数、
路线数与维数不同、第二条记录截断、两侧 EOF、实例提前拒绝和外层截断。

统一验收的 2,984 组实际机器与参考规格对照，以及 69 项显式声明的完整公理审计全部通过，
最终退出码为 0，无失败项。公理集合仅含 `propext`、`Classical.choice`、`Quot.sound`，
无 `sorryAx` 或新增公理。

```powershell
lake build +LeanCompletion.UAV.TreeBudgetPairedParserTotal +LeanCompletion.UAV.TreeBudgetPairedParserExamples
python tools/check_tree_budget_paired_parser.py --repo . --no-build
```

本批实际使用固定依赖缓存，以 `lake env lean -o ...` 按 Spec、TM2、Runs、Total、Examples
顺序定向编译；Examples 可在 TM2 完成后独立编译。检查脚本通过独立编码器生成语料，
命名例子有预期答案，变异输入与 Lean 参考解析器对照，并检查实例字段、装载维数、
证书表体及游标。执行燃料为对应入口已证明的转移界加一，最后一单位用于观察停机。
审计覆盖携带运行证据的 def，源码入口为
[`AuditTreeBudgetPairedParser.lean`](../verification/AuditTreeBudgetPairedParser.lean)。

工具链仍为 Lean `v4.30.0-rc2`，mathlib 固定在
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`，Python 为 `3.13.4`。
未执行全仓冷构建或远端 CI。原始日志与生成语料仅存于忽略的 `verification/runs/`。
本批统计不包含此前证书解析的 127 项审计，也不包含根流单独重验的 171 项审计。

后续先实现费用缩放向量 A 和预算 A_T，并分别精化到 `scaleFees`、`scaleBudget`；
随后接逐行合法性、总重数、列和及完整验证器的机器输出。
