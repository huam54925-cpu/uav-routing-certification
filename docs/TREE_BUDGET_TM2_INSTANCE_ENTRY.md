# 完整实例入口：费用、正分母、预算与 EOF

本批以 `38e13d4` 为基线，接续已有父表、H 和根流入口。对任意原始实例位串 x，同一台实际 TM2 在至多 `65536*(|x|+1)^4` 次转移内停机，返回位等于 `(TreeBudgetSparseVerifier.parseInstance x).isSome`。接受只完成实例阶段；证书记录、行列验证、精确标准终态及 NP 桥接仍是后续工作，#24 保持开放。

## 费用段契约

`A4FeeTailSpec.Fields` 保存费用分子列表 a、分母列表 d、预算分子 b 和分母 q。`read_iff` 将成功解析刻画为

\[
t=\mathrm{encodeInts}(a)++\mathrm{encodeNats}(d)++\mathrm{encodeInt}(b)++\mathrm{encodeNat}(q),
\quad |a|=|d|=n,\quad q>0,\quad \forall d_j\in d,\ d_j>0.
\]

`prefix_canonical` 逐字段还原原始位串；实例 EOF 消去最后尾串。根的费用分母也必须为正。允许负费用、负预算及未约分分数；规范零只采用非负符号，不接受负零或幅值的高位补零。

费用程序用已验证的维数字生成 E(n)，与两个列表的计数头逐位比较。从实际父表生成标记，每个标记许可读取一个字段；巨大声明计数不会成为循环次数。字段原始位先存入反向工作栈，完成一组后翻转到专用输出栈，保留两张表的正向表体及两个标量的完整规范编码。

实例末尾只检查实例游标。证书上下文使用独立栈，即使非空也不能被当成实例尾位。组合机有 57 个布尔栈、461 个标签和 6 个内部状态。

## 主定理与实际转移界

[TreeBudgetInstanceTotal.lean](../LeanCompletion/UAV/TreeBudgetInstanceTotal.lean) 中的 `A4FeeTailMachine.instance_polynomial x ctx` 同时给出实际 `EvalsToInTime`、停机标签 `out.l = none`、精确结果位及逐位保持的任意调用者上下文。`instance_from_init x` 将入口换成 `initList machine x`，无需预装任何已解析字段。成功时 `SavedInstance` / `InstanceFields` 可读回 m、n、r、父表、H、费用分子表体、费用分母表体、预算分子、预算分母，并给出空的实例游标。

[TreeBudgetInstanceSpec.lean](../LeanCompletion/UAV/TreeBudgetInstanceSpec.lean) 的 `accepted_eq_parseInstance` 把“根流接受且费用后缀接受”与仓库 `parseInstance` 的结果相连。[TreeBudgetFeeTailTotal.lean](../LeanCompletion/UAV/TreeBudgetFeeTailTotal.lean) 的 `fee_tail_run` 对任意费用后缀成立，结果位等于 `A4FeeTailSpec.read` 的 `isSome`；成功分支给出四个输出栈的完整顺序，接受与拒绝均保持此前字段和上下文。

令 S 为原始实例位长，费用入口所需的父表表体位长、维数字长、顶点数及剩余串长度均不超过 S。正式组合使用以下保守账本：

| 程序段 | 实际转移上界 |
| --- | --- |
| 已有根流入口 | `32768*(S+1)^4` |
| 每个费用列表组：复制、计数头、父表标记、字段读取及翻转 | `64*(S+1)^2` |
| 两个预算字段与实例 EOF | `16*(S+1)` |
| 整个费用入口 `fee_tail_run` | `256*(S+1)^2` |
| 根流、费用与调用/返回/停机边界合成 | `65536*(S+1)^4` |

字段成功运行的 `word_run_success`、`signed_run_success` 以已消费的原始位数为转移上界；`flush_run` 在反向栈长加一步内恢复正向输出。`loop_run_linear` 另给出了剩余串长 `U + 2*n + 3` 的标记循环界，但本批组合 API 仍使用上表的二次费用界。随包纸稿的 `4*P + 8*D + 2*n + 3*U + 64 ≤ 64*(S+1)` 是较紧的纸面估计，不能替代这里实际形式化的账本。

这些结论同时覆盖所有拒绝路径。结果位在配置的 `out.var.2` 中；供后续证书机读取的字段仍在栈上，本阶段尚未构造标准验证器要求的精确 `haltList` 终态。

## 本批本地验证

压缩包中既有运行输出仅作为历史材料保留在忽略目录。本次已重新运行 Python 源码，得到：

| 检查 | 本次结果 |
| --- | --- |
| 所有短费用串 | 12,285 次，17 接受、12,268 拒绝 |
| 费用段定向变化 | 22,564 次，3,661 接受、18,903 拒绝 |
| 小树矩阵与压缩证书独立枚举 | 237 例，143 可行、94 不可行 |
| 原始实例/证书语料 | 190 例，Python 参考解析通过 34 例，完整验证通过 18 例 |

费用段逐栈转写与独立数值解码在上述 34,849 次调用上一致，同时检查上下文及纸面步界。七项 Lean 内核 `rfl` 机器样例已编译通过；同一批 190 例也已由仓库的 Lean `parseInstance`、`verify` 和实际组合机器执行并逐项一致，检查了结果、上下文以及成功时四个正向费用输出和空实例游标。完整显式审计覆盖 17 个新增模块的 197 项命名声明，全部通过；其中包括两个任意输入主定理和七个机器样例。全部公理报告仅使用 `propext`、`Classical.choice`、`Quot.sound`，未出现 `sorryAx`；语料入口另复核原六个语义定理及七个样例的报告。上述有限测试与任意输入的运行定理分别验收。

机器样例保留随包六项，并新增原始实例多出一位的拒绝样例，与同一合法实例携带非空上下文的接受样例配对。这样分别检查实例 EOF 和调用者上下文。

## 复现及证据边界

本次完成逐模块构建后实际执行 `python verification/check_fee_tail.py --repo . --lean --skip-build`，退出码为 0；111 个项目依赖的完整递归检查、197 项声明审计及 190 例 Lean 对照均通过。

工具链固定为 `leanprover/lean4:v4.30.0-rc2`，mathlib 固定为 `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。本批 17 个新增模块逐模块定向编译，另重检 `Flow`、`ResourceCuts`、`TreeRouteDecomposition`、`TreeSupportExact` 四个基础依赖，其余复用本地缓存。对因工作树复制时间较晚而触发旧时间戳的 67 个依赖，逐一核对来源工作树的源码与 `.olean` 的 SHA256，并确认来源源码早于其构建产物后，仅恢复当前副本的来源修改时间；源码内容及来源目录均未改变。这些缓存来源核对不是 67 次重新构建。未作全仓冷构建或远端 CI；TeX 仅检查源码，未编译 PDF。

```powershell
python verification/check_fee_tail.py
python verification/check_fee_tail.py --repo . --lean
```

第二条通过 Lake 定向构建显式审计导入的全部模块，执行 `verification/AuditTreeBudgetInstanceEntry.lean`，再运行 `verification/RunTreeBudgetFeeTail.lean`。如已逐模块定向构建，可加 `--skip-build`；脚本递归核对全部 `LeanCompletion.*` 项目依赖的构建产物存在且不早于源文件；本批依赖闭包为 111 个模块。外部依赖继续采用上述固定缓存。语料在 `verification/runs/` 下临时生成，原始日志和生成结果均不入库。脚本的运行样例燃料只是回归预算，不是一般时间证明。

中文纸面证明源自用户提供的 `A4_local_verification.zip`，收录并更新于 [LaTeX 源码](TREE_BUDGET_INSTANCE_ENTRY_ZH.tex)。[固定 mathlib 终态定义](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Computability/TuringMachine/Computable.lean) 要求标准输出接口满足整个 `haltList` 配置；本阶段保留字段供证书机使用，最终清空其他栈、恢复初始内部状态并只保留单比特结果属于后续标准验证器交付。
