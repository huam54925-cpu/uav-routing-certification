# 任意条压缩证书记录的 TM2 解析

本批以 `9021e607e665fed9cc1f07b31a103161e652a5af` 为基线，使用用户提供的
`A4_certificate_records_local.zip`。候选的机器程序、`recordBound` 和
`RecordsPolynomialSpec` 保持原文；新增一般运行证明。原候选在固定工具链上未闭合的
`packet_encode`、`packet_isSome` 两处证明已修正。

## 已证明的接口

[`records_polynomial`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsTotal.lean)
实际证明了 [`RecordsPolynomialSpec`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsTM2.lean)。
对任意维数 n、证书位串 y 和调用者上下文 ctx，从 `start n y ctx` 出发，存在停机配置 out：

- 实际 TM2 转移数至多 `recordBound y.length n.bits.length`。
- `out.var.2 = (decodeCertificate n y).isSome`，包括全部畸形和拒绝输入。
- `ctxStack` 和维数字 `n.bits` 逐位保持。
- 成功时 `savedCount` 保存每条记录一枚标记，`savedBody` 保存原序
  `xs.flatMap encodeEntry`，`cursor` 为空。

保留的表体包含每条记录的重数、行长头和坐标。相同行、不同重数、重复记录和零重数
均保持各自位置。零重数行仍须解析并检查行长。独立接口允许 n=0，此时每行必须为空。
行是否合法、预算是否满足以及重数和列和仍由后续验证阶段判断。

接口从已装入规范维数字的准备态开始。结果是配置中的布尔位；完整实例到本准备态的
装载、外层 `pairWire` 与完整验证器输出接口属于后续组合。本批保持不透明调用者上下文，
其长度不计入时间界，因为程序不扫描或复制上下文。

## 物理布局与循环

[`TreeBudgetEntryLayout`](../LeanCompletion/UAV/TreeBudgetEntryLayout.lean) 补全列表及
单条记录的整个返回配置。成功时，精确后缀、规范重数字和行表体就位，全部工作栈为空；
这比高层 `readEntry` 读回等式更强，可直接用于下一次调用。

[`Guard`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsGuard.lean) 的头字段、借位、
恢复和预检运行证明逐步运输标签 0–8 的真实转移，到达 9/10 即交给调用者。
因此证明适用于候选改写后的返回标签，未假设原列表循环在这些标签上的继续行为。

[`row_fields`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsRow.lean) 从任意起始编号
计数规范行字段，跳过载荷位，只在字段终止位上递增。行长字与维数字都规范，逐位比较
成功时两个工作字均为空。[`loop_polynomial`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsLoop.lean)
对剩余记录标记数归纳，保持外层表体、总记录标记、上下文和维数，并覆盖单条解析失败、
行长不符及最终 EOF 失败。返回布局与行长检查不依赖有限回归结果。

## 实际转移界

令 W=|y|，D=|n.bits|，证明采用候选给出的原始界：

\[
Q(W,D)=8(W+1)^2+24W(W+1)^2+64(W+1)(W+D+1).
\]

计数预检首先按实际位串确认 k≤W，随后才调用 k 次单条记录入口。单条入口包括失败分支，
每次至多 `24(W+1)^2` 步。循环的附加费用按实际消耗的互不重叠记录编码段收费：
[`round_run`](../LeanCompletion/UAV/TreeBudgetCertificateRecordsRound.lean) 的界为
`24(W+1)^2 + 32*|encodeEntry e|*(W+D+1)`。
归纳后的循环界是 `24*k*(W+1)^2 + 32*(|rest|+1)*(W+D+1)`。
最初的两次物理复制、进入循环和最终 EOF 也包含在 Q 内。

这是 TM2 `step` 的实际转移计数。机器使用 20 个布尔栈、78 个标签和 6 个有限状态。
输入中的重数不展开为路线；超大记录数在进入记录循环前由位长预检拒绝。

## 2026-11-21 验收与复现

11 个新实现/回归模块已定向编译，含 51 项具名 theorem（其中 10 项为内核 `rfl` 机器回归）。
回归专门覆盖第一条完整而第二条截断、相同行但不同重数的顺序读回、巨大重数、巨大记录数、
空证书尾位、错误行长、零维数、零重数和重复记录。

独立 Python 检查重建 45,959 次对照；其中选出的 501 例已与 Lean 实际机器和
`decodeCertificate` 对照通过，检查接受位、上下文、维数、成功表体、标记和游标。
驱动使用 `recordBound W D + 1` 作为执行燃料，最后一单位用于观察停机。
有限对照与一般运行定理是不同的证据。

本批全部 127 项显式具名声明由
[`AuditTreeBudgetCertificateRecords.lean`](../verification/AuditTreeBudgetCertificateRecords.lean)
审计，包括运行证明的 def。统一验收最终退出码为 0，无失败项；公理集合仅含
`propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或新增公理。

使用 Lean `v4.30.0-rc2` 与 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
的固定本地依赖缓存，Python 版本为 `3.13.4`。未执行全仓冷构建、远端 CI 或 LaTeX/PDF 编译。
原始候选、编译输出和对照日志保留在忽略的 `verification/runs/` 中。

已有依赖时，依次定向编译 `TreeBudgetEntryLayout`、`TreeBudgetCertificateRecordsSpec`、
`TM2`、`Data`、`Guard`、`Calls`、`Row`、`Round`、`Loop`、`Total`、`Examples`
（后十项均带 `TreeBudgetCertificateRecords` 前缀）。命令形式为：

```powershell
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/TreeBudgetCertificateRecordsTotal.olean LeanCompletion/UAV/TreeBudgetCertificateRecordsTotal.lean
python tools/check_tree_budget_certificate_records.py --repo . --lean --no-build
```

[`check_tree_budget_certificate_records.py`](../tools/check_tree_budget_certificate_records.py)
重建 Python 对照和 Lean 语料，并检查完整公理报告。省略 `--no-build` 会先请求 Lake
构建两个顶层模块；本批实际使用的是上面的固定缓存定向编译流程。

## 既有根流模块的单独重验

2026-11-21 另完成对 `38e13d4` 已发布根流批次的定向重验：10 个模块、12 项内核回归
和 171 项显式声明审计全部通过，最终退出码 0，无失败项，公理仅有 `propext`、
`Classical.choice`、`Quot.sound`。这是本日重新执行的检查；根流实现没有重写。
该批源码在 `75b6471` 和 `9021e60` 中相同，日志位于本地
`verification/runs/a4-root-flow-recheck-20261121/`。

下一阶段是费用缩放及逐行、重数和列和检查。完整标准验证器和语言 NP 机器桥接仍未闭合。
