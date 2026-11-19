# A3：压缩证书二进制检查与实际长度界

本地起点为 A0–A2 独立提交 `87cb4e09376af7fd9e8f68b02612255a9b7506c3`，
父提交是研究分支基线 `3389ea74fa1d08a6bb0d4203fc3be7cfbad7f624`。
追踪：[计划 A / #24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24)。
起点提交只包含已验收源码、审计源、测试源和整理文档，没有日志、依赖或构建产品，未推送。

本轮目标为 A3 的检查精化，以及原 A4 中可与 A3 一起完成的证书长度部分。
2026-11-18 本地验收完成：四个新模块编译通过，78 个定理（含 25 个端到端回归），
106 项显式具名声明公理审计通过。本批作为 A3 与长度部分的独立本地提交保存，供 A4 复现起点；未推送。验证器位时间和标准复杂度类连接仍待 A4。

## 格式与执行

设 `E = TreeBudgetBinaryCodec.encodeNat`，`EN = encodeNats`。

```text
输入 = E(m) ++ encodeInput(raw)
条目 = E(count) ++ EN(row)
证书 = E(k) ++ flatMap encodeEntry entries
```

条目中的 `row` 按编号顺序包含全部 `n` 个顶点。根坐标保持原值，在原行语义下检查为零，
解码器不会擅自归零或丢弃条目。输入的根坐标 `H[root]` 仍可任意。

1. `parseSpecifiedRaw` 检查规范整数、完整旧输入和 EOF。
2. `decodeSpecified` 复用 `decodeRaw` 的维数、索引、树和正分母检查，
   随后检查 `m = rootCountCost(...).value`，才建立 `Instance`。
3. `decodeCertificate` 解析条目列表，检查 EOF 和每一行长度，构造原 `Certificate`。
   列表解析器保留“声明计数不得超过剩余位数”的预检。
4. `check` 只计算一次有符号费用缩放，复用 `rowCheck` 检查全部条目，
   再比较重数总和及加权列和。

可执行函数中没有按路线数 `m` 或重数 `count` 展开的循环，也没有模式全集枚举。
树的图和 rank 仅用于 `tree` 的证明解释；执行路径读取已有父数组。
所有行均检查：重复合法行按重数累计，合法零重数行保留，非法零重数行拒绝。

## 新增接口

| 模块 | 主要接口与保证 |
| --- | --- |
| [TreeBudgetSparseCodec](../LeanCompletion/UAV/TreeBudgetSparseCodec.lean) | `parseEntry_append`、`parseEntry_canonical`、`parseRaw_canonical`、`toRaw_ofRaw`、`ofRaw_toRaw`、`decodeCertificate_iff`；保留顺序/重数的往返、EOF、行长和超大计数拒绝；实际 `encodeCert_length` |
| [TreeBudgetSparseVerifier](../LeanCompletion/UAV/TreeBudgetSparseVerifier.lean) | 指定 `m` 的输入解析和根流预检；`check_eq_true_iff`、`verify_refines`、`verify_parsed_iff`，复用原有符号行检查及原证书语义 |
| [TreeBudgetSparseWireBounds](../LeanCompletion/UAV/TreeBudgetSparseWireBounds.lean) | 每条目和输入字段的长度比较、`certificate_length_bound`、`exists_short_witness`、`language_iff_short_witness`、`feasible_raw_has_short_witness` |
| [TreeBudgetSparseWireExamples](../LeanCompletion/UAV/TreeBudgetSparseWireExamples.lean) | 直接调用公开 `verify` 的规范/畸形输入、重复/零重数、负费用、未约分分数、单点根、空机队、`2^80` 重数回归 |

主精化定理 `verify_refines input certificate` 对**任意两条位串**成立：

```text
verify input certificate = true
↔ ∃ I C,
    parseInstance input = some I
    ∧ decodeCertificate I.data.n certificate = some C
    ∧ 原 checkCertificate(I, C) = true。
```

`verify_parsed_iff` 对已解析输入把中间解码条件加强为 `certificate = encodeCert C`。
因此结论同时涉及成功和失败分支，不仅检查由编码器生成的位串。
`feasible_routes_eq_root` 和 `feasible_raw_has_short_witness` 证明根流预检不会排除原矩阵模型的可行输入。

## 实际短位串界

令 `L = input.length`。对 A0–A2 提供的同一稀疏证书，每个重数不超过 `m`，
每个坐标不超过 `H`，且根坐标为零。精确编码公式和位长单调性给出：

```text
|E(count_i)| + |EN(row_i)| ≤ |E(m)| + |EN(H)| ≤ L。
```

正重数给出 `k ≤ m`，故证书头 `|E(k)| ≤ |E(m)| ≤ L`。
A1 的支持位数界以及输入两个字段自身的长度给出 `k ≤ L / 2`（自然数除法）。
对实际编码求和得到：

\[
|\operatorname{encodeCert}(C)| \le L\bigl(\lfloor L/2\rfloor+1\bigr).
\]

`exists_short_witness` 连接了原 A0–A2 一般定理、实际编码器与公开验证入口。
`language_iff_short_witness` 对所有输入位串证明：成功解析且矩阵可行，
当且仅当存在符合上述长度界并被 `verify` 接受的证书位串。
这是短见证的存在性；验证器没有要求每一份被接受的冗余证书都满足这个长度界。

## 验证记录与复现

工具链和依赖锁保持不变：Lean `4.30.0-rc2`，mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
复用本地依赖缓存；实际导入闭包中的 42 个既有仓库依赖模块与研究基线源码逐一比对，
忽略文件末尾空白后相同，另复用 A0–A2 的三个证明模块。A0–A2 源码与此前验收哈希一致，随后才作起点提交。
这里不把 A0–A2 的 3,220 个历史枚举实例重新记作本轮新测试。

四个新模块均使用实际导入关系独立编译，退出 0。
[完整审计入口](../verification/AuditTreeBudgetSparseWire.lean)独立运行退出 0，完整覆盖 106 项声明，
仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx` 或其他非标准公理。
新增源码没有 `sorry`、`admit`、`native_decide` 或新增公理；最终模块编译没有警告。

25 个新回归均由 `decide +kernel` 或已有一般定理证明，包括：重复合法行、合法零重数行、
非法零重数行、错误行长/根坐标/总重数/指定路线数/后代列和，输入和证书尾随位，
截断与非规范整数，父数组不连根、越界根、形状不一致、零费用分母、零预算分母，
未约分有符号费用，单点根及非单点树的空机队，`2^80` 重数的单条目成功验证，
超大条目数/行长声明拒绝，以及条目顺序往返。
原始日志与临时合并检查源只保存在忽略的 `verification/runs/package-a3/`。

正常 Lake 环境的定向复现入口为：

```text
lake build LeanCompletion.UAV.TreeBudgetSparseWireExamples
lake env lean verification/AuditTreeBudgetSparseWire.lean
```

本地验收采用逐新模块 `lake env lean <source> -o <local olean>`，再运行独立审计。
不是全新环境重建，也未运行远端 CI。

## 尚未闭合的 A4 范围

本轮没有把一个额外数值函数命名为运行成本来替代执行证明。
后续须为当前 `verify` 的输入解析、父数组验证、根流预检、证书解析、费用缩放、
逐行检查、加权列和与全部拒绝路径建立明确的位执行模型，并证明固定多项式 `Q(L+W)`。
还须连接标准计算模型或适用的复杂度类框架。此前 #22 搜索器的成本不能直接转移。
因此一般二进制树语言的 NP 成员性尚不标为形式化完成。

下一轮按执行路径固定以下义务：

1. 将解析器的剩余位长预检接到实际循环次数，覆盖非规范字、截断和超大声明计数的拒绝路径。
2. 将树验证、根流及分母缩放接到已有位算术执行，明确数组/列表访问和分配的收费范围。
3. 对任意证书位串，从其位长 `W` 推出条目数、坐标和重数位宽界。
   运行时间证明不能预先假设该证书通过检查，因而不能把 `count ≤ m` 当作畸形证书的前提。
4. 为加权乘法、累计列和、行检查和控制流程合成关于 `L+W` 的固定多项式上界，
   并证明费用擦除后确实等于当前 `verify` 的结果。
5. 完成标准模型/复杂度类连接，再与本轮的全部位串语言等价及短见证定理组合。
