# A 包第一交付：稀疏模式结构定理（A0–A2）

研究基线：`3389ea74fa1d08a6bb0d4203fc3be7cfbad7f624`。
本地分支：`codex/sparse-package-a-20261118`。追踪：[研究计划 #24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24)。
本页记录新增实现及其独立验收，不改写此前文档批次和历史证明批次的验证状态。

子集和交换及奇偶中点沿用整数锥稀疏表示的经典方法，来源和适用边界见
[文献核验](TREE_BUDGET_LITERATURE_REVIEW_20261118.md)。这里新增的是本模型的精确形式化与原检查器连接。

2026-11-18 本地验收完成：A0–A2 四个新增模块编译通过，独立模块导入审计通过，有限枚举通过。
本批作为 A0–A2 的独立本地提交保存，供 A3 准确复现起点；未推送。此验收批次不包含 A3–A4。

## 数学契约

令 `Nonroot R = {v // v ≠ R.root}`，`n = card (Nonroot R)`，
`B = Nat.size m + ∑ v : Nonroot R, Nat.size (H v)`。
`exists_sparse_certificate` 的结论为：每个 `MatrixFeasible R H m s T` 实例存在原类型
`TreeBudgetCertificate.Certificate V` 的证书 `C`，同时满足：

- 原 `checkCertificate R H m s T C = true`；
- `C.row` 为单射，所有 `C.count i > 0`；
- `2 ^ C.size ≤ (m + 1) * ∏ v : Nonroot R, (H v + 1)`；
- `C.size ≤ B`；
- `C.size ≤ 2 ^ n`。

`sparse_checker_complete` 给出上述完整存在性结论与矩阵可行性的双向等价。
费用和预算是任意有理数；没有非负费用、正路线数、非零容量或根编号为零的假设。
输入根坐标可以任意，证书根坐标仍为零。

## 实现与证明边界

| 模块 | 新增内容 |
| --- | --- |
| [SparseNaturalCombination](../LeanCompletion/UAV/SparseNaturalCombination.lean) | 自然数良序最小化、同和子集重数交换、最小支持的子集和单射、盒子/位数界、两份模式替换和势能最小支持的键单射 |
| [TreeBudgetSparseGeometry](../LeanCompletion/UAV/TreeBudgetSparseGeometry.lean) | `parent_guard_iff`、祖先约束线性化、有理多面体、`RowValid`/`ValidPattern` 的整数点对应、中点合法性和精确有符号费用等式 |
| [TreeBudgetSparseCertificate](../LeanCompletion/UAV/TreeBudgetSparseCertificate.lean) | 增广模式计数与矩阵 iff、平方势严格下降、奇偶支持界、重新选择最小支持、原证书/检查器连接 |
| [TreeBudgetSparseExamples](../LeanCompletion/UAV/TreeBudgetSparseExamples.lean) | 非零根编号、负费用/负预算、重复子边、零父边、整数中点、错误路线数、非法零重数行、任意树的空证书 |

证明层的有限类型与经典选择用于存在性，不是实际枚举全部模式的求解算法。
路线数作为增广坐标保留，`matrix_iff_augmented_counts` 不要求调用者额外提供根总流等式。
子集和交换先证明逐点加法恒等式，再求和消去；它保留全部增广列并消去一个正重数。
奇偶论证最小化的是平方势。`exists_simultaneous_counts` 随后重新选择全局支持最小者，
用已经存在的奇偶见证约束它的支持，未把两个极小化对象混同。

没有更改原检查器的接受语义：合法重复行、合法零重数行仍可接受；零重数非法行仍拒绝。
正重数和不重复是新定理提供的见证性质。
本包不声称多项式求解、保持旧 tie-breaking 矩阵、短不可行证书或独立短最优性证书。
对子预算 `q` 的应用只需已知 `MatrixFeasible ... q`；预算最优性仍由既有优化器定理提供。

## 验证与复现

固定工具链为 `leanprover/lean4:v4.30.0-rc2`，mathlib 固定在
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
本地复用依赖缓存；17 个所需仓库依赖模块已对照研究基线源码，忽略文件末尾空白后相同。
本轮不是全新环境构建，也不把中止的依赖重建当作成功构建。
新模块使用 `lake env lean <source> -o <local olean>` 直接编译；日志保留在忽略的
`verification/runs/` 中。源码、工具链和依赖锁不因缓存复用而改动。

[审计源](../verification/AuditTreeBudgetSparse.lean)覆盖四个新增模块全部 54 项显式具名声明，
包括 41 个定理（其中 9 个边界回归）及 13 个定义/缩写。四个模块均实际编译通过；
`lake env lean verification/AuditTreeBudgetSparse.lean` 退出 0，输出完整覆盖 54 项声明。
全部声明的公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，
没有 `sorryAx`、新增公理或依赖编译器求值的证明。新增源文件也不含 `sorry`、`admit` 或 `native_decide`。
源码中的 5 项未使用 section 参数提示属于 linter 提示，不是证明错误。

[独立枚举脚本](../tools/check_sparse_patterns.py)以逐点访问次数费用为旧语义，以线性费用为新语义，
使用精确 `Fraction`；通过 3,220 个实例、44,020 个候选行、2,739 对中点、1,633 个可行实例
的支持界/子集和/势能检查，以及一个不等重数交换例。包含单点根、非零根编号、
零路线、零父边但正后代、子边次数大于父边、负费用和负预算；另有支持最小见证与平方势最小见证不同的明确例子。
枚举仅检查小例，不能替代一般 Lean 定理；其中展开小路线数只属于独立测试。

在具有相同依赖的正常 Lake 环境中可定向复现：

```text
lake build LeanCompletion.UAV.TreeBudgetSparseExamples
lake env lean verification/AuditTreeBudgetSparse.lean
python tools/check_sparse_patterns.py
```

不要以默认 `lake build` 覆盖这些研究模块为前提；默认根导入仍保留历史 Case1 范围。

## 第二交付：按 A3 → A4 推进

以下仍是实施计划，未标为已完成定理。

| 阶段 | 固定契约与依赖 | 退出条件 |
| --- | --- | --- |
| A3 输入入口 | `encodeNat m ++ encodeInput raw`；复用 `TreeBudgetBinaryInput.decodeRaw` 的树、索引和正分母检查；检查 `m = rootCount R H` | 解析往返；截断、非规范整数、错误行长、尾随位、错误路线数的拒绝；在任何依赖路线数量的分配前做根流检查 |
| A3 证书入口 | `E(k)` 后接每项 `E(count) ++ E(N) ++ E(row[0]) ++ ...`；复用 `parseList` 的剩余位长保护和整数行检查 | 检查接受 iff 解码成功且原检查器接受；每行都检查，包括零重数行；只遍历实际证书条目，不展开 `count` |
| A4 长度 | 把实际编码长度等式接到 `C.size ≤ B`；根坐标为零；输入位长 `L` 包含独立 `m` 与完整树数据 | 精确条目长度等式，证明 `N ≤ L`、`B ≤ L`，再证明候选界 `5L² + 4L + 1`；不能只写纸面估计 |
| A4 时间/语言 | 复用 `scaleFeesCost`、`scaleBudgetCost` 及其位宽界；固定实际访问和二进制算术执行 | 对所有输入/证书位串给出固定多项式成本 `Q(L+W)`，包含拒绝路径；连接明确标准计算模型或既有复杂度类框架 |

只有实际语言、编码长度和验证运行成本全部闭合，才将一般二进制树语言的 NP 成员性标为形式化完成。
旧 #22 搜索执行器的成本界不能直接转移给新证书验证器。#23 旧归约机器成本、B 包和 C 包保持独立范围。
