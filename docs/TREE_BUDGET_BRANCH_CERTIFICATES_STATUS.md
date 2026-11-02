# 根分支证书操作与分支搜索：实现及验证状态

日期：2026-11-02。对应研究任务 #16 的第二部分。

本批接续研究仓库提交
[`e1cb4aa`](https://github.com/huam54925-cpu/uav-routing-certification/commit/e1cb4aaf8f2c16f2c6968f322e3d332ce7977983)
中的根子树分解，完成可执行证书拆分、合并，以及复用已有完整搜索器的根分支搜索。
根分解本身的历史验证范围见
[TREE_BUDGET_ROOT_FACTORIZATION_STATUS.md](TREE_BUDGET_ROOT_FACTORIZATION_STATUS.md)。
本文记录新增模块的本地验证，不将前次发布视为本次构建。

## 实现范围

新增三个模块，现有 `Certificate`、`Valid`、`checkCertificate` 和旧搜索器均未修改。

| 文件 | 内容 |
| --- | --- |
| [TreeBudgetBranchCertificate.lean](../LeanCompletion/UAV/TreeBudgetBranchCertificate.lean) | 列表接口、可计算的根孩子枚举、证书拆分和合并、检查器正确性、置换性质。 |
| [TreeBudgetBranchSearch.lean](../LeanCompletion/UAV/TreeBudgetBranchSearch.lean) | 逐分支调用旧搜索、收集并合并证书、可行性充要定理、原访问需求接口。 |
| [TreeBudgetBranchExamples.lean](../LeanCompletion/UAV/TreeBudgetBranchExamples.lean) | 21 个命名回归定理，含实际计算及定理接口检查。 |

可执行接口统一使用 `Fin n`，沿用原树、基地、费用和预算。
局部重数为已有的 `branchMultiplicity R h c`，即分支内保留 `h`、分支外取零；
局部路线数固定为 `h c.val`。根孩子仍按原费用计费。
输入的 `h R.root` 可任意取值，证书行的根坐标仍须为零。

## 证书接口与定理

`entries` 将证书转换为 `(row, count)` 列表，`ofEntries` 将列表转换为原证书结构。
`entries_ofEntries`、`valid_iff_entries`、`valid_ofEntries_iff` 将数据与合法性接口连接起来。
`rootChildren` 使用 `List.finRange` 和 `filterMap` 枚举根孩子；
`mem_rootChildren`、`nodup_rootChildren`、`sum_rootChildren` 分别保证完整性、无重复和求和一致性。

对每个根孩子 `c`，核心行接口为：

```lean
RowValid R (branchMultiplicity R h c) s T p ↔
  RowValid R h s T p ∧ p c.val = 1
```

这是 `rowValid_branch_iff` 的结论。证明由合法行构造已有模式，复用模式的唯一归属和分支外为零性质。
预算项原样保留，不要求服务费或预算非负。

`splitBranch R C c` 过滤 `entries C`，仅保留 `row c.val = 1` 的条目。
`splitBranch_sound` 证明：

```lean
Valid R h m s T C →
  Valid R (branchMultiplicity R h c) (h c.val) s T (splitBranch R C c)
```

该定理没有额外要求调用者提供 `m = rootCount R h`。
局部总重数直接由原证书的 `c` 列推出；`splitBranch_checked` 给出同一结论的布尔检查器接口。

`mergeBranches R cs` 按 `rootChildren R` 的顺序拼接各局部证书的条目。
`mergeBranches_sound` 在以下两个前提下得到合并后的全局 `Valid`：

```lean
m = rootCount R h
∀ c, Valid R (branchMultiplicity R h c) (h c.val) s T (cs c)
```

`mergeBranches_checked` 对应原 `checkCertificate` 的接受结果。
总重数由各分支相加；非根顶点的列和由根子树分割恢复。

这些操作不展开重数，不连接不同分支的路线，也不删除或压缩重复行、零重数行。
拆分保留条目在本分支中的相对顺序，合并保留每份局部证书的顺序。
`merge_split_entries_perm` 对任意有效证书证明拆分后合并与原条目列表满足 `List.Perm`；
回归实例同时检查实际条目顺序可以不同。

`zero_branch_valid_size` 证明：若 `h c.val = 0`，则该局部输入的任何有效证书都有 `C.size = 0`。
因此重数为零的占位行也不合法。函数本身可接受任意原始证书；正确性结论以输入合法为前提。

## 分支搜索与原需求接口

执行路径如下：

1. `searchByRoot` 检查 `m = rootCount R h`，不符立即返回 `none`。
2. `searchBranch` 调用原 `search R (branchMultiplicity R h c) (h c.val) s T`。
3. `collectBranches` 依次收集结果，任一分支失败即返回 `none`。
4. 所有根孩子成功后，`mergeBranches` 生成一份原格式的全局证书。

`collectBranches` 的空列表情况返回默认空证书族，并用 `Function.update` 填入已求解的分支。
`collectBranches_sound` 只对已处理列表中的分支声明合法性；默认值不承担其他分支的合法性。
最终调用使用完整的 `rootChildren` 枚举。
零路线分支仍调用原搜索器，因此根边为零但深处需求为正的输入会被拒绝。

| 定理 | 保证 |
| --- | --- |
| `searchByRoot_sound` | 返回 `some C` 时，原 `checkCertificate` 接受 `C`。 |
| `searchByRoot_correct` | `(searchByRoot R h m s T).isSome = true ↔ MatrixFeasible R h m s T`。 |
| `searchByRoot_none_iff` | 返回 `none` 当且仅当矩阵不可行。 |
| `searchByRoot_isSome_eq_search` | 对任意输入，新旧搜索的成功标志相同；不要求输出证书相同。 |
| `checkTreeBudgetByRoot_correct` | 新需求检查器返回 `true` 当且仅当 `BudgetRoutes R d m s T`。 |
| `solveByRoot_sound` | 输出证书时，整数相容性成立、原检查器接受证书，且预算路线存在。 |
| `solveByRoot_none_iff` | 原需求接口返回 `none` 当且仅当预算路线不存在。 |

`solveByRoot` 先运行已有 `compatible` 整数相容性检查，再将已有 `multiplicities` 交给分支搜索。
`checkTreeBudgetByRoot` 是其成功标志。

## 回归与验证

21 个命名回归定理覆盖：

- 两个分支分别需要 2、3 条路线的手写局部证书、直接合并以及原检查器接受结果。
- 零重数条目的保留、拆分顺序、拆分后合并的条目数量及置换、实际顺序变化。
- 零路线分支拒绝占位行；只有基地时，负预算仍返回可检查的空证书。
- 零根边下存在正深边、全局路线数不符时的拒绝。
- 其他分支的负费用不能救助超预算路线；同一分支内部的负费用抵消。
- 非零基地输入坐标、新搜索输出接受、新旧搜索成功标志一致。
- 原需求的负整数重数拒绝、相容但支撑不连通的拒绝、有符号费用可行实例。

计算型证明使用 `decide +kernel`；一般正确性定理由 Lean 检查。
先完成并构建合并函数和三项手写证书回归，再实现拆分、搜索及其他回归。
最终针对性构建命令在项目根目录执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetBranchExamples
```

2026-11-02，完整构建与修整一处行长提示后的最终构建均成功，退出码为 0，
Lake 报告 8346 个 jobs。三个新模块均在本轮编译通过；
最终命令重新编译例子模块，复用源码未再改变的证书与搜索模块缓存。
最终三个新模块没有错误或 linter 警告，既有依赖的缓存仍会重放历史非致命警告。

证书模块 10 项、搜索模块 9 项、例子模块 21 项公理报告，共 40 项，
仅含 `propext`、`Classical.choice`、`Quot.sound`，成功日志不含 `sorryAx`。
三个新源码均无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。
可执行数据定义不使用经典选择；证明中允许 Lean 标准经典推理。

本次使用固定的 Lean 4.30.0-rc2 工具链、锁定依赖和现有构建缓存，
属于本地针对性构建，不是全新环境重建或独立复核。
79 个既有 Lean 源码及受保护配置/目标文件与本轮保存的哈希快照一致；
没有修改根导入、冻结目标、工具链或依赖锁定文件。
原始日志、开发检查服务器输出和快照仅保存在忽略目录
`verification/runs/branch-certificates-20261102/`。

## 本版边界

本版将根分解接入可运行的证书输出接口，局部仍使用原完整穷举搜索。
剩余需求递归、重复模式压缩和记忆化尚未实现；没有性能改善量级的测量或承诺。
一般内部顶点的孩子子树仍可能共用一条路线的预算，不适用这里的独立根分支求解。
本文记录上传前已完成的本地验证；提交或上传不构成额外验证。
