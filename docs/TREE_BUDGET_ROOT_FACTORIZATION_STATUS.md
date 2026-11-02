# 根子树分解：Lean 实现与验证状态

日期：2026-11-02。对应研究任务 #16。

数学规格见 [TREE_BUDGET_ROOT_FACTORIZATION.md](TREE_BUDGET_ROOT_FACTORIZATION.md)。
该数学稿已发布于研究仓库提交 `961afd020b470865ba36621cf8e5ef132a5d0333`；
本文件记录其后的本地 Lean 实现，不将数学稿发布或历史构建视为本轮验证。

## 实现

新增 `LeanCompletion/UAV/TreeBudgetRootFactorization.lean`，沿用原顶点类型、
原根树、原基地、服务费和逐路线预算。服务费与预算均可为任意有理数。

| 接口 | 已实现的内容 |
| --- | --- |
| `rootBranch`, `InRootSubtree`, `subtree_partition` | 可计算的非根顶点归属与唯一分割；基地单独处理。 |
| `subtree_iff_parent_iterate` | 分支归属等价于有限次父函数迭代到对应根孩子。 |
| `subtree_parent`, `subtree_child`, `subtree_disjoint` | 非根父链封闭、孩子封闭与分支不交。 |
| `pattern_unique_root_child`, `positive_at_rootBranch`, `pattern_support` | 根和为 1 的唯一根孩子及正支撑沿父链传播。 |
| `pattern_zero_outside`, `pattern_branch_equiv` | 分支外坐标为零，模式与按分支分组的 sigma 类型等价。 |
| `LocalCountsFeasible`, `local_count_total` | 局部列和及自动固定的路线数 h(c)。 |
| `pattern_counts_iff_local_counts` | 全局模式计数可行，当且仅当所有根分支局部可行。 |
| `branchMultiplicity`, `branch_pattern_equiv`, `local_counts_iff_matrix` | 分支外置零的输入、保持坐标的模式等价、路线数为 h(c) 的局部矩阵。 |
| `matrix_iff_root_local`, `matrix_iff_branch_matrices` | 全局矩阵分解，显式保留 m=rootCount(R,h)。 |
| `budget_routes_iff_root_local` | 原需求的路线存在分解，保留 FlowCompatible 与根坐标规范化。 |
| `zero_branch_iff` | h(c)=0 时局部可行恰好等价于该分支全部重数为零。 |
| `root_only_matrix_iff`, `single_branch_matrix_iff` | 只有基地以及只有一个根孩子的退化情况。 |

局部到全局的证明通过模式等价重新索引计数并重排有限和；没有合并两条路线，
没有删去负费用访问，也没有加入错误的子边重数单调条件。
根分支函数是可计算定义；模式等价与存在性见证允许经典选择。
这些证明不等于已实现新的分支搜索器或证书合并执行器。

## 回归范围

新增 `LeanCompletion/UAV/TreeBudgetRootFactorizationExamples.lean`，包含 13 个命名定理：

- 零分支与负预算下的空路线族。
- 零根边下存在正深边的不可行性。
- 两个可行根分支、恰好达到预算以及局部合并恢复全局矩阵。
- 其他分支的负费用不能救助超预算路线。
- 同一分支内部的负费用抵消。
- 子边重数大于父边重数的可行模式。
- 全局路线数与根边列和不符的拒绝。
- 原需求到局部谓词的 BudgetRoutes 接口。
- 内部顶点两个孩子共享同一条路线预算的障碍。
- 单根分支没有规模缩减、只有基地时任意预算的空矩阵。

具体有限实例通过现有完整搜索的正确性定理或零分支定理验证；
计算型证明使用 `decide +kernel`，没有使用 `native_decide`。
只有基地和单根分支的退化性质还由一般定理覆盖。

## 验证

正式针对性构建命令（项目根目录）：

```powershell
lake build LeanCompletion.UAV.TreeBudgetRootFactorizationExamples
```

2026-11-02，上述命令成功完成，退出码为 0，Lake 报告 8344 个 jobs。
两个新模块均在本轮编译通过：主模块在首轮构建中完成，最终成功命令复用了其相同源码的缓存；
例子模块在修正一个向量坐标化简步骤后于最终命令中完成。13 个新回归定理全部通过。

13 项主模块与 13 项例子模块公理报告共 26 项，均只含 `propext`、
`Classical.choice`、`Quot.sound`，成功日志没有 `sorryAx`。
两个新源码文件均无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。
新增模块没有编译错误或 linter 警告；既有依赖的历史缓存仍会重放原有非致命警告。

该验证使用当前项目中固定的 Lean 4.30.0-rc2 工具链、锁定依赖及已有构建缓存，
属于本地针对性构建，不是全新环境、独立复核或远程发布包重建。
77 个既有 Lean 源码及受保护配置/目标文件与本轮保存的哈希快照完全一致；
未更改根导入、冻结目标、工具链或依赖锁定文件。
早期失败的开发运行不计为 PASS。上述验证发生在发布之前；上传本批次不构成额外验证。

原始开发日志、Lean 检查服务器通信和输入哈希快照仅保存在忽略目录
`verification/runs/root-factorization-20261102/`。

## 后续

本批次交付结构性充要定理及其接口与边界验证。
证书的可执行拆分与合并、剩余需求搜索、重复模式压缩和记忆化仍为后续任务。
没有实现一般内部子树的独立预算分解，也没有多项式复杂度承诺。
