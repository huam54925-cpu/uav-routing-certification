# TM2 判断父指针追溯的终点

后续（2026-11-20）：[已解析父表上的完整树验证](TREE_BUDGET_TM2_WHOLE_TREE.md)
将这里的逐点终点检查接入实际顶点循环，并计入制备、复制和回收。
下文保留本批原始验收范围与历史运行记录。

输入是已装栈的查询位串 q、k 枚迭代标记和目标根的编码 r。程序先执行整段有界父指针追溯，再逐位比较 r 与返回游标的开头。根的规范编码自带终止位，所以可以在读完根编码时结束比较，游标后面的父表不参与比较。[具体机器和证明](../LeanCompletion/UAV/TreeBudgetWalkRootTM2.lean)

`root_run` 对任意 q、r、标记及上下文给出 **k·32(2|q|+1)²+|r|+3** 次实际转移的上界。追溯失败、目标比可读输入长、比较遇到不同位，都落在同一个界内。`root_refines` 对任意根位串刻画返回标志。在调用者准备的是规范根编码时，`endpoint_is_root` 将返回值精化为参考执行器的终点等式。

`validate_tests` 证明，对已解码的父数组 P，`validateCost P` 通过当且仅当从根走一步回到根，且从每个顶点走 n 步均到达根。这两种测试都使用同一台实际机器。定理中的顶点全称量词仍须由外层程序枚举，外层也须准备每次调用的栈。整机 NP 转接仍有待这些调用和行列检查的完整组合。

复现可运行 `lake build LeanCompletion.UAV.TreeBudgetWalkRootExamples` 与 `lake env lean verification/AuditTreeBudgetWalkRoot.lean`。回归直接执行转移，覆盖抵达根、在二环中未达根、根不固定和畸形查询。[四个机器用例](../LeanCompletion/UAV/TreeBudgetWalkRootExamples.lean) · [审计入口](../verification/AuditTreeBudgetWalkRoot.lean)

本批两个模块通过 Lean 编译，四个机器回归通过内核归约，27 项具名声明通过公理审计。本次另在固定依赖缓存上同时导入从计数预检到根终点检查的七批模块，核对全部 368 项不同声明，公理均在标准白名单内。
