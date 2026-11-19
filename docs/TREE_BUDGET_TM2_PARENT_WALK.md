# TM2 上重复追溯父指针

父表内部查询由下标的规范编码和完整表体拼接而成。运行入口的独立计数栈上已有 k 枚标记，上下文栈可含任意位串。每次跳转消耗一枚标记，嵌入父数组寻址子程序，取回父顶点，再逐位恢复父表，把刚读出的父顶点放到表前作为下一轮下标。如此可以多次调用同一段机器码。调用者负责准备首次查询和标记栈。[机器与表恢复](../LeanCompletion/UAV/TreeBudgetParentWalkTM2.lean)

设刚返回的规范数字有 d 位，其前面的表字段共占 f 位。`requery` 给出 **4d+2f+6** 次实际转移的上界，涵盖地址编码、复制以及恢复前缀顺序。对于任意已解码的父数组 P 和起点 v，`walk_run` 证明停机时完整表体仍在，表前是 `follow P k v` 的编码，原上下文保留。该证明允许父数组含环。`follow_refines` 将结果与 `followCost` 对应。[组合与结果精化](../LeanCompletion/UAV/TreeBudgetParentWalkRuns.lean)

对任意查询位串 q，令 W = |q|。`total_run` 给出 **k·32(2W+1)²+1** 次实际转移的上界。第一次或后续访问都可能遇到越界地址、截断、非规范字段。成功一步后，表体逐位相同，新下标编码的长度至多为表体长度。因此所有新查询的长度至多为 2W。空计数在检查下一次访问前即返回，和有界追溯的零步语义一致。[任意查询的停机证明](../LeanCompletion/UAV/TreeBudgetParentWalkTotal.lean)

回归覆盖连续两跳、二环、第二次访问下标越界、首下标截断以及零次访问。复现可运行 `lake build LeanCompletion.UAV.TreeBudgetParentWalkExamples` 与 `lake env lean verification/AuditTreeBudgetParentWalk.lean`。[回归](../LeanCompletion/UAV/TreeBudgetParentWalkExamples.lean) · [审计入口](../verification/AuditTreeBudgetParentWalk.lean)

后续的[根终点机器](TREE_BUDGET_TM2_WALK_ROOT.md)已实现根固定点检查与单顶点终点比较。全树验证仍需在机器上调度全部顶点。整机还需连接输入记录、费用缩放、完整行列检查及标准布尔输出。一般 NP 成员性的机器假设仍保留。

本批四个模块编译通过，五个机器回归通过内核归约，63 项声明的公理审计通过。
