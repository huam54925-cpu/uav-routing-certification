# A4 连续读取自然数列表的 TM2

输入 s 是任意位串，ctx 是调用者的上下文栈。列表头是规范自然数，后接指定个数的规范自然数。机器在 **20(|s|+1)² 次实际 TM2 转移**内停机。读回值等于 `(parseNatsD s).value`，上下文逐位保留。`list_from_init` 对应空上下文的标准初态。[停机与精化定理](../LeanCompletion/UAV/TreeBudgetCountedNatsHalt.lean)

程序从预检的成功标签 9 直接进入元素循环。每轮弹出一枚标记，调用规范自然数解析器，再把带终止位的元素编码压入反向输出栈。标记耗尽时反转整个输出一次。零的编码仍有终止位，连续的零和重复元素有确定的边界。[循环程序](../LeanCompletion/UAV/TreeBudgetNatListLoop.lean)

`prefix_run` 给出每个已完成前缀的实际执行证据。设已经解析 j 个元素，最初的后缀就是这 j 个规范编码依次拼接，再接当前源栈；剩余标记数为 k−j。这个结论允许当前源栈截断或出现非规范字段。[前缀执行与分解](../LeanCompletion/UAV/TreeBudgetNatListPrefix.lean)

成功时栈 0 是未读后缀，栈 2 是按原序拼接的元素编码，栈 5 保存 ctx，其余栈为空。读回器对栈 2 的解码由 `fields_readback` 保证。失败时清空五个工作栈，并把有限状态的成功标志置为假。清理成本由返回配置的工作栈总长度控制，`result_space` 证明它不超过 2|s|。[读回证明](../LeanCompletion/UAV/TreeBudgetNatListReadback.lean) · [拒绝清理程序](../LeanCompletion/UAV/TreeBudgetListCleanup.lean)

`list_run` 到返回标签的界为 16(|s|+1)²，含读头、预检、元素循环和输出恢复。计入最后的清理和停机转移后使用上面的二十倍二次界。外层记录可继续消费栈 0。列表只有在外层协议要求时才需要检查 EOF。

复现入口为 `lake build LeanCompletion.UAV.TreeBudgetCountedNatsExamples LeanCompletion.UAV.TreeBudgetNatListPrefix` 和 `lake env lean verification/AuditTreeBudgetCountedNats.lean`。[机器回归](../LeanCompletion/UAV/TreeBudgetCountedNatsExamples.lean) · [公理审计](../verification/AuditTreeBudgetCountedNats.lean)

本批重新编译列表、拒绝清理及其依赖的预检模块，六个列表回归通过。列表审计的 70 项和重新运行的预检审计的 62 项声明均通过白名单核对。
