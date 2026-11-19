# 压缩证书记录的 TM2 入口

一条记录由规范自然数重数和一个计数自然数列表组成。`entry_run` 证明对任意位串 s 和调用者上下文 ctx，同一台有限字母表机器在 **24(|s|+1)²** 次实际转移内停机。`refines` 证明记录、未读后缀和失败结果与 `(parseEntryD s).value` 一致，栈 5 上的上下文逐位保留。重数为零时仍解析整行。[入口、停机与结果精化](../LeanCompletion/UAV/TreeBudgetEntryTM2.lean)

读头程序把重数的规范二进制数字存到调用者私有栈。随后嵌入同一台机器的列表程序只访问自己的工作栈。`call_run` 保留每次成功配置转移的实际步数，子程序停机指令把控制转交给显式的继续标签。调用者的最后一条停机转移另行计入。[程序嵌入与步数保持](../LeanCompletion/UAV/TreeBudgetTM2Call.lean)

`entry_suffix` 允许任意后缀。`consecutive_suffix` 将这一结论用于相邻记录，第一条的返回游标正好指向第二条的首位。另有一个实际两次调用的程序，把首条重数和行移入私有栈，再从当前输入栈执行第二次调用。四个有界执行回归覆盖不等长的行、空行后跟非空行、第二条截断及第一条计数超限。上述二十四倍二次界对应单条通用入口。[连续调用与回归](../LeanCompletion/UAV/TreeBudgetTwoEntryTM2.lean)

复现可运行 `lake build LeanCompletion.UAV.TreeBudgetTwoEntryTM2` 和 `lake env lean verification/AuditTreeBudgetEntryTM2.lean`。[公理审计入口](../verification/AuditTreeBudgetEntryTM2.lean)

本批三个模块均通过 Lean 编译，四个连续调用回归由内核归约验证，审计核对了 53 项具名声明。
