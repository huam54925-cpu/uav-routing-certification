# A4：已解析父表上的完整树验证

本批继续 [#24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24)，
基线为研究分支 `a8c122932055e82466ada9f3df0c33dcb966df8a`。

本批的机器从已解析父表工作格式开始，实际执行根固定点检查和全部顶点的终点检查。
顶点枚举、查询构造、标记制备、重复调用、遇错退出及工作栈回收都在同一台有限字母表 TM2 内。
完整 A4 的原始输入、证书和算术检查组合仍是后续工作。

## 入口、输出与保持条件

设 `P : ParentArray n`，其中 n 包含根，父下标和根下标均已核对范围，
但不假设 P 是树。记 `B = (body P).length`、`R = (encodeNat P.root.val).length`。

`start P ctx` 的调用者栈保存父表体 `flatMap encodeNat (table P)`、规范根编码及任意上下文 ctx。
其余工作栈、编号栈、标记栈、待检队列和临时栈均为空。
这个入口没有预装逐顶点查询，也没有预装 n 枚标记。

程序先扫描父表的实际字段，每个完整字段生成一枚标记，并恢复父表的每一位。
复制该标记栈形成待检队列。根检查走一步；随后从二进制编号 0 开始，
每消费一枚队列标记，就从保存的表和根编码构造工作副本，复制 n 枚步数标记，
运行已有终点机器。成功后清空游标中的父表副本，逐位进位得到下一个编号；失败立即停机。
`Data` 和 `ready` 是证明中的栈布局视图，不是机器内部存储的无限类型状态。

机器有固定的 18 个布尔栈、147 个标签和六种内部状态。
根调用与顶点调用使用同一终点程序的两份标签重命名，共享工作栈。
所有栈字母表为 Bool，`finite_alphabet` 明确给出有限性。

输出在终止配置的 `var.2` 中。
`whole_tree_run` 对任意 P 和 ctx 同时证明：

- 确实经过有限次实际转移到达停机配置；
- 返回值等于 `(TreeBudgetCostedInput.validateCost P).value`；
- 父表原文、根编码和调用者上下文逐位保持，成功与拒绝均成立。

这里没有要求输出栈只剩单个位。最终 `StandardVerifier verify` 所需的
`pairWire (x,y)` 输入和 `[verify x y]` 输出规范仍须在完整调用者中实现。

## 循环与转移界

进入编号 i 的测试时，二进制编号栈为 `i.bits`，队列长为 left，且 `i+left=n`。
根测试和先前顶点已通过；保存的父表、根及上下文未变，工作区已回收。
`suffix_step` 刻画“当前顶点通过且剩余顶点全通过”，`loop_run` 将该条件落实到真实转移。
不需要在有限控制中存放自然数 i、n，也不需要预先知道输入是否含环。

令

\[
 H=32\bigl(2(B+2\operatorname{size}(n)+1)+1\bigr)^2.
\]

`setupBound` 和 `iterationBound` 分别为

\[
 A=H+5B+2n+5R+16,\qquad
 C=nH+3B+4\operatorname{size}(n)+2n+3R+20.
\]

`whole_tree_run` 的界为 `A+n*C+1`，包含初始标记计数和复制、根检查、
全部查询和标记副本、终点调用、控制分派、编号进位、回收及停机。
`vertices_le_body` 从每个父字段至少占一位得到 n≤B，
`totalBound_polynomial` 与 `whole_tree_polynomial` 将总界化为

\[
 4096(B+R+1)^4.
\]

ctx 从不被扫描，所以界不依赖 ctx 长度。
这个计费入口是既定多栈工作格式；从原始输入中解析、验证下标、分离父表和根字段的实际机器费用
不在本定理内。原始位串制备必须另有精化与多项式转移证明，不能仅凭此入口布局推定完成。

## 文件与复现

| 文件 | 作用 |
| --- | --- |
| [TreeBudgetStackRoutine](../LeanCompletion/UAV/TreeBudgetStackRoutine.lean) | 保存源的复制、成帧、二进制进位、字段计数与清空；每种操作都有实际转移证明 |
| [TreeBudgetWalkRootContract](../LeanCompletion/UAV/TreeBudgetWalkRootContract.lean) | 对任意调用上下文证明终点检查成功后的精确栈布局 |
| [TreeBudgetWholeTreeTM2](../LeanCompletion/UAV/TreeBudgetWholeTreeTM2.lean) | 固定控制程序和物理栈布局 |
| [TreeBudgetWholeTreeRuns](../LeanCompletion/UAV/TreeBudgetWholeTreeRuns.lean) | 查询制备、子程序调用、连续调用前的回收 |
| [TreeBudgetWholeTreeTotal](../LeanCompletion/UAV/TreeBudgetWholeTreeTotal.lean) | 全顶点循环、完整树验证、保持性及多项式总界 |
| [TreeBudgetWholeTreeExamples](../LeanCompletion/UAV/TreeBudgetWholeTreeExamples.lean) | 直接归约实际转移的四项回归 |
| [审计入口](../verification/AuditTreeBudgetWholeTree.lean) | 新增具名声明的公理审计 |
| [一般 NP 成员性证明](TREE_BUDGET_GENERAL_NP_MEMBERSHIP.tex) | 短证书、任意位串的标准位验证及纸面 NP 定理 |

```text
lake build LeanCompletion.UAV.TreeBudgetWholeTreeTotal LeanCompletion.UAV.TreeBudgetWholeTreeExamples
lake env lean verification/AuditTreeBudgetWholeTree.lean
```

四项机器回归覆盖单点根、非零编号根、根不固定，以及 `[0,0,3,2]` 中较晚暴露的独立二环。
最后一项检查编号 0、1 成功之后在编号 2 拒绝，并核对保存的表、根和上下文。

## 本批验证（2026-11-20）

六个新增模块按实际导入关系编译通过，最终编译没有警告。
本批有 30 项 `theorem` 声明，其中四项是直接执行机器的内核回归；
另外的实际转移证据以返回 `EvalsToInTime` 的 `def` 给出。
审计完整覆盖全部 109 项显式具名声明，退出 0，公理并集为
`propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或其他公理。
源码检查没有 `sorry`、`admit`、`native_decide` 或新增公理。

Lean `4.30.0-rc2` 与 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 保持不变。
本批复用本地固定依赖及基线模块缓存；研究基线与缓存来源工作树的既有 Lean 源码和配置
已核对无差异。六个新增模块各自的最终源码均已重新编译。
这不是全仓冷构建，未运行远端 CI，也不将之前各批的历史回归计作本次运行。
日志、开发中间结果和源文件检查脚本仅保存在忽略目录 `verification/runs/a4-whole-tree/`。

LaTeX 稿只交付源文件，检查了括号、环境配对、交叉引用和文档本地链接。
按本地没有 LaTeX 环境的约束，没有安装 TeX、编译 PDF 或进行版面渲染验收。

## 纸面证明与剩余 A4

LaTeX 稿对精确定义的二进制树语言给出纸面 NP 成员性。
同一份接受证书满足 `W ≤ L*(L/2+1)`；验证算法在任意位串上先限制计数头，
使用实际记录和坐标，直接计算加权列和。标准顺序存储及学校式算术给出保守的多项式位时间。
文稿覆盖负费用、负预算、空机队、单点根以及零重数记录必须检查的约定。

已证明的参考 `Costed` 六次界及同一短证书的十二次界，不是完整 TM2 的转移界。
本批整树机器也不是完整 `StandardVerifier verify`。
余下项目是原始输入制备、任意证书记录与 EOF、根流、费用缩放、全部行合法性、
总重数和跨记录列乘加的单程序组合；最后才可应用无机器参数遗漏的 NP 转接。
本批不关闭 #24。
