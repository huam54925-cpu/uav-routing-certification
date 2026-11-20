# H 列表与根流的原始输入 TM2 入口

本批沿 `6cc8b60` 的父表前缀入口继续读取 H，检查坐标数，并计算非根直接孩子的总重数。根流匹配只通过当前阶段；费用、正分母、预算、实例 EOF 和证书仍待后续机器处理。#24 与完整 A4 继续开放。

## 接受条件与保留数据

原始实例串的已处理部分为

\[
E(m)\Vert E(n)\Vert E(r)\Vert\mathrm{encodeNats}(p)
\Vert\mathrm{encodeNats}(H)\Vert t.
\]

`TreeBudgetRootFlowSpec.accepts_iff` 的条件是：父表长度等于声明的 n，`decodeParents r p` 成功，H 长度等于 n，并且

\[
\sum_{i<n,\ i\ne r,\ p_i=r} H_i=m.
\]

`reference` 将求和逐项连接到现有 `rootCountCost` 的数值。根坐标被明确排除；根上的 H 可以任意大。`parse` 与 `canonical` 对规范前缀和任意尾串往返，不要求尾串能解析为费用字段。

`TreeBudgetRootFlowTM2.root_flow_polynomial` 从任意原始位串 s 和任意上下文 ctx 出发，给出实际 TM2 运行、停机以及结果等式。`root_flow_from_init` 使用标准 `initList`，所有工作栈从空开始。结果读取 `out.var.2`；此接口尚未生成完整验证器所需的单比特输出栈。

`SavedPrefix` 保留调用者上下文，以及此前成功解析的 m、n、r、父表与原始 H 后缀。父表验证通过且 H 解析成功后，`SavedH` 在接受和根流/长度拒绝时都保留完整 H 表体及精确 t。`saved_fields` 汇总下一阶段可读回的字段。上下文长度不进入时间界，程序没有扫描或复制它。

## 真实程序与计费

静态 `Wiring` 调用编译器只重标记标签和栈地址；`call_run` 保持子程序实际转移次数。外层按顺序调用父表前缀、计数列表和根流扫描器，字段装载均通过物理复制完成。

扫描器保存父表和 H 原文，在工作副本上同步读一项。两个工作游标同时结束才进入最终比较；任意单侧提前结束立即拒绝。因此无需按 H 的巨大声明计数展开，也不会接受被截短的 zip。H 的计数头先由已有列表守卫处理。

当 `p_i=r` 且 `i≠r` 时才装载加法器。`accumulated_value` 证明数值关系，`accumulated_length` 与循环不变量给出计费所需的实际字长界，包括高位补零：

\[
|u_i|\le |H\text{ 的编码表体}|\le S.
\]

`scan_run` 对任意起始编号、剩余两表及累加字成立。循环不变量同时限制编号、父表剩余位长和“当前累加字长 + H 剩余表体位长”；因此选中和跳过分支都保持费用界。最终使用两次以 true 为初始标志的数值 ≤ 比较，每次分别准备被破坏性读取的副本，允许两个数值相同的字具有不同长度。

实际转移上界如下，S 是整个入口实例串位长：

| 部分 | 界 |
| --- | --- |
| 已有父表前缀和整树验证 | `16384 * (S+1)^4` |
| H 计数列表 | `20 * (S+1)^2` |
| 一轮同步扫描，含解析、分支、复制、加法和推进 | `128 * (S+1)` |
| 扫描核心，含表复制、双 EOF、两次数值比较 | `256 * (S+1)^2` |
| 原始入口全部组合，含装载、子调用返回和停机 | `32768 * (S+1)^4` |

这些界按 TM2 `step` 次数计算，不是参考工作量。局部线性界使本批新增扫描达到二次界；全入口沿用父表验证的四次阶。

## 回归与复现

`TreeBudgetRootFlowExamples` 直接约化组合机器的转移函数。覆盖非零根与巨大根坐标、误计孙节点导致的根流不匹配、255+1 的进位、单点根、空后缀、畸形费用后缀、H 少一项/多一项、巨大计数配短后缀、截断/非规范 H 字段、独立二环，以及补零累加器的数值相等。

2026-11-20 本批定向编译通过十个实现/回归模块；61 项具名 theorem 中，12 项是以内核 `rfl` 检查的实际机器回归。`verification/AuditTreeBudgetRootFlow.lean` 覆盖 171 项显式具名声明（包括运行证明的 def），审计逐项核对了声明集合，公理只出现 `propext`、`Classical.choice`、`Quot.sound`。未使用 `sorry`、`admit`、新公理或 `native_decide`。

使用 `leanprover/lean4:v4.30.0-rc2` 与 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 的本地固定依赖缓存。没有全仓冷构建或远端 CI；此前批次的 PASS 不计入本次结果。TeX 仅执行环境配对、括号和内部引用检查。原始运行输出仅留在忽略目录 `verification/runs/a4-root-flow/`。

依赖已构建时，按以下顺序编译：

```text
TreeBudgetTM2CallOn
TreeBudgetRootFlowSpec
TreeBudgetRootFlowScanTM2
TreeBudgetRootFlowScanRuns
TreeBudgetRootFlowScanLoop
TreeBudgetRootFlowScanTotal
TreeBudgetRootFlowTM2
TreeBudgetRootFlowRuns
TreeBudgetRootFlowTotal
TreeBudgetRootFlowExamples
```

每个模块采用下面第一条的命令形式，再执行审计源码：

```powershell
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/TreeBudgetRootFlowTotal.olean LeanCompletion/UAV/TreeBudgetRootFlowTotal.lean
lake env lean verification/AuditTreeBudgetRootFlow.lean
```

用户提供的中文纸面推导收录于 [LaTeX 源码](TREE_BUDGET_A4_ROOT_FLOW_PLAN_ZH.tex)，保留原计划及固定基线，另补本批的实际循环不变量与具体费用推导。未编译 PDF。

下一批优先处理费用分子、正分母、预算及实例 EOF，再进入任意条证书记录和行列算术。
