# 原始父表前缀、范围检查与整树 TM2 串接

本批从已经拆出的实例位串 `x` 开始，消去 `e2aea2c` 整树机器要求调用者预装父表、根编码和合法下标的假设。不是完整 A4 验收：其余实例字段、任意条证书记录、EOF、行列算术和最终 `StandardVerifier` 组合仍待完成。

## 输入与精化契约

真实前缀为

\[
E(m)\Vert E(n)\Vert E(r)\Vert\mathrm{encodeNats}(p)\Vert\mathrm{rest}.
\]

`encodeNats` 包含自己的计数头。机器先用规范自然数读取器读 `m,n`，再调用既有 `TreeBudgetEntryTM2` 读取 `r` 和计数父表。计数列表的巨大计数短后缀守卫仍实际执行。`rest` 是从 H 字段开始的原始后缀，本批不解码它。

`TreeBudgetParentPrefixSpec.lean` 定义 `Raw`、`parse` 和 `accepted`。`canonical` 证明任何成功解析的位串恰为相应 `encode a`，包含原来的精确后缀。接受谓词为

\[
\mathrm{parse}(x)=\mathrm{some}(a),\qquad
a.n=|a.p|,\qquad
\mathrm{decodeParents}(a.r,a.p)\ne\mathrm{none}.
\]

其中 `decodeParents` 包括根与父下标范围、根固定点和所有顶点到根的检查。因此“所有下标合法但有独立环”的父表仍然拒绝。

## 实际机器与费用

`TreeBudgetParentPrefixTM2.machine` 有 28 个布尔栈、258 个程序标签和 6 个有限内部状态。机器中没有以自然数值为循环次数的声明维数循环，也没有把解析或 `decodeParents` 当作转移中的计算原语。`Raw`、`Data` 和纯函数端点仅用于陈述和证明运行契约。

解析成功后，机器保留一份 `m,n,r` 数字、父表体、后缀和上下文，另在工作栈中：

1. 复制父表并重新封装根编码；逐位比较 `r<n`。
2. 扫描实际父表体，每读出一个父字段就逐位比较 `p_i<n`；二进制计数器只随实际父表项递增。
3. 比较实际项数与声明 `n`，清空计数工作栈。
4. 调用 `e2aea2c` 的整树 TM2，最后真实停机。

只有范围与维数检查全部通过，证明才构造 `ParentArray |p|` 并将工作布局识别为整树机器的入口。这一构造不要求无环；无环与根可达性由整树机器判定。

主定理 `prefix_polynomial` 对任意位串 `s` 和任意调用者上下文 `ctx`，给出实际终态 `out`，满足：

- 从 `start s ctx` 出发，实际 TM2 转移至多 `16384 * (s.length + 1)^4`；`out.l = none`。
- `out.var.2 = TreeBudgetParentPrefix.accepted s`。
- 上下文逐位保留；只要前缀解析成功，保存银行的全部栈均保留，涵盖接受、范围拒绝、维数拒绝与树检查拒绝。
- `saved_fields` 展开为 `m,n,r`、父表体、精确 `rest` 和 `ctx` 的物理栈等式。
- `init_eq` 将空上下文入口与普通 `initList machine s` 对齐，不需预装其他数据。

`inputPrefix_encoding` 和 `parse_inputPrefix` 直接连接仓库的 `TreeBudgetSparseVerifier.encodeSpecified`，不要求 `Shape` 假设。声明维数不符的真实编码仍然由机器检查。

令 `S=|s|`。解析器费用至多 `32(S+1)^2`。制备、父字段范围循环和维数检查分别使用线性、二次、线性界。`occupied` 证明根编码和父表体来自原串不相交的片段，故 `R+B≤S`；整树调用费用从 `4096(B+R+1)^4` 放宽为 `4096(S+1)^4`。子程序嵌入保持实际转移数，复制、比较、递增、清理、调用返回和最终停机均计入最终界。

上下文长度不出现在界中，因为程序只保留上下文，不遍历它。终态结果位仍在 `out.var.2`；本定理不是 `pairWire (x,y)` 上输出单元素栈 `[verify x y]` 的完整标准验证器定理。

## 源码与验证

新增模块按依赖顺序为：

```
TreeBudgetTM2CallRight
TreeBudgetNatRoutine
TreeBudgetCompareRoutine
TreeBudgetParentPrefixSpec
TreeBudgetParentPrefixParse
TreeBudgetParentPrefixTM2
TreeBudgetParentPrefixRuns
TreeBudgetParentPrefixRanges
TreeBudgetParentPrefixTotal
TreeBudgetParentPrefixExamples
```

`TreeBudgetParentPrefixExamples.lean` 的八项回归从原始位串执行组合机器，以内核 `rfl` 检查实际转移函数：维数不符、父下标恰等于 n、独立二环 `[0,0,3,2]`、合法非零根且 H 后缀保持、巨大计数配短后缀、截断头、非规范头和空父表。独立二环回归观察到整树工作计数器停在 2，表明机器通过前缀检查后实际调用并运行到了出错顶点。

本轮定向编译上述十个模块，并运行 `verification/AuditTreeBudgetParentPrefix.lean` 审计全部 153 项新增显式具名声明，其中 52 项为具名 theorem（包含八项机器回归；其余运行证明中的 def 同样参加审计）。公理仅允许 `propext`、`Classical.choice`、`Quot.sound`；不使用 `sorry`、`admit`、新公理或 `native_decide`。

复现采用固定的 `leanprover/lean4:v4.30.0-rc2` 与 mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。依赖已构建时，按上述次序执行：

```powershell
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/TreeBudgetParentPrefixTotal.olean LeanCompletion/UAV/TreeBudgetParentPrefixTotal.lean
lake env lean verification/AuditTreeBudgetParentPrefix.lean
```

第一条展示单模块命令形式；完整复现应为每个新增模块分别替换模块名并按依赖顺序执行。本次使用本地固定依赖缓存，没有全仓冷构建或远端 CI；运行输出留在忽略的 `verification/runs/` 下，不进入提交。`e2aea2c` 的六模块、四回归、109 声明验收是历史结果，未计入本轮新验收数。

`TREE_BUDGET_GENERAL_NP_MEMBERSHIP.tex` 的两处预算指示函数统一修为 `+\mathbf{1}_{f(v)\ne r}`。本地没有 LaTeX 环境，本批只检查和修改源码，不声称编译过 PDF。

## 下一步

后续 H 列表与根流入口已另行实现，见 [根流批验收](TREE_BUDGET_TM2_ROOT_FLOW.md)。本页以上仍记录 `6cc8b60` 批次的原始验收范围。

#24 保持开放。当前下一步是费用和预算字段、正分母与实例 EOF，随后把任意条证书记录的计数、EOF、行长与现有算术/行检查组件串接，最后完成 `StandardVerifier verify` 与语言 NP 成员性桥接。现有纸面 NP 证明和 Lean 参考工作量界继续单独标注。
