# 父数组寻址与行的根坐标检查

列表解析器返回的元素栈是规范自然数编码的顺序拼接。这里的入口接收 `encodeNat i ++ table.flatMap encodeNat`，即带访问下标的表体。这是内部工作格式。外层验证器还需把已解析的表和下标放到相应栈中。

**读取父顶点。** 机器用列表子程序跳过 i 个字段，再在返回的源栈上执行规范自然数子程序。对于任意输入位串 s 和上下文栈 ctx，`lookup_run` 在 **24(|s|+1)²** 次实际转移内停机。`refines` 保证结果等于先执行 `parseNats` 再在其后缀上执行 `parseNat`，同时保留 ctx。缺失、截断和非规范的目标字段都会导致失败。父数组专用引理 `parent_at` 把取回的值识别为 `parent P v`，并指定目标字段之后的完整后缀。[寻址机器](../LeanCompletion/UAV/TreeBudgetParentLookupTM2.lean) · [父数组定理与机器回归](../LeanCompletion/UAV/TreeBudgetTableChecks.lean)

**检查行的根坐标。** 规范的零编码只有一位 `false`。成功跳过指定前缀后，专用机器用一条 peek 转移检查该位，保留当前源栈和已读字段。因此停机界为 **20(|s|+1)²+1**。`row_root_zero` 将结果与现有行检查器对 `p[P.root]` 的 `zeroNatD` 检查对应。重数不参与该判断。[机器、通用精化与停机界](../LeanCompletion/UAV/TreeBudgetIndexedZeroTM2.lean)

复现可运行 `lake build LeanCompletion.UAV.TreeBudgetTableChecks` 和 `lake env lean verification/AuditTreeBudgetTableChecks.lean`。四个有界机器回归分别覆盖内部零坐标、越表、非规范目标和截断目标。这批证明覆盖单次访问；父指针重复追溯、行的其余判断、费用缩放及整个验证器的组合还有待完成。

三个模块已编译，47 项具名声明已核对公理。`follow_one` 精化一步参考追溯，`row_reject_of_root` 证明根坐标检查失败时原行检查器返回假。
