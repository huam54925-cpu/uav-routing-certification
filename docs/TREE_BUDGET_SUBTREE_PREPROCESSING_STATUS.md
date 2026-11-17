# 子树预检与自动预处理 H0–H4

日期：2026-11-17。语义基线为 G 包 `604efea285e1561479f76d95acd27ca338f242ce`，
工作区从导航提交 `a89e0b2d68226f76887f3fcb4ca1e10a5a6769f3` 建立。
**H0–H4 已实现并通过下述本地验证。** 本包针对 #19；#22 的验收边界和开放状态不变。

## 输入与执行顺序

`TreeBudgetSubtreePre.Input N` 存储根编号、`Vector (Fin N) N` 父数组、
`Vector Nat N` 的 H、`Vector Rat N` 的规范服务分数、自然数路线数及规范预算分数。
`Represents I R` 指定根和每个父坐标与既有 `RootedTree` 相同。
预检及预处理只读取这些物化数组，不调用任意用户提供的父关系、H 或费用函数。
`materialize` 是语义适配器；其外部函数求值不属于已物化输入模型的收费范围。

`execute R I` 的次序固定为：扫描全部 N 个编号计算根部质量 → 读取并比较 m →
只有通过时运行 `prepareC` → 调用 G 包 `solveR`。拒绝分支不访问服务或预算，
不运行 prepare，不构造 m 维向量，返回 `none` 和全零 DP/载荷统计。
失败仍有预检费用；单根且 `m=2^200` 的入口计 13 个模型指令，宽度为 201。

证明接口：

| 层次 | 已给出的接口 |
| --- | --- |
| H0 | `Represents`、`materialize_represents`、`execute_reject` |
| H1 | `rootMassC_value`、`denLCMC_value`、`scaleNumC_erase`、`floorBudgetC_erase`、`prepareC_value`、`execute_certificate_eq` |
| H1 独立计数规格 | `euclid_ops_exact`、`rootScan_ops_exact`、`denLCMC_ops_exact`、`prepareC_ops_exact` |
| H2 | `euclid_step_ranges`、`two_remainders_lt`、`euclid_iterations_le`、`denLCMC_sublist_dvd`、`rootScan_partial_le`；`PreRanges` 中的全部临时量契约 |
| H3 | 各算术原语的值/范围/收费界、`execute_preBitWork_le`、无额外宽度假设的 `execute_preBitWork_canonical` |
| H4 | `execute_resource_eq`、`execute_pass_keyStats`、`execute_pass_payload`、`execute_pre_and_DP_bounds` |

`prepareC_value` 是整个结构的相等：scale、全部 weight 坐标、budget 同时保持。
`execute_certificate_eq` 保持整个 `Option Certificate`，包括零行成功证书与 `none`
的区别。通过分支的整个 G 包 `ResourceResult` 相等，因此 17 个 DP 字段及 9 个载荷字段
均保持；没有重新运行 key-only checker 来取得新计数。

## 算术与收费契约

本包选择**带统一填充宽度的数学收费语义**。`Run.value` 为参考执行的结果，
`Run.ops` 为模型指令数，`Run.width` 为该运行的保守标量位宽。
一条比较、加减、乘、带余除、物化标量读写或列表控制指令，按该运行宽度 W 收费
`32*(W+1)^2`。因此 `bitWork r = 32*(r.width+1)^2*r.ops`。
这一定义有意对较短的操作数多收费；不是 Lean 内建操作或标准机器的运行时间假设。

读数组的索引位宽也计入：`index_size` 保证合法编号不超过 N 位。
控制和读写的固定收费使用以下块契约；源码中的递推与独立计数规格逐项对应：

| 参考块 | 模型指令数 |
| --- | --- |
| Euclid 非终止迭代 | 零比较、divmod、两次标量移动，共 4；终止比较 1 |
| 规范化 | 一次实际 Euclid，加两个精确除法和两个分量写入，共额外 4 |
| 有理加法 | 两个交叉乘积、分子加法、分母乘积及临时读写，规范化之外额外 8 |
| 系数 | 根坐标 3；非根分支加 10，含父数组/服务读取、索引、比较及控制 |
| LCM | 一次 Euclid，加乘法、除法、读取共 3；列表递推另加 3 |
| scaleNum | 4，含分母读取、自然数商、带符号乘积及结果写入 |
| floorBudget | 8，含预算读取、分子乘积、divmod、符号/余数判定、负 floor 修正和输出 |
| collect / collectV | 每个已求出的元素 2，终止 1；每个系数只求值一次 |
| rootScan | 每个非根根子顶点 12，其他顶点 8；终止 1 |
| 入口 | rootScan 后读取/比较/控制 3；通过附加 2，拒绝附加 1 |

对象分配、引用、共享指针、实际栈和 GC 不包含在标量读写契约内。
`ops/width` 是证明观察量：计算统计字段、最大位宽和 `bitWork` 的物理执行成本
不在模型内。没有把这些 ghost 观察量的维护默认为免费机器指令。
若需要实际执行计数器的位时间，必须再实现和计入计数器表示及更新。

有理加法采用未约分交叉乘积后规范化的明确参考实现。
`normalizeC` 复用同一次 `euclid` 返回的 gcd 构造 `Rat`；证明字段在运行时擦除。
LCM 采用 `a*b/gcd`，先乘后除的临时乘积已纳入。
`floorBudgetC` 直接计算 `(D*T.num)/T.den`，并证明等于原 `floor(D*T)`；
该参考实现不构造原 Lean 有理乘法的中间规范分数。
数值精化与收费证明对应本包参考实现，不能将其收费转给 Lean 内建 Rat/gcd/div。

系数确实求值两遍：第一次形成分母列表，第二次形成整数权重向量。
`prepareC_ops_exact` 给出的独立递推为

```text
prepareOps = 2*sum_v coefficientOps(v) + denOps(coefficientList) + 8*N + 16
euclidOps(a,b) = 4*euclidIterations(a,b) + 1
euclidIterations(a,b) <= 2*size(a)
```

没有采用从原始服务分母先求 D 的可选优化，也不假定编译器共享两次系数求值。

## 中间值与显式多项式

参数约定：`size 0 = 0`；b 至少为 1，是规范服务及预算的分子绝对值/正分母最大位宽；
h 是全部 H 坐标的最大位宽；mu 是 m 的位宽；N 是顶点数。
根服务虽不参与系数，也包含在 b 的总输入约定中。
`serviceBits`、`massBits` 给出规范最大值，`inputFits_canonical` 自动建立全部宽度前提。
这些最大值只用于分析，入口不会在预检前扫描服务去计算它们。

```text
W = (N+2)*(2*b+h+mu+4)
preOps <= 128*(N+1)*(b+1)
preWidth <= W
preBitWork <= Q(N,b,h,mu)
Q = 4096*(N+1)*(b+1)*(W+1)^2
```

Q 是总次数六的明确多项式。准备阶段另满足
`prepareOps <= (48*b+85)*N+17` 和
`prepareWidth <= N+(N+1)*(2*b+2)+b+2`。
拒绝分支有更专门的界，独立于服务、预算及 m 的数值：

```text
G = N + N*(h+1) + mu + 1
rejectPreBitWork <= 32*(G+1)^2*(12*N+5)
```

H2 的范围包括：有理加法的两个交叉乘积、未约分分子和及分母乘积；
规范化两次精确除法；LCM 乘积和商；scaleNum 商及带符号乘积；预算分子乘积、
商、余数与负 floor 的 `q+1` 修正。
Euclid 每步余数小于除数，商/余数不超过被除数，全部递归操作数宽度不增，
两步余数至少减少一位。任意 LCM 子列表结果均整除最终 D，覆盖前缀和实际递归后缀。
任意根扫描子列表的部分和不超过总质量 M，允许空非根族、全零和任意带符号费用。

与 G 包组合时，同时给出上述预处理位收费界和原来的 `resourceWork` 界。
`preBitWork + resourceWork` 是混合单位，未命名为 totalTime。
完整子树 DP 的所有标量操作、对象/地址/堆管理、编译后秒数及标准机器模拟仍未覆盖。

## 本次验证与复现

2026-11-17 实际执行并回读：

- 7 个新 Lean 模块定向构建成功，含直接公理审计入口。
- 118 个显式命名声明，加结构构造器/字段共 129 项，全部逐项直接打印并回读一次。
  只依赖 `propext / Classical.choice / Quot.sound` 子集，无 `sorryAx` 或额外未证公理。
- 13 个 `decide +kernel` 边界例子；608 组完整记录均通过 Prepared、整个证书、
  17 个 DP 字段、9 个载荷字段、独立计数递推和费用界检查。
  包括单根、零路线成功/失败、空及全零费用、同分母/互素分母、完全抵消、负 floor、
  巨大分母、`m=2^200` 拒绝，以及首个/中间/末个根状态接受和全失败。
- Python 独立重算全部 608 组数值、计数和位宽记录；并检查 66,049 对 Euclid 输入、
  400 对连续 Fibonacci 输入及 4,489 对规范分数加法。完整证书对照中，根编号 0 的通过
  分支包含首次接受 48 组、中间接受 4 组、末项接受 1 组、全失败 73 组；另有
  452 组预检拒绝和 30 组非零根。上述类别属于同一批记录，不累计成额外实例。
- 直接重新执行既有 G 包 603 组、F 包 603 组、A–E 的 483 组及 DP 的 21 组回归，
  全部通过。A–E 的入口也调用 21 组 DP 检查，不重复累计。
  这些重跑记录单列；没有把 Lake 的 `Replayed` 输出当作新执行。

使用既有 Lean `v4.30.0-rc2`、Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` 环境和缓存。
发布副本与本次编译的新源码保持字节一致。既有源码差异已核对为注释或空白；
不修改原目录中其他未提交文件。不是冷构建，没有新的性能测量或 TeX 编译。

在配置好的相同 Lean 环境执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSubtreePreAudit
lake env lean LeanCompletion/UAV/TreeBudgetSubtreePreExamples.lean *> verification/runs/subtree-preprocessing/examples.log
python tools/check_subtree_preprocessing.py --lean-log verification/runs/subtree-preprocessing/examples.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeResourceExamples.lean *> verification/runs/subtree-preprocessing/g-regression.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeAutoExamples.lean *> verification/runs/subtree-preprocessing/f-regression.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeBoundsExamples.lean *> verification/runs/subtree-preprocessing/ae-regression.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeDPExamples.lean *> verification/runs/subtree-preprocessing/dp-regression.log
```

`PreExamples` 输出的 `HCASE` 是本地验证数据；Python 用整数和 `Fraction` 独立重算
完整 Prepared、预检/预处理/入口计数、位宽和多项式界，并以既有独立 F 模型
复核根编号 0 的有序完整证书。非零根的全证书及全部统计由 Lean 回归与一般定理检查。
有限核对不代替 Lean 内核证明。原始日志、JSON、构建产物只留在忽略目录。

## 保留范围

#19 的给定游走拼接、实际逐顶点路线输出、进一步压缩及整个执行器的机器成本仍独立保留。
#21 的一般见证转换、#22 的最终验收、#23 的归约机器成本不由本包启动或改变。
