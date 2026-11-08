# #22 第二块：二进制执行成本与存储精化（2026-11-07 历史包）

2026-11-08 更新：本文保留 11 月 7 日包的实现与验证边界。其后 [A–E 共享存储执行](TREE_BUDGET_STORED_EXECUTION_STATUS.md) 已接通完整堆执行，并证明新执行器自身的分配、地址位宽、总成本及所选模型下的 FPT。下文的未完成项描述历史状态，旧验证数字没有重新标记为本次检查。

本页接续已发布的[完整向量搜索精化](TREE_BUDGET_VECTOR_MEMO_REFINEMENT_STATUS.md)。
该历史阶段的验收标准包含具体堆访问与表示正确性；仅有当时下述执行器的工作量定理
不足以完成 #22。该缺口已由后续 A–E 包补齐，当前 #22 保持开放等待最终验收决定。

## 计算任务与输入

输入是自分隔二进制串，包含顶点数、根索引、父数组、重数向量、费用的原始有符号
分子与正分母，以及预算分数。自然数的低位在前，每个有效位由一位标记引入，
终止位为零；自然数零与负零有不同处理，非规范高位零被拒绝。
列表有长度字段，解析器在递归分配前检查长度不超过剩余输入位数。
完整输入不允许尾部垃圾。

`parseInput_canonical` 证明成功解析的输入恰等于该记录的规范编码，
因此后续位长中的 `ell` 是实际输入长度。
`decodeRawCost` 检查数组形状、所有索引、正分母及父指针；父树检查要求根指向自己、
每个顶点沿父数组走 `n` 步到根。其语义解释证明产生同根、同父指针的 `RootedTree`，
非计算的图与秩仅出现在证明中。

计算从给定 `H` 开始，根坐标归零，初始层数取规范 `rootCount`，缓存为空。
输出区分非法输入、合法但无解、成功的空矩阵和成功的非空矩阵。
需求到 `H` 的包装器、实际顶点路线展开及压缩输出均不包含在此任务中。

## 同一个可执行程序的对应

`TreeBudgetCostedExecution.execute` 依次执行实际解析、输入校验、清分母、
候选生成与检查、搜索和矩阵序列化。
`execute_value` 将其值精确接回 `TreeBudgetBinaryPipeline.run`；
`preparedSearch_observe` 接回原向量搜索的具体答案、有序缓存和六类事件计数。
矩阵编码有解码往返定理。

`TreeBudgetBinaryCorrectness.execute_output_correct` 从成功解析的实际输入比特串
直接得到“输出存在当且仅当原始分数下的 `MatrixFeasible`”；
`execute_refines` 同时固定完整返回记录、矩阵解码、有序缓存和六类计数。
`execute_success_sound` 将成功输出对应的具体证书接回原有检查器。

清分母用逐位移位加法乘法计算其余分母的乘积，避免把整除当作原子操作；
`cofactorCost_value`、`scaleFeesCost_value`、`scaleBudgetCost_value` 证明与原缩放公式相同。
位长证明允许未约分分数、负费用和负预算，控制所有部分和的绝对值，不能用最终
抵消后的数值代替中间量上界。

键比较、守卫、减法和零测试由逐位原语实现。向量比较先物化全部比较结果再求合取。
搜索保留首命中、有序完整插入过滤、失败后传递缓存、成功时提前停止。
查表比较和插入过滤比较都计费。成功答案的长度和坐标界覆盖临时返回值以及缓存成员。

## 历史包已实现的工作量与当时边界

令 `S` 为规范化输入的非根状态盒大小，`M` 为非根总重数，`t` 为正非根坐标数，
`U` 为最大非根重数。完整成本执行器累计的内在单元工作量满足：

```text
execute.steps ≤ 8,388,608 * S^3 * (ell + 1)^4
```

主定理为 `TreeBudgetBinaryTotalWork.execute_steps_state_cube`。
其前提仅是实际解析、校验成功的等式，没有把目标总成本界作为假设。
该累计量包含从解析到矩阵写出的所有阶段；它仍是当前成本执行器的工作量指标，
尚未识别为带地址访问的参考机时间或 Lean 编译程序的时间。

同一工作量定理已作 `S≤2^M` 与 `S≤(U+1)^t` 的参数代入。
这些定理的名称明确使用 `steps`，不把参数代入本身宣称为已验收的机器时间 FPT 结论。
[文献与模型对照](TREE_BUDGET_COST_MODEL_COMPARISON.md)说明了完整时间界成立后如何得到
FPT(`M`)、FPT(`t,U`) 与一元编码下的 XP(`t`)，以及二进制显式输出的长度障碍。

现有分配计数沿实际搜索递归累加，保留行向量、答案尾部与条目负载的共享；
搜索分配计数不超过其内在工作量的八倍。先证明分配数量，再证明地址位长，
没有用待证总时间反推地址宽度。

新增的具体存储组件有三层，它们与完整执行器的连接尚未证明：

| 模块 | 已证明的范围 |
| --- | --- |
| `TreeBudgetTypedStore` | 追加分配的比特／引用槽、不可变块、字与引用数组解码；新块正确、旧块保持、引用合法 |
| `TreeBudgetAddressedBlocks` | 地址逐位解码后选择真实堆槽，引用负载逐位传输，读块与复制的实际循环、成本界和表示保持 |
| `TreeBudgetSearchStore` | 键和答案的二进制负载、实际长度头、缓存节点的键／答案／尾引用；有序缓存解码、重复键首命中、追加共享及旧表示保持 |

其中缓存对象层目前使用未带成本的堆读接口；它并未自动调用带地址收费的块接口。
块复制定理中的空间容量前提也尚未由完整程序的分配轨迹统一消去。
当前答案对象是完整矩阵的二进制块，缓存追加共享已有负载引用；新答案的构造仍须
实现共享行链或按实际编码长度计费。因此上述搜索计数器的八倍界不能直接用作
这个具体对象布局的累计堆分配界。

完整验收仍须将搜索中的键、向量、答案、缓存及帧放进具体引用存储：

1. 构造、读、复制与共享保持解码关系，且每个引用在已分配区域内。
2. 每次程序访问实际经过带地址收费的存储原语。
3. 对递归与候选后缀归纳，同时保持值、缓存顺序、事件、存储不变量和成本。
4. 从该完整存储执行得到总时间定理，再给出时间意义的参数化结论。

单独的地址扫描循环、分配上界或固定地址宽度乘数都不能替代上述程序精化。
本次不据此关闭 #22，也不将历史纸面 RAM 界改称新完成的 Lean 时间证明。

## 验证与复现

验证使用仓库固定的 Lean 工具链与依赖，本地缓存复用；不声称新环境重建、
远端 CI 或运行时间实验。原始构建、公理审计和回归输出保留在被忽略的
`verification/runs/issue22-bit-cost-20261107/`。

发布源的既有项目依赖与已发布基线逐文件对照；差异只涉及四个文件的换行或末尾空白。
工具链、Lean 选项以及发布仓库的九项依赖版本一致；开发环境额外的 Prim、repl、
LeanArchitect 不在本包导入闭包中。发布工作区本身未另行作干净重建。

本次最终联合构建显式列入全部 **37 个新模块**，退出 0，完成 **8399 项构建任务**
（包含复用缓存）。共有 **611 个定理声明，其中 40 个为 Examples 模块中的边界回归**。
另对全部 **866 项显式声明**逐项执行 `#print axioms`，退出 0，866 项全部有报告；
公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`。
公开审计入口的 21 项主要接口也单独执行通过。新增源码没有 `sorry`、`admit`、
新增 `axiom`、`unsafe` 或 `native_decide`。既有依赖与部分新模块仍有非阻断的
样式、未使用简化参数等 linter 警告；不声称无警告构建。

以下公开入口的导入闭包覆盖这些新模块，可复现构建和主要接口审计：

```powershell
$binaryTargets = @(
  'LeanCompletion.UAV.TreeBudgetBinaryTotalWork',
  'LeanCompletion.UAV.TreeBudgetBinaryCorrectness',
  'LeanCompletion.UAV.TreeBudgetBinaryExamples',
  'LeanCompletion.UAV.TreeBudgetCostedCandidatesExamples',
  'LeanCompletion.UAV.TreeBudgetCostedInputExamples',
  'LeanCompletion.UAV.TreeBudgetCostedExecutionExamples',
  'LeanCompletion.UAV.TreeBudgetAddressedBlocksExamples',
  'LeanCompletion.UAV.TreeBudgetSearchStoreExamples'
)
lake build @binaryTargets
lake env lean verification/AuditTreeBudgetBinaryCost.lean
```

边界回归包括非首位置根、非法父环、
零分母、负数与未约分分数、非规范或截断字、尾部垃圾、超大数组计数、失败缓存
首命中、成功空答案，以及成功时的具体答案、缓存顺序与六类计数；新增存储回归
覆盖地址跨越 8／16、复制保留旧块、共享引用以及堆缓存中的重复键首命中。

发布基线为 `4243887554da87d090c81ec3e150efc3d2511777`，目标是
`huam54925-cpu/uav-routing-certification` 的既有
`research/structural-service-cuts-20261023` 分支。发布只包含这 37 个模块、公开审计
源码、两份新说明，以及 README 和旧成本说明的状态同步；原始日志与生成的审计
清单留在本地。旧成本说明仅更新历史状态，本次未重新编译 LaTeX 或生成 PDF。
