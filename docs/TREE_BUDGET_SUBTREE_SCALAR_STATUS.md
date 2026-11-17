# 子树 DP 统一标量收费（I0–I4）

基线为研究分支的 H 包 `b23b766e2e202e134546a3e1b781f0ca4c2bafbe`。
本包固定当前候选、去重和矩阵表示，连接 G 的资源统计与 H 的算术收费。

## 执行与收费契约

输入沿用 H 的物化 `Input`：根、父编号、质量、服务系数、路线数和预算。
树的秩与合法性证明仅用于终止和正确性，不是运行时遍历输入。
`Represents` 连接父编号表与 `RootedTree`；`childrenInputC_eq`、`candidateCapInputC_eq`
给出父编号向量读取版本与树接口版本的整个计数记录相等；父关系查询具有
具体物化读取实现。
拒绝分支在 `prepareC`、任何路线维向量和 DP 之前返回。

本包沿用 H 的数学算术模型。一次标量读、写、算术、测试、布尔操作、
列表构造／析构或控制指令计一个单位。固定大小的记录构造及字段访问使用
源码列明的指令数。下表的终止测试也收费；复合布尔谓词使用固定的标量
指令块，外层坐标扫描和成员扫描保持短路。证明、统计和费用观察为 ghost，
不把这些观察字段的维护实现算入被分析程序。

| 操作 | 执行收费／边界 |
| --- | --- |
| 编号枚举 | 每个编号两条指令，加一个终止测试；含索引递增与写入 |
| `mapC` | 每个回调加三条列表控制指令，终止一条 |
| `filterC` | 每个谓词加四条列表控制指令，终止一条 |
| `appendC` | 左表每格三条，终止一条；右表复用 |
| `flatMapC` | 显式包含回调、左表 append 和外层控制 |
| `allC` | 每个实际检查的谓词加三条控制指令，遍历完成再计一条 |
| 向量构造 | 每格回调外计五条写入、游标和控制指令，终止一条 |
| 向量相等 | 先收费编号枚举；每个实际比较坐标两次读取、一次相等测试；从左至右短路 |
| 状态相等 | active／used 在 cost 之前；第一字段不等时不读取 cost 坐标 |
| 支持、加法、初始乘积 | 每格分别两、三、四条回调指令；再加向量构造控制 |
| 候选 cons | 每格三条 head／tail 分支、索引转换和读取指令；再加向量构造控制 |
| 孩子列表 | 每次扫描全部 N 编号；枚举、父读取、谓词、过滤共 `12*N+2` |
| 去重 | 先递归尾表，再完整映射所有尾表键，最后短路成员扫描；保留右侧代表 |
| 矩阵拼接 | 每路线、每顶点；非本顶点先映射所有孩子坐标，再自然数求和；包含临时列表和部分和 |
| 根部处理 | 初始零向量、全部 raw 状态加法、cap 过滤、去重、首次接受扫描和证书构造均收费 |

各复合阶段的费用是子调用实际费用之和，加以下固定控制块。它们是本包
约定的源指令；没有用全局上界回填计数。

| 阶段 | 子调用以外的控制收费 |
| --- | --- |
| `compositionsC` | 零维分支 4；递归层每个选值的范围生成、减法、调用控制 6，再加 4；每个递归结果封装 1 |
| `candidatesC` | 质量／父关系接口和候选结果控制 3 |
| `insidePairC` / `rootPairC` | 向量参数／picks 字段读取、picks cons 与结果封装共 5 |
| `insideC` / `rootsC` 的递归层 | 子结果接入、记录及分支控制共 5 |
| `entryC` | 选择与矩阵参数读取、状态及条目封装共 5 |
| `nodeRunC` | support、scale、inside、结果映射的接口控制共 4 |
| `collectC` | 每个结果列表格的读取、构造、继续共 3，终止 1；统计聚合为 ghost |
| `nodeC` / `computeC` | 子调用接口与结果封装各 5 |
| `findC` | 每个实际谓词外的列表读取、选择／分支控制 4；耗尽 1 |
| `finishC` | `none` 分支 2；接受分支在零向量和矩阵构造外计 6 |
| `solveC` | 五个阶段的接口及返回控制共 7 |
| `executeC` | 通过分支在 guard、prepare、DP 外计 8；拒绝分支在 guard 外计 1 |

复合字段访问指逻辑记录字段路径；对象寻址、指针追踪与真实布局在下一层
建立。所有按维度、表长、实际比较次数增长的工作由循环递推给出。

对象标识、真实地址、分配器、共享引用、垃圾回收、栈／控制帧和编译器
实现仍在模型之外。`attach` 的证明成分按擦除解释；有序孩子值的映射控制
已经计费。本包没有改变候选、孩子、比较字段、去重代表或矩阵的表示顺序。

## 单次执行和结果精化

`Counted` 由实际循环返回值及次数。`mapWork`、`allWork`、`memberWork`、
`dedupWork` 和候选次数递推独立描述计数；全局上界没有用于定义 `ops`。
矩阵拼接的计数是

```
8*m*N + 10*m*(N-1)*k + 5*m + 1
```

其中 `k` 为选择的孩子数。`glueC_work_bound` 把它接到 G 的 `glueCharge`，
复用原来的矩阵语义。`keyMapCells` 与 `eqCalls` 分别进入新费用；一次
`eqCall` 已展开为实际访问的坐标，而不是把整条向量比较当作常数。

`insideC_value`、`nodeC_value`、`computeC_value`、`rootsC_value`、
`solveC_value` 均为整个 `ResourceResult` 相等，包括有序表、picks、矩阵
和 17＋9 个字段。`findC_value` 保持实际首个接受项。`executeC` 只执行
一次 guard、一次 prepare 和一次新 DP；旧执行器仅出现在精化定理和测试中。

## 费用连接

令 `R_G = resourceWork (solveR ...)`。`solveC_ops_le_resource` 证明的具体连接式为

```
C_DP <= 4096*(N+1)*(m+1)^2*(1+R_G).
```

空表循环、候选递归控制、各层映射／连接、根部零向量和 N 编号扫描已
包含在左侧实际计数中。局部证明先保留孩子表数量和输入表长度，再在树
递归中使用 `nodeCalls`、候选统计及已付费的输出表长度消去这些额外项。
随后代入 G 的既有定理得到 `dpUpper N m U P`；这里只要求非根质量不超过 U。

共同宽度使用保守的控制界：列表游标的位宽不超过其已收费构造次数。
因此无需假设堆容量，也不需要先实现地址布局。设 `b=serviceBits I`、
`h=massBits I`、`mu=I.routes.size`，令 `Cbar=inputDPUpper R I`，则

```
W_DP(c) = (N+2)*(b+h+2) + N + m + c + 4
W_* = max ((N+2)*(2*b+h+mu+4)) (W_DP(Cbar)).
```

这刻意采用较宽的 padding，没有声称最小位宽。它覆盖有符号原始费用、
未接受的根部 used／cost、候选乘积、矩阵临时部分和、索引和列表控制。
`ScalarRanges` 直接复用 G 的 raw／选择语义，不以最终接受证书范围替代
中间状态范围。`ScalarControls` 进一步把回调、候选递归和树后代的实际费用接到外层调用；
`executeC_table_cursor_fits` 覆盖每个实际后代表的前缀／后缀游标。
H 的预处理内部算术范围继续由 H 定理覆盖。

`executeC_bitWork_le` 使用同一全段最大宽度：

```
bitWork (executeC R I)
  <= 32*(W_*+1)^2*(128*(N+1)*(b+1) + Cbar + 6).
```

新增接入六条指令来自入口参数／Prepared 字段读取和控制。预处理部分
按共同宽度重新收费，未使用两个不同宽度的 `bitWork` 之和。拒绝分支
与 H 的执行记录完全相等，保留
`32*(guardWidth N h mu+1)^2*(12*N+5)` 专门界。

## 验证与复现

2026-11-17 在既有开发环境实际执行并通过以下检查。

| 检查 | 本次记录 |
| --- | --- |
| 定向 Lean 构建 | 13 个新增模块全部通过；`ScalarAudit` 目标构建成功 |
| 新具名声明及 `Counted` 接口直接公理审计 | 205 项在构建与直接运行输出中逐项齐全；仅 `propext`、`Classical.choice`、`Quot.sound` 子集，无 `sorryAx` 或额外公理 |
| 新 Lean 回归 | 608 个完整记录，156 个通过预检、452 个预检拒绝；全部 17＋9 字段与旧入口相等 |
| 坐标比较 | Lean 与 Python 各 1,225 例；空向量、相等、首／末坐标不同、长公共前缀 |
| 内核例子 | 11 例；右侧代表、全 N 扫描、根 cap 拒绝、空表、零路线、巨大 m 提前拒绝 |
| 新 Python | 608 个完整证书与精确计数重放，含非零根；所有 G 字段、原始费用与矩阵部分和范围 |
| H/G/F/旧 DP | 直接重跑 H 608、G 603、F 603、A–E 483 及基础 DP 21，全部通过 |
| G Python | 3,680 表型、22,080 资源／位宽／根预检型，全部通过；新增可选根参数，默认行为保持 |

新 Python 使用循环中的收费器独立累加次数；不从 G 总界反推计数。
G Python 的可选根参数允许逐项复核非零根，保持原编号顺序。新检查器还
拒绝带 Lean 错误或不完整记录的日志。有限回归不代替一般 Lean 定理。

复现命令（在 Lake 项目根，PowerShell；目录保持忽略）：

```powershell
New-Item -ItemType Directory -Force verification/runs/subtree-scalar | Out-Null
lake build LeanCompletion.UAV.TreeBudgetSubtreeScalarAudit *> verification/runs/subtree-scalar/build.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeScalarAudit.lean *> verification/runs/subtree-scalar/audit.log
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeScalarExamples.lean *> verification/runs/subtree-scalar/examples.log
python -B tools/check_subtree_scalar.py --lean-log verification/runs/subtree-scalar/examples.log
python -B tools/check_subtree_resources.py *> verification/runs/subtree-scalar/python-resources.log
```


沿用 Lean `v4.30.0-rc2`、Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
与现有开发缓存，定向构建。13 个新增源码与验证副本逐字节相同；73 个
项目内导入模块除换行／文件末尾空行外一致，发布包的依赖修订号一致。
开发工程额外依赖未被这些模块导入。不做冷构建、TeX
编译或实际运行时间声明。原始输出仅保留在本地忽略目录
`verification/runs/subtree-scalar/`。

## 后续边界

下一层是对象表示、真实地址读写、分配、共享和控制帧的执行精化。
#22 的组件只有在证明与本执行器调用对应后才能复用；其整个存储搜索
时间定理不能直接移植。#19 的逐顶点游走输出／拼接、#21 一般见证转换
和 #23 归约机器成本继续保持各自范围。
