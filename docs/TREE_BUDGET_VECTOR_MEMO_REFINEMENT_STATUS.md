# 完整显式搜索精化：#22 第一大块

日期：2026-11-07（Asia/Tokyo）。本包承接已完成的显式候选列表对应，交付向量搜索的完整执行精化；#22 的编码、原语成本、位长、地址与存储和总时间证明仍是后续范围。

## 验收接口

| 模块 | 完成接口 |
| --- | --- |
| [TreeBudgetVectorMemoState](../LeanCompletion/UAV/TreeBudgetVectorMemoState.lean) | 数组向量键、答案和关联表缓存；解码；首命中查表与删除全部同键项的稳定插入对应 |
| [TreeBudgetVectorMemoSearch](../LeanCompletion/UAV/TreeBudgetVectorMemoSearch.lean) | 独立普通扫描与递归执行器；失败传递子缓存，递归始终复用完整候选表 |
| [TreeBudgetVectorSearchStats](../LeanCompletion/UAV/TreeBudgetVectorSearchStats.lean) | 独立统计执行器、统计擦除、通用扫描精化、完整执行精化及逻辑保留行数对应 |
| [TreeBudgetVectorMemoIntegration](../LeanCompletion/UAV/TreeBudgetVectorMemoIntegration.lean) | 整数缩放与原始正分母分数入口、根规范化、具体证书、成功／失败语义、缓存成员界与计数界转移 |
| [TreeBudgetVectorMemoExamples](../LeanCompletion/UAV/TreeBudgetVectorMemoExamples.lean) | 内核计算的控制流和正式入口边界回归 |

核心定理 `TreeBudgetVectorSearchStats.memoStatV_refines` 对任意候选列表、层数、残量和原始缓存证明：

```text
decodeMeasured (memoStatV ps k r cs)
  = TreeBudgetSearchStats.memoStat (ps.map decode) k (decode r) (decodeCache cs)
```

这是一条完整结果等式，保留具体答案、缓存顺序与重数，以及 `calls`、`hits`、`expansions`、`candidates`、`lookupComparisons`、`insertionScans` 六字段。它不预设候选合法、无重复或缓存合法。`memoStatV_erase` 证明统计擦除恰为独立普通执行器；`memoRowsWithV_refines` 由该擦除和完整精化导出普通结果对应。执行器直接使用向量比较、零测试和物化截断减法，未以解码后调用旧执行器代替实现。

`scanStatV_refines` 对候选后缀归纳并推广缓存；`memoStatV_refines` 对层数归纳并推广残量和缓存。查表命中失败与命中空成功保持不同；零层也先查表；插入统计来自扫描完成后的缓存长度。计数不包含候选生成费用，完整键比较次数也不等于向量坐标比较或位操作次数。

## 正式入口与性质转移

入口先规范化根坐标，再为同一规范化总需求生成一次完整候选表，并以空缓存启动。指定路线数的入口给出与 `searchMemo` 返回证书的精确相等及成功／失败语义；统一计数界使用规定的 `rootCount` 初始层数。

整数费用入口使用正比例缩放假设；原始分数入口仅要求各分母为正，允许负费用、负预算和未约分分数。树仍由现有 `RootedTree` 提供，父数组的输入编解码及其成本不在本包内。

`CacheReadyV` 拉回现有 `CacheValid ∧ KeysNodup ∧ AllKeysReachable`。中间递归在残量可达、原缓存就绪的条件下保持该性质；中间扫描另要求候选合法。正式空缓存入口的保持性及成员界使用规范化需求和 `rootCount` 初始层数，不覆盖任意指定路线数。对每个实际成功缓存成员得到行数等于键中的层数、层数不超过初始 `rootCount`、行根坐标为零和逐坐标上界。这里保留无重复键条件，避免被遮挡的非法条目逃过约束。

六字段精确相等使现有逻辑界直接适用于向量实现：以 `S = ∏(H(v)+1)`（非根坐标）计，展开与缓存规模至多 `S`，候选检查至多 `S²`，调用至多 `1+S²`，查表比较至多 `S+S³`，插入扫描至多 `S(S−1)/2`；命中与调用、展开满足原有记账恒等式。另转移 `S≤2^M` 和 `S≤(U+1)^t` 的参数化逻辑界。这些不是运行时间或峰值内存定理。

## 回归范围

回归核验完整缓存或具体证书，覆盖同键冲突首项优先和稳定全过滤，三种查表结果，零层缓存优先，较后缓存项命中，空成功／失败，重复候选失败后命中，残量保护，失败缓存传给后续成功，成功提前停止，递归重复使用同一行，非零根坐标输入，负费用／预算和未约分分数。

原始一维例 `ps=[1,1], k=1, r=2, cs=[]` 得到六字段 `(3,1,2,2,1,1)`，用于捕获错误去重或丢失失败缓存；它不是合法树实例的声明。

## 验证与发布

在现有锁定开发环境实际执行以下最终联合构建，退出 0，完成 8365 个构建任务（含复用依赖缓存）：

```powershell
lake build LeanCompletion.UAV.TreeBudgetVectorMemoState LeanCompletion.UAV.TreeBudgetVectorMemoSearch LeanCompletion.UAV.TreeBudgetVectorSearchStats LeanCompletion.UAV.TreeBudgetVectorMemoIntegration LeanCompletion.UAV.TreeBudgetVectorMemoExamples
```

五个新模块共有 **63 个定理，其中 14 个是边界回归**。回归使用 `decide +kernel`；完整二元组结果先用 `Prod.ext` 分解，再逐分量由内核计算，完整等式的声明保持不变。没有增加局部或项目编译选项。

另按源文件完整列举定义、缩写、结构和定理，对全部 **93 项显式声明**执行 `#print axioms`，审计命令为：

```powershell
lake env lean verification/runs/issue22-full-refinement-20261107/AuditAll.lean
```

该次审计退出 0，93 项均有输出，无遗漏；依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`。新增源码无 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。五个新增模块无编译警告；既有依赖重放的警告与本包区分。此验证使用现有依赖缓存，不是新环境重建、远端 CI 或性能测量。

开发中的失败检查包括长度引理参数、解码过度展开、归纳证明改写、性质转移中的表达式匹配，以及嵌套结果相等的可判定性合成。最终版本均已修正；失败运行及主动停止的重复检查不计为 PASS。最终构建和审计原始输出分别为本地 `final-build-success.log`、`all-axioms.log`，仅保存在 ignored `verification/runs/issue22-full-refinement-20261107/`，不纳入提交。

发布基线为 `85fc3a92ec659970e0596d8778fc7b7c98d12043`，目标为 `huam54925-cpu/uav-routing-certification` 的既有 `research/structural-service-cuts-20261023` 分支，使用独立发布工作区。提交限定为五个新 Lean 模块、本说明和 README。新模块导入闭包包含 48 个既有项目模块，忽略换行和末尾空白后均与目标基线一致；工具链、Lean 选项和目标使用的 9 个依赖锁定版本一致。本地额外的 Prim、repl、LeanArchitect 不在新模块导入闭包中。

开发工作区的 121 个既有 UAV Lean 文件经前后 SHA-256 核对未改变，原有根导入、工具链、配置、依赖锁定和冻结验证输入未修改。发布源码与最终验证源码逐字节核对；发布工作区未另行重建。未修改远端议题，#22 不作为整个完成关闭。
