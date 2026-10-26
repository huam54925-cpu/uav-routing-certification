# 副本障碍与轮廓割等价性（2026-10-26）

本次在 `research/structural-service-cuts-20261023` 分支发布五个新模块，
以前序提交 `f7147cf13d043537fc1a2f2d361eee251b3685e6` 为基础。
五个文件原样保留本地源码；文件头的“待编译”是写作阶段的旧状态，
当前验证范围以本文为准。

## 新增结果

| 模块 | 结果 |
| --- | --- |
| [CopyLiftObstruction](../LeanCompletion/UAV/CopyLiftObstruction.lean) | 由精确预算可行分解不存在推出服务副本提升不存在；每个结构提升都有违规副本割，并给出四节点具体见证。违规子集可依赖于提升，并非一个子集对所有提升都违规。 |
| [CopyFiberCompression](../LeanCompletion/UAV/CopyFiberCompression.lean) | 同一副本流中，两个子集的逐点副本数量相同，出割流分别为 1、2，容量割结论相反。仅靠数量不能恢复单个子集的割值或通过状态。 |
| [CopyProfileService](../LeanCompletion/UAV/CopyProfileService.lean) | 不含基地副本的子集，其服务总量及取整需求仅由逐点数量轮廓决定。 |
| [CopyProfileMinimum](../LeanCompletion/UAV/CopyProfileMinimum.lean) | 对可实现轮廓定义最小出割值 `kappa`，证明最小值可达且不大于任一实现子集的出割值。 |
| [CopyProfileCuts](../LeanCompletion/UAV/CopyProfileCuts.lean) | 对同一个副本流，全部副本容量割与按可实现轮廓最小出割值表达的全部轮廓割等价，并衔接原提升定义中的非空子集条件。 |

依赖链为 `CopyLiftObstruction → CopyFiberCompression → CopyProfileService
→ CopyProfileMinimum → CopyProfileCuts`；首个模块导入既有
`VisitCopyLift` 和 `FixedFlowObstruction`。

轮廓最小值仍依赖给定副本流，且只对有实现见证的轮廓定义。
这里证明的是精确的数学重组，不提供高效最小化算法，也不声称单个
子集的割流由轮廓唯一确定。服务恒等式及割重组本身不要求服务非负、
预算为正；路由分解应用仍保留其相应假设。模型沿用仅计服务费用的设置。

## 本次实际验证

2026-10-26，在已有本地 JSP 扩展工程中执行：

```powershell
lake build LeanCompletion.UAV.CopyProfileCuts
```

退出码为 0，构建成功。工具链为 Lean `4.30.0-rc2`，mathlib 为
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`，与 UAV 工程的固定版本一致。

- `CopyProfileCuts` 本次从源码构建，输出 5 项公理报告。
- 其余四个新模块由 Lake 复用既有缓存，并重放各自 10、9、6、3 项报告；
  不将这 28 项重放报告描述为本次重新编译或重新审计。
- 上述 33 项输出中的公理仅含 `propext`、`Classical.choice`、`Quot.sound`
  或其子集，未见 `sorryAx`。五个文件未发现 `sorry`、`admit`、新增
  `axiom` 声明或 `native_decide`。
- 构建输出包含已有 linter 警告，涉及未使用类型类假设、注释及资源限制
  说明等；构建没有因此失败。

本次使用已有依赖与构建缓存，未进行独立 UAV 工程的干净环境重建。
原始输出仅保留在本地忽略目录 `verification/runs/publish-20261026/`。
源码、文档链接及提交差异另经检查；冻结 Case1 模块、数据、证书、
工具链、依赖锁定和默认构建入口保持不变。
