# 有界轮廓、精确分解与四节点见证（2026-10-27）

在 [10 月 26 日的轮廓割结果](COPY_PROFILE_CUTS_STATUS.md) 基础上，
本次原样发布三个本地新增模块，继续使用
`research/structural-service-cuts-20261023` 分支。

## 新增结果与边界

| 源码 | 主要结论 |
| --- | --- |
| [CopyProfileRealizability](../LeanCompletion/UAV/CopyProfileRealizability.lean) | `realizableProfile_iff_bounds`：轮廓可实现，当且仅当基地计数为零且每个非基地节点的自然数计数不超过需求。通过选择每个节点的前若干个副本构造规范实现子集。 |
| [CopyProfileDecomposition](../LeanCompletion/UAV/CopyProfileDecomposition.lean) | `exact_decomposition_iff_bounded_profile_lift`：预算可行的精确路线分解存在，当且仅当存在结构副本提升满足全部有界轮廓最小割约束。 |
| [CopyProfileExample](../LeanCompletion/UAV/CopyProfileExample.lean) | 对既有四节点 `witnessFlow`，轮廓 `(0,2,1,0)` 的服务量为 4、预算为 3、最小出割 `kappa = 1`，取整需求为 2，因此该轮廓割失败。 |

分解等价定理保留无自环物理流、服务费用非负、预算严格为正的假设；
路线数等于基地出流，并精确保持需求与边流。预算只计服务费用，
不含飞行费用。轮廓范围的明确化没有给出高效提升搜索或最小割算法。
示例中的 `kappa = 1` 针对固定的 `witnessFlow`，不推广为所有提升的数值。

## 验证来源

用户于 2026-10-27 提供本地 Lake 构建完成记录：目标
`LeanCompletion.UAV.CopyProfileExample` 构建成功，`LeanExitCode=0`。
该目标导入 `CopyProfileDecomposition`，后者导入
`CopyProfileRealizability` 与既有 `CopyProfileCuts`。

用户提供的输出包含 `CopyProfileExample` 的七项公理报告：
`badProfile_values`、`badProfile_bounds`、`badProfile_kappa_eq_one`、
`badProfile_work_eq_four`、`badProfile_requirement_eq_two`、
`badProfile_violates_profile_cut`、`witness_not_all_bounded_profile_cuts`。
这些报告仅列出 `propext`、`Classical.choice`、`Quot.sound` 或其子集，
没有 `sorryAx`。所提供的片段未包含前两个模块的独立公理报告，
因此不将它表述为三个模块全部审计命令的新输出。

本次上传检查了三份源码、导入依赖、文档链接和提交差异，未重新运行
Lean，也未做干净环境重建。三份发布源码与当前本地文件逐字节一致；
用户构建输出未附源码哈希，因此不声称已完成该历史构建与文件的哈希绑定。
源码未发现 `sorry`、`admit`、新增 `axiom` 声明或 `native_decide`。
`CopyProfileRealizability` 文件头关于回复环境未编译的说明保留原样；
它指写作阶段，与上述用户提供的后续构建记录分别说明。

后续可在已配置的工程根目录执行：

```powershell
lake build LeanCompletion.UAV.CopyProfileExample
```

原始终端输出不上传。冻结 Case1 模块、输入数据、证书、工具链、
依赖锁定和默认构建入口保持不变。
