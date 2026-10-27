# 有界轮廓、精确分解与四节点见证（2026-10-27）

在 [10 月 26 日的轮廓割结果](COPY_PROFILE_CUTS_STATUS.md) 基础上，
提交 `d2ee5751dc6a01589bee5f99514f63076ef6406e` 原样发布三个本地新增模块，继续使用
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

用户于 2026-10-27 分三轮提供本地验证记录：

| 模块 | 执行方式 | 本轮该模块的公理报告 | 结果 |
| --- | --- | --- | --- |
| `CopyProfileRealizability` | `lake env lean .\LeanCompletion\UAV\CopyProfileRealizability.lean` | 4 项 | `LeanExitCode=0` |
| `CopyProfileDecomposition` | `lake build LeanCompletion.UAV.CopyProfileDecomposition` | 3 项 | Built，构建成功，`LeanExitCode=0` |
| `CopyProfileExample` | `lake build LeanCompletion.UAV.CopyProfileExample` | 7 项 | Built，构建成功，`LeanExitCode=0` |

合计 14 项不同声明的公理报告，按各自模块的三轮输出记录；后续构建
重放的依赖报告不重复计数，也不据此声称依赖在该轮全部重新编译。
这些报告覆盖三个文件现有的全部 `#print axioms` 命令：

- `CopyProfileRealizability`：`copiesBelow_card`、
  `visitProfile_le_required`、`canonicalSet_profile`、
  `realizableProfile_iff_bounds`。
- `CopyProfileDecomposition`：`profile_cuts_iff_bounded_profile_cuts`、
  `serviceCopyLift_iff_structural_bounded_profile_cuts`、
  `exact_decomposition_iff_bounded_profile_lift`。
- `CopyProfileExample`：`badProfile_values`、`badProfile_bounds`、
  `badProfile_kappa_eq_one`、`badProfile_work_eq_four`、
  `badProfile_requirement_eq_two`、`badProfile_violates_profile_cut`、
  `witness_not_all_bounded_profile_cuts`。

14 项报告仅列出 `propext`、`Classical.choice`、`Quot.sound` 或其子集，
均无 `sorryAx`。这些是用户提供的本地执行结果，本次文档同步未重新运行
Lean，也未做干净环境重建；用户输出未附源码哈希，因此尚未完成
历史构建与远端源码的哈希绑定。

原发布记录说明三份上传源码与发布时本地文件逐字节一致；这不等于
历史编译文件已获哈希绑定。本次仅把 `CopyProfileRealizability` 的文件头
改为指向本记录，定义、定理、证明及审计命令均未改动。
原发布源码检查未发现 `sorry`、`admit`、新增 `axiom` 声明或
`native_decide`。

后续可在已配置的工程根目录执行：

```powershell
lake build LeanCompletion.UAV.CopyProfileExample
```

原始终端输出不上传。冻结 Case1 模块、输入数据、证书、工具链、
依赖锁定和默认构建入口保持不变。
