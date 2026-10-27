# 轮廓最小割枚举器与容量割检查器（2026-10-27）

本次在研究分支最新提交 `90840f6` 基础上，原样发布两个新增模块，
保留已有证明和最新文档更新。

## 新增接口

- [CopyProfileEnumeration](../LeanCompletion/UAV/CopyProfileEnumeration.lean)
  枚举不含基地且实现指定轮廓的副本子集。`minimumValue?` 返回最小出割值；
  不可实现轮廓返回 `none`，可实现的零值返回 `some 0`。
  `minimumValue_eq_kappa` 将计算值连接到数学定义；`minimizingSubsets`
  返回全部达到最小值的子集，并附成员刻画及非空性证明。
- [CopyProfileChecker](../LeanCompletion/UAV/CopyProfileChecker.lean)
  用有限类型枚举全部有界轮廓。`checkAll_eq_true_iff` 证明布尔检查等价于
  `AllBoundedProfileCuts`；`violatingProfiles` 返回失败轮廓，
  `violatingProfile_has_counterexample` 提供最优子集中的违规见证。
  `serviceCopyLift_iff_structural_check` 将检查结果接回完整服务提升条件。

这是对固定副本流的指数规模枚举基准，不搜索副本流，也不宣称多项式复杂度。
`checkAll` 只检查容量割；完整提升还必须满足 `IsStructuralCopyLift`。
路线模型和分解接口沿用[前阶段结果](COPY_PROFILE_DECOMPOSITION_STATUS.md)。

## 后续认证（2026-10-27）

提交 [1e1f829](https://github.com/huam54925-cpu/uav-routing-certification/commit/1e1f82901cdd9932ebcbd19596a54698089a58ed)
新增 `CopyProfileReport.witness_check_four`，使用 `decide +kernel`
证明既有四节点 witnessFlow 在预算 4 下的检查为真，并结合结构条件得到
服务提升和精确分解。详见[报告及验证记录](COPY_PROFILE_REPORT_STATUS.md)。

下方“本次验证范围”保留检查器发布时的缓存重放记录。
其中“预算 4 的 #eval 本身不是独立 Lean 定理”仍成立；
后续新增定理提供了另一个证明层次，不能反向把先前的 #eval 记成内核证明。
本次说明更新没有重新编译枚举器或检查器。

## 本次验证范围

2026-10-27，在已有本地工程执行：

```powershell
lake build LeanCompletion.UAV.CopyProfileChecker
```

退出码 0，构建成功。两个新增模块均显示 `Replayed`，使用已有缓存；
本次没有从源码重新编译它们，也不将缓存重放描述为新的独立公理审计。

重放输出中，枚举器的三个示例依次为 `some 1`、`some 0`、`none`；
检查器在既有四节点副本流、预算 3 和预算 4 下分别输出 `false`、`true`。
这些是缓存中的运行输出，预算 4 的 `#eval` 本身不是独立的 Lean 定理。
枚举器 9 项、检查器 8 项公理报告仅列出 `propext`、`Classical.choice`、
`Quot.sound` 或其子集，未见 `sorryAx`。
构建包含未使用类型类假设和空行风格等 linter 警告，未导致失败。

发布文件与当前本地源码逐字节一致，未发现 `sorry`、`admit`、新增
`axiom` 声明或 `native_decide`；另检查导入依赖、文档链接和提交差异。
本次不是独立 UAV 工程的干净环境重建。原始输出仅存于本地忽略目录
`verification/runs/publish-20261027-checker/`。冻结 Case1 模块、数据、
证书、工具链、依赖锁定和默认构建入口保持不变。
