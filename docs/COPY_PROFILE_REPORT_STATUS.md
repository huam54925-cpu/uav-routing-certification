# 违规报告与预算 4 的内核证明（2026-10-27）

[CopyProfileReport.lean](../LeanCompletion/UAV/CopyProfileReport.lean)
在[轮廓检查器](COPY_PROFILE_CHECKER_STATUS.md)基础上，增加四节点实例的
可读违规报告，以及预算 4 时的肯定结果。

- `reportRows` 枚举失败轮廓及全部最优实现子集；
  `report_cutValue_eq_kappa` 证明显示的割值等于轮廓最小值，
  `reportRows_sound` 证明每条报告都严格违反容量割。
- `witness_check_four` 使用 `decide +kernel` 证明预算 4 的检查为真，
  随后通过既有正确性接口得到全部有界轮廓割、完整服务提升和
  `exact_decomposition_four` 的预算可行精确分解。
- `reportRows_four_eq_empty` 证明预算 4 时无违规报告。

以上固定使用既有四节点 `witnessFlow` 和 `fixedFlow`。预算仅计服务费用，
不含飞行费用；这里的预算数值 4 不是 Case1 的无人机数量结论。

## 本次实际验证

2026-10-27，在已有本地工程执行
`lake build LeanCompletion.UAV.CopyProfileReport`，退出码为 0。
Lake 将该模块从源码构建（`Built`，约 25 秒），导入依赖复用既有缓存。
七项公理报告仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
有空行风格和资源限制说明的 linter 警告，未导致构建失败。

本次运行得到一条预算 3 的违规记录：轮廓 `(0,2,1,0)`，服务量 4，
所需出割 2，实际割值 1，选中副本 `v1#0`、`v1#1`、`v2#0`。
预算 4 的报告列表为空、记录数为 0。预算 4 的肯定结果同时有上述
内核检查定理支持，已超出前阶段仅运行 `#eval` 的证据范围。

发布源码原样保留，与当前本地文件逐字节一致。检查了文档链接和提交差异；
冻结证明、数据和依赖配置保持不变。未进行独立 UAV 工程的干净环境重建。
原始输出仅保存在本地忽略目录 `verification/runs/publish-20261027-report/`。
