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

## 同一固定流的正反对照与下一步

预算 3 的全局不可行性已经由
[CopyLiftObstruction](../LeanCompletion/UAV/CopyLiftObstruction.lean)中的
`FourNode.no_budget_exact_family` 和 `FourNode.no_service_copy_lift` 证明：
前者排除所有预算可行精确路线族，后者排除所有合格服务副本提升。
本次打印的一条违规报告只针对指定 witnessFlow，不能单独承担上述全称结论。

预算 4 的 `CopyProfileReport.exact_decomposition_four` 则给出同一
fixedFlow 的可行精确分解存在性。路线数由基地出流决定，本例为 2。

辅助例子整理见[精确预算阈值与显式路线见证（#11）](https://github.com/huam54925-cpu/uav-routing-certification/issues/11)：
复用 `FixedFlowObstruction.b_visit_forces_cost_four`、需求覆盖及支持保持，
结合预算 4 可行性，组装 `ExactBudgetFeasible T ↔ 4 ≤ T`。
这是待单独形式化的推论；不能仅凭预算 3、4 两个结果排除所有中间预算。

理论主线转向[同支持图内的精确边重数障碍及条件性等价（#12）](https://github.com/huam54925-cpu/uav-routing-certification/issues/12)，
不以该小例子的阈值整理作为前置任务。

拟显式核验的路线为 `0→1→2→1→0` 与 `0→1→3→0`，
服务费用分别为 4、2。当前新模块给出的是存在性定理，尚未在该模块中
定义并核验这组具名物理路线见证。

## 原发布时的构建记录

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

## 说明同步的证据边界（2026-10-27）

用户另提供直接执行
`lake env lean .\LeanCompletion\UAV\CopyProfileReport.lean` 的终端输出：
`LeanExitCode=0`，违规文本列表一项、预算 4 列表为空、记录数为 0，
七条公理报告仅含上述三个标准公理。
这份直接 Lean 检查输出与前节原发布文档记录的 Lake 构建分开记述；
它本身不证明 `Built` 标签、约 25 秒耗时或发布前逐字节一致性。

本次仅核对远端源码并更新说明，未重新运行 Lean、读取本地原始构建日志，
也未新增本地编译文件与远端源码的哈希绑定。前节的源码一致性说明指
原发布阶段，不是本次重新完成的检查。
