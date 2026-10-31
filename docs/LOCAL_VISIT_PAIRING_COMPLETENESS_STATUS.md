# 局部访问配对证书：完备性与精确可行性等价

状态同步：2026-10-31；本地验证与源码发布：2026-10-30。

- 研究分支：`research/structural-service-cuts-20261023`
- 证明提交：[46be65c](https://github.com/huam54925-cpu/uav-routing-certification/commit/46be65c20534bfdd537c270ecdb596bf43d9120c)
- 固定源码：[LocalVisitPairingCompleteness.lean](https://github.com/huam54925-cpu/uav-routing-certification/blob/46be65c20534bfdd537c270ecdb596bf43d9120c/LeanCompletion/UAV/LocalVisitPairingCompleteness.lean)
- 该证明提交仅新增上述 600 行文件；本次状态同步仅修改 Markdown 文档和 Issues。
- 关联：[成果总览 #12](https://github.com/huam54925-cpu/uav-routing-certification/issues/12)、[充要刻画与后续 #13](https://github.com/huam54925-cpu/uav-routing-certification/issues/13)。

## 已完成的数学结论

固定有限物理节点集 V、基地 o、自然数需求 d、自然数有向边流 x、
有理服务费用 s 和预算 T。最终两个 iff 假设：

- x(v,v)=0；
- 对所有 v，s(v)≥0；
- T>0。

路线非空、途中不回基地、相邻物理节点不同；允许非相邻重复访问，
服务按访问次数收费。只计服务费用，不包括飞行费用和时间窗。
d(o) 被覆盖语义忽略；零需求任务不产生访问副本。

`HasLocalCertificate o d x s T` 表示存在访问副本上的局部配对 p、
自然数秩 rank，以及以 `Nonempty` 包装的 `BudgetPotential`，满足：

1. 前驱／后继在任务副本处相互一致，基地不配对到达与出发；
2. 每个任务副本沿后继的秩严格下降；
3. `pairedFlow p` 精确投影到指定物理流 x；
4. 费用势在基地为零，满足局部费用递推不等式和出发位置预算。

已证明：

```text
exactFeasible_iff_hasLocalCertificate:
  ExactFeasible o x d (outFlow univ x o) s T
    ↔ HasLocalCertificate o d x s T

exactFeasible_iff_count_and_hasLocalCertificate:
  ExactFeasible o x d m s T
    ↔ m = outFlow univ x o ∧ HasLocalCertificate o d x s T
```

固定 m 的路线数条件不可省略。结论是证书存在性与精确可行性的等价，
不要求证书唯一，也没有声明每个任意配对均可行。

## 已完成的证明链与边界

| 环节 | 主要声明 |
| --- | --- |
| 从规范副本恢复唯一访问位置 | copyPosition、existsUnique_positionCopy |
| 相邻位置构造配对 | pairingOfRoutes |
| 恢复同一个提升流 | pairedFlow_pairingOfRoutes_eq_liftedFlow |
| 精确物理投影 | pairingOfRoutes_projects_exact |
| 剩余边数给出递减秩 | routeRank、routeRank_last、routeRank_descending |
| 后缀服务和给出费用势 | routePotential_step、routePotential_start、routePotential_isBudgetPotential |
| 任意预算可行精确路线族构造证书 | exists_local_certificate_of_exact_family |
| 两个方向的接口 | hasLocalCertificate_of_exactFeasible、exactFeasible_of_hasLocalCertificate |
| 空族与零实例 | zero_exactFeasible、zero_hasLocalCertificate |

逆向构造沿用访问位置双射；同一物理点的不同访问位置、不同编号的相同路线
不会合并副本。流等式逐条恢复边重数，超出仅保持支持或度数的结论。
秩取路线长度减当前位置；费用势为包含当前访问的后缀服务和。
零费用可使势保持不变，排环仍由严格递减的自然数秩负责。

源码没有加入正路线数、正需求、路线互异或禁止非相邻重复访问的假设。
`pairingOfRoutes_singleton` 覆盖单次访问；零实例两个通用定理甚至不要求
非负费用或正预算。最终 iff 仍沿用上面列出的充分性假设。
逆向构造本身只需精确覆盖、精确流和逐路线预算。

## 验证证据及源码身份

用户提供的 `verification-summary.txt` 与 `final-iff-types.txt`
记录了 2026-10-30 在既有 Windows 工程中的实际检查：

- Lean：`leanprover/lean4:v4.30.0-rc2`；
- mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`；
- 使用 Lake 生成的 setup 做单文件源码检查，退出码 0；
- 执行下述局部构建，新模块 **Built（25s）**，16 项既有 LeanCompletion
  依赖条目 **Replayed**，退出码 0；
- 22 项选定声明的公理报告仅含 `propext`、`Classical.choice`、
  `Quot.sound` 或其子集，无 `sorryAx`；记录称新模块无警告。
  22 是打印检查项数量，不是文件全部声明数；8330 jobs 不是新编译模块数。

```powershell
lake build LeanCompletion.UAV.LocalVisitPairingCompleteness
$buildCode = $LASTEXITCODE
Write-Host "LeanExitCode=$buildCode"
```

固定远端源码 UTF-8 内容的 SHA256 为：

```text
6217F8AFA6461186355D5F0859472689E456035FB60E14059D3B6984F09C6123
```

本会话已计算远端源码哈希，确认与用户验证记录中的源文件哈希一致，
并核对证书定义、两个 iff 的类型、22 条公理打印命令及证明占位符情况。
附件是整理后的验证记录和类型输出，不是全部原始构建日志；
本次远端审阅与文档同步没有重新执行 Lean。

按用户发布记录：九项目标依赖版本锁定均一致；17 个本地导入模块中，
15 个与目标源码一致，CopyProfileRealizability 和 FixedFlowObstruction
两模块仅历史验证头部注释不同，证明代码相同。该依赖比较按记录引用，
本次没有独立重做两个工作区的比较。独立目标工程尚未完成干净重建。

原始输出与审计材料仍保留本地 ignored `verification/runs/issue13-batch3/`；
不随本次文档更新上传。10 月 29 日四模块的 58 项缓存报告是另一阶段的证据，
详见 [历史发布记录](STRUCTURAL_DECOMPOSITION_PUBLICATION_STATUS.md)，
不得与本次 22 项检查混为一次新执行。

## 下一步与未完成事项

1. 优先证明仅记录 next 的表示与现有 Pairing 等价。
   必须限制每个任务目标至多一个任务前驱；基地可接受多个前驱。
   无任务前驱的副本成为出发位置。next 在基地的值不参与任务后继语义。
2. 证明存在规范证书：基地秩 0，任务秩在 1…N，非负费用下后缀势在 0…T，
   其中 N 为非基地总访问需求。这些范围尚未封装为新定理。
3. 补同支持严格分离实例的无证书推论及含重复访问的显式证书例，
   作为接口应用；不将尚未实现的例子标为完成。
4. 再考虑可执行检查、编码位数和搜索。next-only、最小信息表示、
   高效搜索与多项式复杂度均未证明。

合法副本流本来就稀疏；不能仅比较稠密矩阵大小便宣称信息论压缩。
N 是展开后的访问数，需求二进制编码时 O(N) 不等于对紧凑输入的多项式界。
本阶段成果定位为明确模型中的表示等价和形式化证书设计，不宣称文献新颖性。
