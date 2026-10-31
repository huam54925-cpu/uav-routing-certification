# Next-only 与有界完整证书（2026-10-31）

Issue #13 的 prev 冗余消除和规范数值范围已完成。现有精确可行分解、
局部配对证书、next-only 证书及有界 next-only 证书构成存在性等价链。
固定路线数版本始终保留基地出流条件。

## 接口与假设

新模块均位于 `LeanCompletion/UAV/`：

| 模块 | 结论 |
| --- | --- |
| `LocalVisitPairingNext.lean` | 任务目标的任务前驱唯一即可恢复 prev；任务字段及 pairedFlow 逐边保持 |
| `LocalVisitPairingNextCertificate.lean` | 费用势和秩转换，HasNextCertificate 与 HasLocalCertificate 纯表示等价 |
| `LocalVisitPairingBounds.lean` | 精确覆盖路线总长度为 N；规范 routeRank 和后缀 routePotential 的范围 |
| `LocalVisitPairingBoundedCertificate.lean` | 同一组 q、rank、cert 满足全部证书条件与数值界；接回最终可行性 iff |

N = Σ(v ≠ depot) required(v)，重复访问按位置计数，不计基地需求。
有界证书要求 rank(none)=0、任务秩在 1…N、全部副本势在 0…T。
基地势为零来自同一份 NextBudgetPotential 的 depot_zero 字段。

纯 next/local 表示等价和遗忘范围界不需要费用符号、正预算或物理无自环假设。
从精确可行路线构造有界证书只需服务费用非负、0 ≤ T，不增加 hloop。
该构造明确使用 pairingOfRoutes、routeRank、规范后缀势及保值转换。

最终三个 iff 沿用物理流无自环、服务费用非负、T > 0：

```text
HasBoundedNextCertificate o d x s T ↔ HasNextCertificate o d x s T

ExactFeasible o x d (outFlow univ x o) s T
  ↔ HasBoundedNextCertificate o d x s T

ExactFeasible o x d m s T
  ↔ m = outFlow univ x o ∧ HasBoundedNextCertificate o d x s T
```

不要求 required(depot)=0、m>0、非空任务集、路线互异或禁止非相邻重复访问。
基地可接受多个返回；next 不要求全局单射。单独的 next 前驱唯一性允许环，
零费用环也能满足预算条件，但严格递减秩排除它。
零需求、零流实例对任意服务函数有有界证书，当且仅当 0 ≤ T。
这没有把一般可行性 iff 推广到 T=0。

## 验证范围

以下为本会话先前实际执行、随后经用户源码和日志审阅的本地构建，
不是本次发布时重新执行的检查：

| 模块后缀 | 新模块状态 | 退出码 | 本模块选定公理报告 |
| --- | --- | --- | --- |
| Next | Built（24s） | 0 | 18 |
| NextCertificate | Built（22s） | 0 | 16 |
| Bounds | Built（22s） | 0 | 14 |
| BoundedCertificate | Built（29s） | 0 | 9 |

四个新模块均无警告；57 项报告仅含 propext、Classical.choice、Quot.sound
或其子集，无 sorryAx。已有依赖的缓存重放警告不是新模块警告。
源码无 sorry/admit 或新增公理。日志保留在原工作区 ignored verification/runs/，不上传。
构建使用原本地工作区缓存、Lean 4.30.0-rc2 及现有锁定依赖。
本次发布只复制四个已验证模块并更新说明，不修改既有 Lean 源码或依赖版本。
目标独立工程的干净重建仍未完成。

复现入口：`lake build LeanCompletion.UAV.LocalVisitPairingBoundedCertificate`。

## 规范势的公共分母与整数网格（后续提交，2026-10-31）

新增 `LocalVisitPairingPotentialGrid.lean`。对有限有理服务费用，选取全部
输入服务分母的乘积 D，证明 D>0，且任意列表、后缀和与规范 routePotential
经 D 缩放后均为整数。重复访问按次数累加；整数性不要求费用非负或预算条件。

结合非负服务、0 ≤ T 和逐路线预算，先证明整数见证 z 非负且
z ≤ floor(D*T)，再转为自然数 k。最终由同一个正 D 对全部副本满足：

```text
∀ c, ∃ k : ℕ, (k : ℚ) = (D : ℚ) * routePotential ... c
  ∧ (k : ℤ) ≤ Int.floor ((D : ℚ) * T)
```

D 只依赖服务费用，不包含 T 的分母；D*T 无须为整数。基地、空路线族、
零需求均保留，无 Nonempty 假设。本结论针对指定规范势，不声称任意费用势
均位于同一个网格。

前一轮实际本地构建为 **Built（23s）**、`LeanExitCode=0`，新模块无警告；
9 项公理报告仅含标准公理或子集，无 sorryAx，源码无占位证明或新增公理。
本次提交核对并复制同一源码，没有重新执行 Lean；既有源码及依赖版本不变。
原始日志留在 ignored `verification/runs/2026-10-31-potential-grid/`，不上传。
目标独立工程的干净重建仍未完成。

复现入口：`lake build LeanCompletion.UAV.LocalVisitPairingPotentialGrid`。

## 后续边界

证书存在性允许从可行路线重新构造另一份 next，不保证保持输入 next。
有理势落在 [0,T] 并不意味着编码位数有界。规范后缀和的公共分母与整数网格
已由上述后续提交完成，但尚未定义最终有限编码证书，尚未证明
位复杂度、信息最小性或多项式搜索算法。
复杂度必须区分总访问数 N 与原始输入位数；二进制需求下展开 N 个副本
本身可能很大。仅计服务费用的研究结论不改变冻结 Case1 应用基线。
