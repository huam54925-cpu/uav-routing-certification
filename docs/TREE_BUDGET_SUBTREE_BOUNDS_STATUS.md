# 子树 DP：规模界、实际统计、整数精化与证书输出

日期：2026-11-14。基线：`df2d3f46bafb15b1d0943105e5b3ce3fc63912d7`。
本包新增独立模块，保留原压缩执行器、候选顺序、孩子顺序和右侧代表去重规则。
用户提供的 [中文证明参考稿](subtree_bounds_plan_zh.tex) 原样保存；它的“待形式化”及
未编译标记属于提供时的状态，当前验证状态以本文和 Lean 源码为准。未编译 LaTeX。

## 分包验收

| 包 | 本轮 Lean 交付 | 验收边界 |
| --- | --- | --- |
| A | `Invariants`：固定费用总和、非活跃费用零、支撑规模、支配退化、坐标恢复、零顶重数及零路线分类；`executable_cost_sum` 接到实际表成员 | 有符号费用；不改默认状态表示，不声称信息最小性 |
| B | `CompositionBounds`、`CandidateBounds`、`GridBounds`、`SupportBounds`、`TableBounds`、`MassBounds`：候选 Nodup 与精确长度、根孩子筛选数、整数区间、全维及按支持分层的网格界、子树组合乘积界及质量界 | 网格界需要明确的正整数缩放契约；质量推论保留正路线数与根相容性 |
| C | `StatsBounds`、`StatsGlobalBounds`、`CountsExact`：中间表及去重前 raw 列表界、全部 17 字段的界、精确节点与候选计数、总统计界 | 同一次原有理执行器的高层逻辑统计；两个最大值字段不加入总和 |
| D | `IntegerDP`、`IntegerStats`、`IntegerTrace`：独立整数执行器、有序列表精化、负预算 floor、判定与去重比较轨迹对应、全部 17 字段相等 | 对应整数算术次数沿用 `ratAdds/ratMuls` 字段名；不意味着算术位成本相等 |
| E | `WitnessDP`：显式矩阵载荷、按键保留合法代表、完整有序键表投影、原检查器接受性、失败完备性、路线语义桥接 | 输出矩阵模式证书；不输出逐顶点游走，不把 `none` 称为简短不可行性证书 |

上述模块均位于 `LeanCompletion/UAV/TreeBudgetSubtree*.lean`。
`BoundsSeed` 保留收到的七条证明尝试，已先行独立检查；后续验收覆盖整个新增包。

## 数学与实际统计接口

令 `columnCount m h = q_m(h)`，其中 `q_0(0)=1`、`q_0(h>0)=0`，正路线数时为
`choose (h+m-1) (m-1)`。`columnFactor m h = max 1 (columnCount m h)`；
`globalProduct R H m = P = ∏ x≠root, columnFactor m (H x)`。
空表不使这个包络乘积变零，因此可以控制遇到空表之前已经生成的中间列表。

`compact_cost_eq_of_le` 不需要两个状态的支持集相同：固定总和与逐坐标支配已足以推出
费用向量相等。`compact_cost_recover` 恢复任意指定坐标，非活跃坐标费用为零；
固定非空支持时，`compact_finset_card_fixed_support` 只编码 `|A|-1` 个活跃费用坐标。

`GridScale R s D w` 要求 `D>0`，且每个非根顶点满足
`(w x : ℚ) = D * linearWeight R s x`。以 `L=gridLower`、`U=gridUpper` 表示带符号区间，
每个缩放费用都是 `[L,U]` 中整数，`U-L = ∑ |w(x)|H(x)`。
正路线数 `m=k+1` 的实际返回表长度不超过 `2^(k+1)*(U+1-L).toNat^k`。
正顶重数时进一步有
`∑ r∈[1,min(m,H(v))], choose m r * (U+1-L).toNat^(r-1)`；
根孩子只需 `r=H(v)` 一项，`H(v)>m` 时其返回表为空。
根孩子筛选后候选数精确为 `choose m (H v)`，包含 `m=0` 情形；
该筛选发生在完整列枚举之后，不能用它代替生成成本。

`insideCosts_length_le`、`insideRaw_length_le`、`rootFold_length_le`、
`rootRaw_length_le`、`nodeRaw_length_le_columnProduct` 控制返回表及生成中的列表。
局部列重复折叠、根过滤前被拒绝的配对、空表、去重扫描均计入统计证明。

下面是主统计包络定理的完整类型（位于 `UAVProof.TreeBudgetSubtreeStats`，
打开 `TreeFlowExistence` 与 `TreeBudgetSubtreeExecutable` 命名空间）：

```lean
theorem checkCompactStats_bounds {N : ℕ}
    (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ)
    (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    Covers (checkCompactStats R H s m T).stats
      (globalEnvelope m ((m + 1) * (U + 1) * globalProduct R H m)
        (globalProduct R H m) (N - 1)) ∧
      (checkCompactStats R H s m T).stats.insidePairs +
        (checkCompactStats R H s m T).stats.rootPairs ≤
          (N - 1) * globalProduct R H m
```

`Covers` 对除 `eqCalls` 外的每个字段逐项比较；对相等比较用
`2*s.eqCalls ≤ envelope.eqCalls`，以保留去重的三角形比较界。
`globalEnvelope` 的该字段为 `2*(N-1)*P^2`，于是独立定理给出
`eqCalls ≤ (N-1)*P^2`，不是多一倍的界。全部字段如下。

| 字段 | 已证明的界或恒等式，`n=N-1` |
| --- | --- |
| `nodeCalls` | `n`，精确 |
| `compositionCalls` | `∑ x≠root, choose (H x+m+1) m ≤ n*(m+1)*(U+1)*P` |
| `rangeChoices` | `rangeChoices+n = compositionCalls`，精确 |
| `columnsGenerated`, `columnsAccepted`, `subsetCalls` | 各不超过 `n*P` |
| `insidePairs + rootPairs` | 不超过 `n*P`，包括根拒绝配对 |
| `rootRejected` | 不超过 `n*P` |
| `ratAdds`, `ratMuls` | 各不超过 `m*n*P` |
| `dedupInput`, `dedupOutput` | 各不超过 `2*n*P` |
| `eqCalls` | 不超过 `n*P^2` |
| `acceptCalls` | 不超过 `P` |
| `maxRawTable`, `maxDedupTable` | 各不超过 `P` |

总和定理的完整类型是：

```lean
theorem checkCompactStats_logicalWork_le {N : ℕ}
    (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ)
    (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    logicalWork (checkCompactStats R H s m T).stats ≤
      32 * N * (m + 1) * (U + 1) * globalProduct R H m ^ 2
```

`logicalWork` 仅求前 15 项累加字段之和。取 `M=∑ x≠root,H(x)`，
正路线数时有 `P≤m^M`；若另有 `m=∑ u∈children(root),H(u)`，
`canonical_logicalWork_le` 给出 `32*N*(M+1)^2*M^(2*M)`。
这些结论不是标准机器时间、算术位复杂度或实际峰值内存界。

## 整数入口与证书入口

整数入口为 `TreeBudgetSubtreeInteger.check`，预算由 `floorBudget D T` 得到。
`compute_lift_eq` 和 `rootFold_lift_eq` 证明除以 `D` 后的**完整有序列表相等**；
`check_eq` 证明判定相同，`checkMeasured_count` 证明 17 字段完全相同。
`scanComparisons_map`、`dedupComparisons_map` 保留短路次数。
`IntegerTrace` 进一步记录尾部先去重、随后短路扫描的布尔比较结果序列，证明其长度等于
原比较计数，且费用向量、局部状态、根状态三种提升均保持完整比较轨迹。
一般缩放契约是证明参数；基准程序中的 LCM 预处理经过输入检查，未作为新的通用
预处理正确性定理交付。`floor(1*(-1/2))=-1`、`floor(3*(-1/2))=-2` 有内核回归。

证书入口为 `TreeBudgetSubtreeWitness.solve`。
`compute_keys`、`roots_keys` 证明忘掉载荷后仍为原有序列表；
`compute_realizes` 证明载荷满足 `PartialValid`、根孩子 cap、支持与费用条件。
`solve_sound` 证明每个 `some c` 都使既有 `TreeBudgetCertificate.checkCertificate` 返回真；
`solve_none_iff` 等价于矩阵不可行。`solve_size` 给出 `c.size=m`，因此零路线成功返回
`some` 零行证书，而不是 `none`；原证书类型是结构，空证书不是列表字面量 `[]`。
`solve_exact_iff` 接回路线存在性时保留 `HasDegrees` 假设。
显式矩阵载荷引入的复制、构造与存储开销不属于包 C 的原执行器统计界。
本轮没有接入改变表成员语义的安全剪枝；仅证明了带符号剩余费用下界的必要条件。

## 实际验证与复现

本轮使用既有 Windows 开发环境和缓存，Lean `v4.30.0-rc2`，Mathlib 固定提交
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`。未安装 LaTeX，未升级依赖。
在已有开发树定向构建，再将经检查的源码发布到目标仓库的独立工作树。
新增模块依赖的 36 个既有 `LeanCompletion` 模块与发布基线相同
（比较忽略换行格式和末尾空白）；工具链字节相同，目标清单全部 9 个依赖版本匹配。
开发包经 `Prim` 间接依赖 Mathlib，目标独立包直接依赖 Mathlib；这不是新克隆冷构建声明。

- 原始七条种子：`lake env lean` 和独立模块构建均成功。
- 其余新增模块在本轮实际构建成功，最终定向构建退出码为 0。
  发布前清理末尾空行后，`Invariants`、`CompositionBounds`、`TableBounds`、
  `StatsGlobalBounds`、`BoundsExamples` 为 Built，其他目标为 Replayed。
  总计 8,366 jobs 大量复用缓存，不能把 jobs 当成新证明数。
- `BoundsExamples` 实际执行 483 组表／整数／统计／证书检查，并再次执行原 21 组 DP 回归。
  覆盖零路线成功与失败、零顶重数但后代非零的空表、单顶点树、负预算、带符号费用、
  有理缩放、零费用键碰撞，以及 `m=1,h=100` 的 102 次候选递归。
- 收到的 Python 有限脚本在本轮重新运行：63 组组合、2,944 组实例、8,400 张局部表通过。
  这与来稿报告的数值相同，但这里记录的是本轮重跑；有限枚举不替代一般 Lean 证明。
- `BoundsAudit` 检查 223 个新增显式命名声明，包括种子、执行函数、证明、回归与基准入口；
  只允许标准 `propext`、`Classical.choice`、`Quot.sound`，不接受 `sorryAx`。
  最终另以 `lake env lean` 直接执行该审计源，退出码为 0；并逐一检查 223 个输出的公理集合。
  原始输出留在忽略目录，审计源纳入提交。源码仍有样式与未使用参数警告。

这次发布共新增 18 个 Lean 模块；`BoundsAudit` 是其中的审计源，不是原始审计输出。

在仓库根目录执行：

```powershell
New-Item -ItemType Directory -Force verification/runs/subtree-bounds | Out-Null
lake build LeanCompletion.UAV.TreeBudgetSubtreeBoundsAudit *> verification/runs/subtree-bounds/build.log
Write-Host "BuildExitCode=$LASTEXITCODE"
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeBoundsAudit.lean *> verification/runs/subtree-bounds/audit.log
Write-Host "AuditExitCode=$LASTEXITCODE"
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeBoundsExamples.lean *> verification/runs/subtree-bounds/examples.log
Write-Host "RegressionExitCode=$LASTEXITCODE"
python -B tools/check_tree_budget_subtree_bounds.py
```

冷环境需按仓库既有方式准备固定依赖；不得把本记录理解为已经进行了冷环境复现。
全部原始日志、计时 JSON、临时驱动和构建产物仅保留于 `verification/runs/`。

## 整数执行性能观测

`IntegerBench` 使用既有六个冻结输入，分别计时原有理版、预缩放整数版和包含缩放的整数版。
预热后按最快一臂约 20ms 校准同输入的共同批量；7 轮轮换三臂顺序，每次结果写入 `IO.Ref`
并检查校验和。统计、表一致性检查及输出序列化不在计时区间；整数端到端一臂包含 LCM、
整数权重与预算构造。采用加载已编译模块的 `lake env lean --run`，不是独立原生二进制对照。
本轮小样本耗时不构成一般速度保证，逻辑操作次数相同也不保证耗时相同。

最后一轮测量在 Intel Core i7-14650HX 的上述 Windows 环境运行，未与 Lean 构建并行。
六个输入的有序表、判定、17 字段及 126 个计时样本的校验和全部通过。
下表为每次执行耗时的七轮中位数，单位微秒；“整数含缩放”列包含预处理。

| 输入 | 每批次数 | 有理版 | 整数预缩放 | 整数含缩放 | 含缩放／有理 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `zero_4` | 128 | 243.3 | 165.3 | 188.8 | 0.776 |
| `zero_8` | 128 | 396.6 | 280.5 | 294.5 | 0.742 |
| `fees_4` | 64 | 744.7 | 620.0 | 640.7 | 0.860 |
| `fees_8` | 8 | 4885.8 | 4556.6 | 4677.4 | 0.957 |
| `rational_short` | 64 | 555.3 | 437.7 | 465.5 | 0.838 |
| `rational_long` | 64 | 604.0 | 435.8 | 443.0 | 0.733 |

这六个输入中，包含缩放的整数版中位数为有理版的约 0.73–0.96 倍。
`fees_8` 波动明显：有理版七轮范围约 4476–8529 微秒、含缩放整数版约 4085–6798 微秒。
不能把其中较小的中位数差异当成稳定加速结论。未据此修改默认执行入口。

复现时先构建 `LeanCompletion.UAV.TreeBudgetSubtreeIntegerBench`；在忽略目录建立驱动：

```lean
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerBench
def main := UAVProof.TreeBudgetSubtreeIntegerBench.main
```

然后用 `lake env lean --run <驱动路径> 7 20`，将输出重定向到忽略目录。
