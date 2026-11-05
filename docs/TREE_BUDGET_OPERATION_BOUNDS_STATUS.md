# Issue #20：执行次数证明进度

日期：2026-11-05（Asia/Tokyo）。**状态界参数小包已通过本地定向构建和公理审计，完成后在此暂停。** 在既有 A、B 包之上，本轮新增 `S(H) ≤ 2^M`、`S(H) ≤ (U+1)^t` 及边界回归。各证明阶段完成时仅作本地编辑，未提交或推送；本次按用户要求将成果整理为研究分支提交，不修改远端 Issue。下文保留 A1、A2、B 各自的历史验证记录，不将其计为参数小包的新运行；Issue #20 继续保持开放。

## A1 已完成：缓存增长与展开次数

新增源码：

- [TreeBudgetSearchStatsBounds.lean](../LeanCompletion/UAV/TreeBudgetSearchStatsBounds.lean)
- [TreeBudgetSearchStatsBoundsExamples.lean](../LeanCompletion/UAV/TreeBudgetSearchStatsBoundsExamples.lean)

沿用现有 `memoStat`、`scanStat`、`Counts` 和关联表缓存，没有修改搜索实现。记 `K₀` 为输入缓存的列表长度，`K` 为输出缓存的列表长度，`E` 为该次调用记录的 `expansions`。

| 接口 | 结论及适用范围 |
| --- | --- |
| `insert_eq_cons_of_lookup_none`、`insert_length_of_lookup_none` | 查询为外层 `none` 时，插入等于直接前置新条目，长度恰好增加一；重复的其他键保留 |
| `memoRowsWith_lookup_above` | `k < q.1` 时，求解层数 `k` 的状态保持键 `q` 的查询结果，包括缺失结果 |
| `scan_parent_lookup_none` | 子搜索结束后父键仍然缺失；候选后缀 `tail` 可独立于子求解器的完整候选表 `ps` |
| `memoStat_lookup_above`、`scanStat_parent_lookup_none` | 用现有擦除定理把上述性质连接到统计执行器 |
| `scanStat_cache_length` | 缓存增长可沿候选扫描组合，涵盖跳过、失败后继续和成功提前停止 |
| `memoStat_cache_length` | **`K = K₀ + E`**，适用于任意候选列表及任意原始缓存 |
| `memoStat_cache_length_mono`、`memoStat_empty_cache_length` | 输出长度不小于输入；空缓存时 **`K = E`** |
| `initial_expansions_le` | 正式树预算初始入口的 **`E ≤ stateBound R H`** |

通用增长定理不要求 `CacheValid`、`KeysNodup` 或候选合法性。`K₀` 包含重复条目；`some none` 是已缓存失败的命中，只有外层 `none` 才是缺失。高层保持条件为严格不等式，不能弱化为 `k ≤ q.1`。

树入口推论针对

```lean
memoRowsStat R H s T (rootCount R H) H emptyCache
```

证明链为：新增长等式给出 `E = K`，`memoRowsStat_erase` 把统计缓存转换为原执行器缓存，已有 `initial_cache_length_le` 给出

```text
K ≤ S(H) = ∏ (v ≠ R.root), (H(v) + 1).
```

可达性与键无重复性由已有空缓存入口定理负责。不能把这个 `E ≤ S(H)` 直接推广到任意候选表或任意热缓存。

## A1 历史验证记录

以下为 A1 阶段的历史结果，不能替代 A2 修改后的构建和审计。2026-11-05 在本地工程根目录实际执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSearchStatsBounds LeanCompletion.UAV.TreeBudgetSearchStatsBoundsExamples
```

最终退出码为 0，Lake 报告 `Build completed successfully (8345 jobs)`。两个新模块均在 A1 阶段编译通过；最终命令复用了 A1 上一轮构建成功且源码未变的主证明模块，重新编译了回归模块。12 个主模块定理及 10 个回归定理的公理审计只包含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；当时新增源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`，两个新模块无 linter 警告。既有依赖重放的警告不属于 A1 新增。

验证使用既有 Lean 4.30.0-rc2、锁定依赖及构建缓存，不是全新环境重建或远端 CI。开发期间失败的构建和取消的重复直接检查均不计为 PASS。原始输出仅保存在 ignored `verification/runs/issue20-growth-20261105/`，成功构建记录为 `build-verified.log`，审计摘要为 `final-checks.txt`。

A1 开始时的 96 个既有 UAV Lean 文件及 6 个受保护文件（根导入、冻结目标源码、工具链、Lake 配置、依赖锁、验证目标配置）经 SHA-256 比对均未改变。A1 最终仅新增本说明和上述两个 Lean 模块；没有暂存、提交或推送，既有未跟踪文件保持原状。

当时的回归覆盖零步成功/失败、正层数空候选、守卫拒绝、重复其他键保留、当前键的重复冲突答案与失败命中、成功空答案命中、重复零候选复用失败、子调用失败后继续并成功提前停止。具体计数用于验证执行路径，不替代一般计数定理。

## A2：一般执行次数关系与正式入口

本阶段仅扩展同一主模块、回归模块及本说明，沿用现有执行器和计数口径。记 `P = ps.length`，`I = insertionScans`，`Q = candidates`，`C = calls`，`J = hits`；`K₀`、`K`、`E` 与 A1 相同。

已证明的通用结果适用于任意候选表和原始缓存，包括重复候选、重复缓存键及语义无效的缓存答案；不要求 `CacheValid`、`KeysNodup` 或候选合法、完整：

```text
K = K₀ + E                         （复用 A1）
I + triangle K₀ = triangle K
I = K₀*E + triangle E
  = K₀*E + E*(E-1)/2
Q ≤ P*E
C ≤ 1+Q
C = J+E
```

`triangle 0 = 0`、`triangle (t+1) = triangle t + t`。联合不变量 `Accounting` 只包含势函数等式、候选界、调用界和调用分解这四个字段；缓存增长继续复用 A1 的独立定理。

扫描层使用 `Accounting P tail.length 0`，即 `Q ≤ |tail| + P*E`、`C ≤ Q`；状态层使用 `Accounting P 0 1`。`tail` 与子求解器复用的完整列表 `ps` 独立，`P` 始终对应完整列表长度。失败后的缓存传递使中间势函数相消；成功时提前停止；父状态新增一次展开吸收完整候选扫描的额外预算。

| 阶段与接口 | 结论 | 当前验证状态 |
| --- | --- | --- |
| A2.1：`triangle_zero`、`triangle_succ`、`triangle_add`、`triangle_mono` | 三角数递归、加法与单调性 | 定向构建已通过 |
| A2.1：`scanStat_accounting` | 任意候选后缀的四字段联合归纳 | 定向构建已通过 |
| A2.2：`memoStat_accounting`、`scanStat_memoStat_accounting` | 主执行器与实际子求解器扫描的联合统计关系 | 构建与审计通过 |
| A2.2：`memoStat_insertionScans_potential`、`memoStat_insertionScans_eq` | 势函数等式及 `I = K₀*E + triangle E` | 构建与审计通过 |
| A2.2：`memoStat_candidates_le`、`memoStat_calls_le`、`memoStat_calls_eq_hits_add_expansions` | `Q ≤ P*E`、`C ≤ 1+Q`、`C = J+E` | 构建与审计通过 |
| A2.3：`two_mul_triangle`、`triangle_closed` | `2*triangle E = E*(E-1)` 与自然数除二闭式 | 构建与审计通过 |
| A2.3：`memoStat_insertionScans_closed` | `I = K₀*E + E*(E-1)/2` | 构建与审计通过 |
| A2.3：`initial_candidates_le`、`initial_calls_le` | 正式初始入口的 `Q ≤ P*S(H)`、`C ≤ 1+P*S(H)` | 构建与审计通过 |
| A2.3：`initial_insertionScans_le`、`initial_insertionScans_le_closed` | 正式初始入口的 `I ≤ triangle S(H)` 及 `I ≤ S(H)*(S(H)-1)/2` | 构建与审计通过 |

最后四项树入口界专用于 A1 所列的正式空缓存调用，且此处 `P` 为 `TreeBudgetFiniteSearch.candidates R H s T` 的列表长度。它们复用 `initial_expansions_le`，先证明势函数形式的插入扫描界，再转换闭式；递归统计证明不处理自然数除法。

回归模块补充热命中无展开、插入扫描和候选检查，重复旧键使 `K₀*E` 项不可省略，守卫拒绝时 `C < 1+Q`，以及失败后成功时插入扫描和提前停止的具体计数。四项新增回归均使用现有实例，并以 `decide +kernel` 完成验证；原来的十项回归声明与证明未改。

## A2 历史验证与完成状态

A2.1 与 A2.2 分别通过定向构建，成功记录为 `a21-verified.log`、`a22-verified-2.log`。A2.3 与 A2.4 最终在工程根目录执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetSearchStatsBounds LeanCompletion.UAV.TreeBudgetSearchStatsBoundsExamples
```

该命令退出码 0，报告 `Build completed successfully (8345 jobs)`，两个目标模块均在这次命令中重新编译成功。成功记录为 ignored `verification/runs/issue20-accounting-20261105/a23-a24-build.log`，审计摘要为同目录下的 `final-checks.txt`。开发期间失败的构建不计为 PASS，即使文件名包含 `verified` 也以实际退出码为准。

本轮实际增加 **19 个主定理、4 个回归定理**；最终主模块共 31 个定理，回归模块共 14 个定理。45 个定理均有 `#print axioms` 输出，无遗漏；公理依赖集合不超出 `propext`、`Classical.choice`、`Quot.sound`，其中两个三角数递推定理不依赖任何公理。无 `sorryAx`，源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`；两个目标模块无 linter 警告。

本轮复用既有 Lean 4.30.0-rc2、锁定依赖及构建缓存，没有独立环境重建、性能实验或远端 CI。A1 的 12 项主定理证明块与原有十项回归经文本比对保持不变；其余 96 个 UAV 源文件和 6 个受保护文件经 SHA-256 比对均未改变。范围仅为本说明及两个已有本地证明模块；没有暂存、提交、推送或处理无关未跟踪文件。原始输出及核验快照均仅留在 ignored `verification/runs/issue20-accounting-20261105/`。

**A2.1–A2.4 均完成，A 包整体通过本地验证，并在 A 阶段结束时暂停。** Issue #20 继续开放；A2 阶段没有实施 B 包。

## A 阶段完成时的结论边界（历史）

A 阶段的结果只约束现有计数器的逻辑操作次数，不覆盖候选生成、完整键比较内部工作、算术位成本或见证存储，也不等于程序运行时间界。A 阶段结束时尚未证明 `P ≤ S(H)`，当时不能把 `Q ≤ P*S(H)` 改写为已证明的 `Q ≤ S(H)^2`。后续 B 阶段专门补充这一证明链，状态单独记录如下。

## B：候选列表长度与关联表比较次数

本阶段新增独立模块，复用 A 包和现有执行器，不改写枚举、查询、插入或搜索流程：

- [TreeBudgetCandidateCount.lean](../LeanCompletion/UAV/TreeBudgetCandidateCount.lean)：候选列表长度。
- [TreeBudgetSearchCostBounds.lean](../LeanCompletion/UAV/TreeBudgetSearchCostBounds.lean)：查表比较次数与正式入口推论。
- [TreeBudgetSearchCostBoundsExamples.lean](../LeanCompletion/UAV/TreeBudgetSearchCostBoundsExamples.lean)：本阶段的七项边界回归。

继续使用 `P = ps.length`、`K₀`、`K`、`E`、`Q`、`C`，新增 `L = lookupComparisons`。这里的一次比较表示访问一个关联表条目；完整键内部包含多个坐标，内部比较工作不由 `L` 逐项计数。

### B1：直接计算可执行列表长度

`boundedVectors_length` 按枚举定义递归计算 `flatMap` 和 `map` 的列表长度，证明

```text
|boundedVectors n b| = ∏ (i : Fin n), (b(i) + 1).
```

`boundedVectors_bound_length` 将 `b = bound R H` 代入；根坐标上界为零，因此该坐标只贡献一个取值，得到实际枚举列表长度恰为 `S(H)`。`candidates_length_le_stateBound` 再使用过滤不增加长度，得到

```text
P = |TreeBudgetFiniteSearch.candidates R H s T| ≤ S(H).
```

这条证明计算列表位置数，不要求候选 `Nodup`，也没有用集合有限性替代列表长度证明。它不分析枚举每个向量的费用、合法性判定的费用或生成整个候选列表的时间。

### B2：查询比较次数沿实际执行组合

已证明的通用结果覆盖任意候选列表及原始缓存，包括重复键；没有额外的 `CacheValid`、`KeysNodup` 或候选合法性假设：

```text
(lookupStat cs q).2 ≤ cs.length
L ≤ C*K = C*(K₀+E)
```

每次查表至多访问当时缓存的全部条目。A1 的增长定理保证扫描期间的缓存长度不超过最终长度；扫描归纳处理失败后继续、成功提前停止和守卫拒绝，主归纳再计入根查询。空缓存时得到

```text
L ≤ C*E ≤ E + P*E².
```

对 A1 所列的正式树预算空缓存入口，结合 A 的 `E ≤ S(H)`、`Q ≤ P*S(H)`、`C ≤ 1+P*S(H)` 和 B1 的 `P ≤ S(H)`，已证明

```text
Q ≤ S(H)²
C ≤ 1+S(H)²
L ≤ C*S(H)
L ≤ S(H) + P*S(H)² ≤ S(H) + S(H)³.
```

| 接口 | 结论 | B 阶段验证状态 |
| --- | --- | --- |
| `boundedVectors_length`、`boundedVectors_bound_length` | 原始枚举列表的精确长度 | B1 定向构建与公理审计通过 |
| `candidates_length_le_stateBound` | `P ≤ S(H)` | B1 定向构建与公理审计通过 |
| `lookupStat_comparisons_le_length` | 单次查询比较数不超过缓存长度 | 构建与公理审计通过 |
| `scanStat_lookupComparisons_le_cache_length`、`memoStat_lookupComparisons_le_cache_length` | 扫描层和状态层的 `L ≤ C*K` | 构建与公理审计通过 |
| `memoStat_lookupComparisons_le` | 一般原始缓存的 `L ≤ C*(K₀+E)` | 构建与公理审计通过 |
| `memoStat_empty_lookupComparisons_le`、`memoStat_empty_lookupComparisons_le_polynomial` | 空缓存的 `L ≤ C*E ≤ E+P*E²` | 构建与公理审计通过 |
| `initial_candidates_le_stateBound_sq`、`initial_calls_le_stateBound_sq` | 正式入口的 `Q ≤ S(H)²`、`C ≤ 1+S(H)²` | 构建与公理审计通过 |
| `initial_lookupComparisons_le_calls_mul_stateBound`、`initial_lookupComparisons_le`、`initial_lookupComparisons_le_stateBound_cube` | 正式入口的三个查表界 | 构建与公理审计通过 |

### B 历史验证记录

B1 已在工程根目录实际执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetCandidateCount
```

退出码 0，报告 `Build completed successfully (8343 jobs)`；新增候选计数模块在本次命令中编译成功。三个定理均有 `#print axioms` 输出，依赖仅包含 `propext`、`Classical.choice`、`Quot.sound`，新增模块无 linter 警告。原始日志为 ignored `verification/runs/issue20-candidate-lookup-20261105/b1-build-01.log`。该运行复用既有 Lean 4.30.0-rc2、锁定依赖和构建缓存，不是全新环境重建。

最终联合命令：

```powershell
lake build LeanCompletion.UAV.TreeBudgetCandidateCount LeanCompletion.UAV.TreeBudgetSearchCostBounds LeanCompletion.UAV.TreeBudgetSearchCostBoundsExamples
```

退出码 0，报告 `Build completed successfully (8348 jobs)`。该命令复用了本轮已成功且源码未变的 B1 模块缓存，重新编译了查表界模块和回归模块；成功记录为 `verification/runs/issue20-candidate-lookup-20261105/b-final-build.log`。

本轮新增 **14 个主定理（B1 三个、B2 十一个）、7 个回归定理**。这 21 个定理全部有公理审计输出，无遗漏；依赖集合不超出 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。新源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`，最终三个模块无 linter 警告。首次 B2 构建的三处 linter 提示已修正，以最终运行记录为准。

七项回归以 `decide +kernel` 验证零维枚举、非均匀及含零坐标的枚举、空缓存查询、重复旧条目的全部扫描、首条失败答案命中、晚位置热命中，以及已学习状态命中和回溯未命中的计数。晚位置热命中满足 `K₀=2,C=1,E=0,L=2`：它达到一般界，并严格排除把 `L ≤ C*E` 用于任意热缓存。

本轮开始时的 **98 个既有 UAV 源文件**（含 A 包及其回归）和 **6 个受保护文件**经 SHA-256 比对均未改变。工作范围为三个新增 Lean 模块及本说明；没有修改执行器、重建独立环境、重复性能实验、暂存、提交、推送或修改远端 Issue。既有依赖与构建缓存被复用，不是全新环境重建或远端 CI。

核验摘要为同目录的 `final-checks.txt`。B 阶段的原始输出与核验快照仅保存于 ignored `verification/runs/issue20-candidate-lookup-20261105/`。**B 包全部通过本地验证，并在 B 阶段结束时暂停；Issue #20 继续保持开放。**

## 状态界参数小包：总量、正坐标数与最大值

本阶段新增两个独立模块，沿用原来的 `stateBound`，不修改 A、B 的证明模块或可执行搜索：

- [TreeBudgetStateParameters.lean](../LeanCompletion/UAV/TreeBudgetStateParameters.lean)：参数定义、有限乘积辅助引理与两个状态界。
- [TreeBudgetStateParametersExamples.lean](../LeanCompletion/UAV/TreeBudgetStateParametersExamples.lean)：五项边界回归。

参数均只读取非基地坐标；基地的 `H(R.root)` 不参与任何参数：

| 定义 | 数学含义 |
| --- | --- |
| `nonrootVertices R` | 非基地顶点集合 `{v : v ≠ R.root}` |
| `totalMultiplicity R H` | `M = ∑ (v ≠ R.root), H(v)`，非基地父边重数总量 |
| `positiveCoordinates R H` | 非基地且 `H(v)>0` 的坐标集合 |
| `positiveCount R H` | `t`，上述正坐标集合的元素个数 |
| `maxMultiplicity R H` | `U`，非基地坐标上 `H` 的有限上确界，空集时为零 |

`maxMultiplicity` 的定义在全部非基地坐标上取 `Finset.sup`，包括零坐标；这与正坐标上的最大值一致，避免单独假设存在正坐标。`S(H)` 仍为非基地坐标上 `H(v)+1` 的乘积。

本轮已证明的两个主要结果为：

```text
S(H) ≤ 2 ^ totalMultiplicity R H                 = 2^M
S(H) ≤ (maxMultiplicity R H + 1) ^ positiveCount R H = (U+1)^t.
```

第一条证明链逐坐标使用 `h+1 ≤ 2^h`，再把有限乘积中的指数相加。第二条先删除 `H(v)=0` 对应的单位因子，只留下 `t` 个正坐标，再将每个因子上界为 `U+1`。这些命题不引入费用、预算、候选合法性或缓存不变量假设；空非基地集合和零正坐标无需额外前提。

| 接口 | 结论 | 本阶段验证状态 |
| --- | --- | --- |
| `add_one_le_two_pow` | 自然数单因子界 `h+1 ≤ 2^h` | 构建与公理审计通过 |
| `prod_add_one_le_two_pow_sum` | 任意有限集合上的乘积与总量界，含空集合 | 构建与公理审计通过 |
| `multiplicity_le_maxMultiplicity` | 任意非基地坐标满足 `H(v) ≤ U` | 构建与公理审计通过 |
| `stateBound_eq_prod_positiveCoordinates` | 移除零坐标不改变状态乘积 | 构建与公理审计通过 |
| `stateBound_le_two_pow_totalMultiplicity` | `S(H) ≤ 2^M` | 构建与公理审计通过 |
| `stateBound_le_maxMultiplicity_pow_positiveCount` | `S(H) ≤ (U+1)^t` | 构建与公理审计通过 |

五项回归复用已有单基地树和四顶点路径，基地输入均故意设置为较大的数值：

| 回归 | 检查内容 | 本阶段验证状态 |
| --- | --- | --- |
| `zero_nonroot_ignores_large_root` | 非基地全零时 `S=1,M=t=U=0` | 构建与公理审计通过 |
| `root_only_has_empty_parameters` | 只有基地时，空非基地集合的乘积为一，上确界与其余参数为零 | 构建与公理审计通过 |
| `unit_values_attain_both_bounds` | 三个非基地值均为一时，两条界均取等号 | 构建与公理审计通过 |
| `sparse_nonuniform_parameters` | 非基地值为 `2,0,3` 时 `S=12,M=5,t=2,U=3`，两条上界分别为 `32` 和 `16` | 构建与公理审计通过 |
| `single_positive_attains_max_bound` | 只有一个正坐标时最大值界取等号，零坐标不增加 `t` | 构建与公理审计通过 |

### 参数小包本轮验证记录

本轮在工程根目录实际执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetStateParameters LeanCompletion.UAV.TreeBudgetStateParametersExamples
```

退出码 0，报告 `Build completed successfully (8353 jobs)`；两个新增目标模块均在该次命令中实际编译成功，未复用这两个目标的编译结果。成功记录为 ignored `verification/runs/issue20-state-parameters-20261105/build-01.log`。

本轮新增 **6 个主定理、5 个回归定理**，11 个定理全部有 `#print axioms` 输出，无遗漏；公理依赖集合不超出 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。新增源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`，两个新模块无 linter 警告。五项回归均通过 `decide +kernel` 验证。

本轮开始时的 **101 个既有 UAV 源文件**及 **6 个受保护文件**经 SHA-256 比对均未改变。工作范围为两个新增 Lean 模块及本说明；没有修改既有 A、B 证明或执行器，没有暂存、提交、推送或修改远端 Issue。构建使用既有 Lean 4.30.0-rc2、锁定依赖及依赖构建缓存，不是全新环境重建或远端 CI。

核验摘要为同目录的 `final-checks.txt`。本轮原始输出与核验快照仅保存于 ignored `verification/runs/issue20-state-parameters-20261105/`。**本参数小包通过本地验证，在此暂停；表示与位成本留到下一部分，Issue #20 继续保持开放。**

## 当前结论边界与下一小包计划

A、B 包得到的是所定义计数器的操作次数界；本参数小包进一步约束同一个有限状态数 `S(H)`。候选生成、完整键比较的坐标和位成本、自然数及有理数运算、见证存储与实际运行时间仍未包括在内；不能将 `L ≤ S(H)+S(H)³` 或本阶段的指数表达式直接表述为已证明的程序时间复杂度。

下一小包计划进入表示与位成本的计数接口：

1. 明确完整缓存键 `(k,r)` 的表示与比较计数，区分访问一个关联表条目、比较多少坐标和处理多少位。
2. 固定编码方式、数值大小前提与计数接口后，再研究如何把键比较成本连接到 B 包的 `lookupComparisons` 界。
3. 候选生成与 `RowValid` 检查、自然数及有理数运算、见证列表规模分别留作后续小包，避免把尚未计数的工作混入现有运行次数结论。

这些表示与位成本目标尚未形式化。本阶段不宣称完整输入位复杂度、FPT/XP 分类或困难性结论；模型归约仍属于后续 D 包。

## 发布核对（2026-11-05）

本次发布包含上述七个 Lean 模块与本说明，基于研究分支的 `028adf57`。七个源码文件与各阶段最终验证快照逐字节一致；本说明仅补充发布状态。目标仓库的 Lean 工具链、Mathlib 及其锁定依赖版本、Lean 编译选项与验证环境一致；相关 LeanCompletion 导入闭包在忽略换行格式及文件末尾空白后相同。目标仓库保留原有直接依赖 Mathlib 的配置，本地验证工程还包含这些模块未使用的 Prim 等依赖。

本次发布核对没有重新执行 Lake 构建或远端 CI，以上 PASS 均来自各阶段明确记录的实际本地运行。原始日志、审计输出和快照不纳入提交。
