# 自动整数见证执行器资源界（G0–G4）

基线为 F0–F4 的 `58d54620aa8634238409bf6c6e98a91db40c670a`。本包给实际执行一次的整数矩阵见证搜索加入资源计数，并证明结果擦除、全部 17 字段统计迁移、数值大小、矩阵构造累计式和全局资源界。

## 形式化接口

| 包 | Lean 源码及结论 |
| --- | --- |
| G0 | `TreeBudgetSubtreeResourceGuard`：根孩子重数和 `rootMass`；矩阵可行的必要条件；`solveGuarded_eq` 保持完整证书；通过预检时 `m ≤ M` 及含零路线的 `P ≤ (max 1 M)^M` |
| G1 | `ResourceDenominators`、`ResourceWidths`、`ResourceRealizes`：约分分母桥、服务分母 LCM 恒等式、整数权重/floor 预算界、去重前节点和 inside 费用、cap 前根原始配对费用、矩阵及临时自然数坐标界 |
| G2 | `ResourcePrimitivesSeed`、`ResourceExecutorSeed`、`ResourceStats`：单次执行；完整有序键表和矩阵证书擦除；`solveR_keyStats` 与 `solveAutoR_keyStats` 是整份 `DPStats` 相等，包含两个 maxima |
| G3 | `ResourceCensus`、`ResourceKeyMaps`：选择列表不变量、每个节点一次的子树累计、八个载荷字段的精确式及独立的键映射三角界 |
| G4 | `ResourceBounds`：九字段载荷上界、总资源界、矩阵/临时坐标内容容量、预检入口和质量参数界；`ResourceExamples`、`ResourceAudit` 及独立 Python 回归 |

以上短模块名均有 `TreeBudgetSubtree` 前缀。G0/分母/标量宽度在 `UAVProof.TreeBudgetSubtreeResource` 命名空间，其余在 `UAVProof.TreeBudgetSubtreeResourceSeed`。保留 `Seed` 名称用于追溯用户提供的执行器，不表示其中定理依赖未证明的假设。数学种子被整合为 Guard、Denominators 和 Widths 模块，没有重复维护第二份预检实现。

公开入口 `solveGuardedR` 在构造任何 `m` 维向量及调用 `prepare` 之前检查 `m = rootMass R H`。失败直接返回 `none` 和零 DP/载荷计数；通过才执行 `solveAutoR`。`solveGuardedR_erase` 和 `solveAutoR_erase` 保持整个 `Option Certificate`，再由基线 `solveAuto_eq` 接到原有有理见证求解器。

### 数值及原始状态

令 `n=N−1`，非根服务分子绝对值和分母均小于 `2^b`。`prepare.scale` 等于非根服务约分分母的 LCM（实现把根项换成分母为 1 的零）；因此在固定根与服务值时与树形无关。

```text
D ≤ 2^(n*b)
|w(v)| < 2^((n+1)*b+1)
|floor(D*T)| < 2^((n+1)*b)       当 |T.num| < 2^b
W = sum_{v != root} |w(v)| * H(v)
W < 2^((n+1)*b+1+Nat.size(n)+Nat.size(U))
```

预算界包含负预算；分母桥包含 `D=0`，自动准备的 D 则严格为正。标量证明不需要多余的 `b≥1` 或预算分母上界。这里的位宽是绝对值的二进制位数，具体有符号编码的符号位属于编码约定。

`inside_cost_bound` 覆盖任意孩子子列表，含空表所生成的基础费用；`insideRaw_cost_bound`、`nodeRaw_cost_bound`、`rootsRaw_cost_bound` 分别覆盖去重之前和根 cap 拒绝之前的费用。证明先建立完整整数矩阵的 `Realizes`/选择不变量，再利用互不相交的孩子子树，未把保留状态的网格界直接用于 raw 表。

`nodeRaw_coordinate_fits`、`temp_prefix_coordinate_fits`、`certificate_coordinate_fits` 覆盖实际矩阵、任意部分累加和以及最终证书；根坐标为零。`coordBits U = max 1 (Nat.size U)`，所以 U=0 也有明确的一位坐标编码。

### 精确载荷与全局界

`nodeRawEntries` 是证明/回归视图。执行器在实际生成矩阵时计数，不为取得统计重新运行这个视图。令 `A_v` 为节点去重前条目数，`A=∑_{v≠root} A_v`，`k_v` 为孩子数，`C` 为返回证书存在时的 1（否则 0）。`solveR_charges` 给出：

```text
matrices     = A+C
matrixCells  = m*N*(A+C)
columnReads  = m*(A+C)
childReads = natAdds = tempCells
             = m*(N−1)*(sum_{v!=root} k_v*A_v + C*k_root)
pickCons     = keyStats.insidePairs + keyStats.rootPairs
rootZeroCells = m*C
```

费用相同而载荷不同的条目依旧保留右侧代表。完整 `map key` 的费用独立于短路相等比较：每次调用有 `2*keyMapCells ≤ ell*(ell−1)`；累计使用 `dedupInput ≤ 2*n*P`、`maxRawTable ≤ P` 得到 `keyMapCells ≤ n*P*(P−1)`。没有假设键对载荷单射。

`A_v≤P`、`A≤nP` 与 `∑_v k_v=n` 给出 `childReads/natAdds/tempCells ≤ m*n²*P`。三个精确式由同一个度数加权和推出，没有逐节点放大成多一个 N 的界。

```lean
theorem solveAutoR_resourceWork_le
    (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ)
    (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    resourceWork (solveAutoR R H s m T) ≤
      64 * (N + 1)^2 * (m + 1) * (U + 1) * globalProduct R H m^2
```

`resourceWork = logicalWork keyStats + payload.work`。实现证明先将九个载荷项分别压到同一上界，获得常数 9；再与旧逻辑界的常数 32 合并到 64。这比参考文稿的载荷常数 6 更宽，但总接口及其无额外容量假设的要求相同。

矩阵坐标内容累计容量至多 `m*N*(n*P+1)*coordBits U`；临时坐标内容累计容量至多 `m*n²*P*coordBits U`。`M=totalMass R H` 时，`solveGuardedR_resourceWork_le` 对整个预检入口给出 `64*(N+1)^2*(M+1)^2*(max 1 M)^(2*M)`，含预检失败和 `m=0`。

这些是指定源码计费模型中的界。预处理和预检本身、计数器维护、整数运算的机器位成本、对象头、地址/共享指针、其他状态向量、栈、引用计数及 GC 不在九字段中；没有宣称 `totalTime`、整个堆的 `peakMemory`、编译后的实际分配次数或通用加速。

## 验证与复现

2026-11-15 在本地实际执行：12 个新 Lean 模块（含审计入口）定向构建成功；11 个 `decide +kernel` 例子及 603 组新执行回归通过，另覆盖 `m=2^200` 提前拒绝和 `keyMapCells=2190`、`eqCalls=290` 的独立边界。新回归逐项检查完整证书、全部 17 字段、矩阵累计式、数值宽度、原始 inside/节点/根费用及临时坐标。

原有 F 包 603 组自动证书检查已直接重跑；A–E 的 483 组检查及 21 组 DP 用例也直接重跑通过。独立 Python 本次实际运行通过 3,680 组有序表/LCM 检查、22,080 组资源/证书/位宽/预检场景及两个特殊边界；深链与高分支星形计数由此独立覆盖。各类别重叠，不将它们相加。

构建及单独 `lake env lean` 的直接审计均成功，167 个命名声明逐项回读齐全，仅使用 `propext / Classical.choice / Quot.sound` 的子集，无 `sorryAx` 或额外公理。源码无 `sorry`、`admit` 或自设公理；保留少量行长提示，不存在构建错误。

固定 Lean `v4.30.0-rc2` 和 Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`，未升级依赖。使用现有开发环境与缓存，没有冷环境重建。发布副本与验证源码逐文件核对；推送和 Issue 编辑不算再次构建。不同批次及重叠检查类别的数字不相加为独立实例总数。

```powershell
New-Item -ItemType Directory -Force verification/runs/subtree-resources
lake build LeanCompletion.UAV.TreeBudgetSubtreeResourceAudit
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeResourceAudit.lean
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeResourceExamples.lean
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeAutoExamples.lean
lake env lean LeanCompletion/UAV/TreeBudgetSubtreeBoundsExamples.lean
python tools/check_subtree_resources.py
```

执行时将原始 stdout/stderr 重定向到本地忽略目录 `verification/runs/subtree-resources/`。审计源逐条 `#print axioms`，不靠只扫描源码中的占位符来判断证明完成。

[中文纸面参考](SUBTREE_RESOURCE_PROOFS_ZH.tex) 按用户要求原样保存、未编译 LaTeX。它是实施前的推导与种子说明，其中“尚未编译/后续目标”描述参考稿当时的状态；本报告和提交中的 Lean 源码记录实际实施结果。该原稿 SHA-256 为 `b52d6360146b010c477dbc09117253d92ae2cdf577e5ac7eee9686df15fd1a3f`。压缩包、原始说明文本、CHECK_RESULTS、生成 JSON、运行日志及构建产物不入库。

本包只完成子树自动整数见证执行器的上述资源层。给定游走拼接、逐顶点路线输出、一般访问副本往返契约以及标准机器成本仍由相关 Issue 分别保留。

## 发布源码指纹

以下 SHA-256 对验证后的源码字节计算，作为源码溯源；不是原始运行或日志清单。所有新源码与本地验证副本字节一致。55 个本地 Lean 导入闭包模块中，既有依赖与发布基线仅有四处文件末尾空白差异，无证明内容差异。

| 源码 | SHA-256 |
| --- | --- |
| `TreeBudgetSubtreeResourceAudit.lean` | `88e9f673f835e430f58e58072d8f06b91b017f92cb329ef2cb2a2cdfc4330e66` |
| `TreeBudgetSubtreeResourceBounds.lean` | `0a90065cea4a2e02ad7bce2b5ba499635b67b5008ac115c7efd7a73411039ac9` |
| `TreeBudgetSubtreeResourceCensus.lean` | `a7db8d8480f72f9bf20670e78c8ecf012d82701b98c3caf508ae003d138abf0c` |
| `TreeBudgetSubtreeResourceDenominators.lean` | `70819059885fb6a802b846e41de3ca4d3ad57c0ed024226b931e293eb5c02bcc` |
| `TreeBudgetSubtreeResourceExamples.lean` | `bff1f10c31ca3e8ff01ebb4c535db7ea100a4677aafa5c1545ac2aa6f0fd912b` |
| `TreeBudgetSubtreeResourceExecutorSeed.lean` | `e5731c066a5846cc4606e364a67b42764eff06e37ed4d8382a974640bf8fff77` |
| `TreeBudgetSubtreeResourceGuard.lean` | `bad71ae1ca8c8a12258936b8b80e20e90587b9d0abad9bde9637034fce66a672` |
| `TreeBudgetSubtreeResourceKeyMaps.lean` | `68a9701fd598a5c928a331c1b11d9e7374fa825681972d3d4920a1db20e17714` |
| `TreeBudgetSubtreeResourcePrimitivesSeed.lean` | `7e86cd86231647c09f6897e7cb8ecbb86179ae83c17cf216983a6ec0e3432a4c` |
| `TreeBudgetSubtreeResourceRealizes.lean` | `edb256cb544cfdc1f15520545ceb3d6eabfb8beef6068a1aa04f49e57859d702` |
| `TreeBudgetSubtreeResourceStats.lean` | `596231fad1f4e3e2c50e12971bec90a0f0e1372e81bd989909542e1c7c362067` |
| `TreeBudgetSubtreeResourceWidths.lean` | `1b2daa814cdee9e50be874800b55d815b3acc992336e1a7b95ffc4f62ad1e338` |
| `check_subtree_resources.py` | `2403a35228166559caf59957eb373148517f09626533f66812d53dbecacb8afd` |
