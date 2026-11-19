# 树路由认证：三项创新计划与分阶段验收

日期：2026-11-18。研究基线：`f3ea0823be69ffa7152dec903069c2ba79ad20a4`，分支 `research/structural-service-cuts-20261023`。

实施追踪：[计划 A — #24](https://github.com/huam54925-cpu/uav-routing-certification/issues/24) · [计划 B — #25](https://github.com/huam54925-cpu/uav-routing-certification/issues/25) · [计划 C — #26](https://github.com/huam54925-cpu/uav-routing-certification/issues/26)。总览继续由 [#15](https://github.com/huam54925-cpu/uav-routing-certification/issues/15) 协调；本页 A0–A4、B0–B4、C0–C4 是阶段编号的统一定义。

本文最初随 `3389ea7` 发布为研究计划，该文档批次未执行 Lean 或 Python 试验。随后优先实施 [A0–A2](TREE_BUDGET_SPARSE_CERTIFICATES_STATUS.md)，保存为独立本地提交 `87cb4e0`，再实施 [A3 与实际编码长度](TREE_BUDGET_SPARSE_WIRE_STATUS.md)。新增运行和剩余位时间义务各自单列。下文“建议接口”是原计划名称，实际声明名以验收记录及源码为准；B/C 仍为计划。

三项计划围绕同一个问题展开：**哪些可行解可以短表示，哪些边界信息不能丢失，以及哪些路线标签可以安全消除？** 它们分别产生证书规模定理、接口下界和算法改进；不把更多成本常数、更多状态文档或更大的模型范围本身作为创新成果。

配套的[文献核验与适用边界说明](TREE_BUDGET_LITERATURE_REVIEW_20261118.md)记录论文版本、已读范围、参数化外延和不可直接搬用的结论。本文负责可执行的阶段计划；文献中的探索性推论不自动成为本轮已经实现或已经形式化的结果。

完整证明写法与 Lean 关键接口草案见[中文理论草稿 LaTeX 源码](TREE_ROUTING_RESEARCH_DRAFT_20261118_ZH.tex)。该源码同样是待本地编译、核对和逐项形式化的研究材料。

## 1. 研究对象、现有基础与本轮边界

固定带根树、精确边流 `H`、路线数 `m`、有理服务费 `s` 和统一预算 `T`。每条路线是非空 depot excursion，中途不回 depot。令非根顶点集合为 `V⁺`、`n = |V⁺|`，路线 `i` 在顶点 `v` 的父边精确重数为 `pᵢ(v)`。本文的 `n` 是全部非根顶点数；已有 #22 的参数 `t` 保留为正坐标数，不与这里的维度混用。已有矩阵刻画要求：

1. 列和精确：`Σᵢ pᵢ(v) = H(v)`。
2. 每行恰有一次根出发：`Σ_{v child(root)} pᵢ(v) = 1`。
3. 正支持向祖先闭合；它不是 `pᵢ(child) ≤ pᵢ(parent)`。
4. 每行服务费用不超过预算。

用已有服务费用变换记 `w(v) = s(v) + s̄(parent(v))`，其中根处的延拓值取零，则一行费用为 `Σ_v w(v)pᵢ(v)`。本文允许 `w` 为任意有符号有理数。需要已有 `HasDegrees` 等假设才能使用的路线语义等价，仍须逐项保留。

本轮直接复用以下四块基础，不重建第二套理论：

| 已有基础 | 本轮怎样使用 | 不重复的工作 |
|---|---|---|
| 四约束矩阵与合法路线的等价、精确边流和有符号费用公式 | A 的解码语义；B 的例族合法性；C 的重排行为 | 不另造路线语义或偷偷加强支持约束 |
| #23 的 strict-hub 归约、二进制编码及语义保持 | A 完成短证书与位成本检查器后，补充成员性方向 | 不重复 3-PARTITION 归约，也不提前宣布标准编码下 NP-complete |
| #22 的残余向量搜索、缓存与地址执行成本 | 保持作为独立基线，后续比较证书和搜索策略 | 不把其已证明成本自动转移给 A/C |
| #19 的子树 DP、整数化、预算优化/profile、路线输出及局部 heap 精化 | 提供正确性参照和输出桥；C 产生独立的新 API | 不把局部 heap 精化写成完整 DP 地址执行已闭合 |

[TreeBudgetSubtreeBreakpointBounds.lean](../LeanCompletion/UAV/TreeBudgetSubtreeBreakpointBounds.lean)、[TreeBudgetSubtreeRouteOutput.lean](../LeanCompletion/UAV/TreeBudgetSubtreeRouteOutput.lean)、[TreeBudgetSubtreeHeapDedup.lean](../LeanCompletion/UAV/TreeBudgetSubtreeHeapDedup.lean) 等已有模块分别处理既定预算查询、显式路线输出及去重存储层。本文不把已存在的预算断点压缩当作新成果。

已核验的具体复用入口如下；新接口应在这些入口之上扩展：

| 现有模块 | 已有入口 | 对新工作的约束 |
|---|---|---|
| [TreeBudgetPatterns.lean](../LeanCompletion/UAV/TreeBudgetPatterns.lean) | `matrix_iff_pattern_counts`、`family_iff_counts`、`pattern_count_total` | 模式计数与路线/矩阵之间的语义桥已存在 |
| [TreeBudgetCertificate.lean](../LeanCompletion/UAV/TreeBudgetCertificate.lean) | `Certificate`、`Valid`、`checkCertificate_eq_true_iff`、`valid_implies_matrix`、`matrix_iff_exists_certificate` | 已有不展开重复行的检查器；A 不重建格式或 sound/complete 证明 |
| [TreeBudgetCertificateCompression.lean](../LeanCompletion/UAV/TreeBudgetCertificateCompression.lean) | `compress_sound`、`compress_checked`、`compress_reduced` | 已有相同行合并；A 新增的是不同合法解之间的稀疏存在界，不是把合并重命名 |
| [TreeBudgetSubtreeBudgetProfile.lean](../LeanCompletion/UAV/TreeBudgetSubtreeBudgetProfile.lean) | `optimize_spec`、`least_exact_iff` | A/C 新 API 对齐可行性与最小预算，不自动继承旧的选证顺序 |
| [TreeBudgetSubtreeBudgetQueries.lean](../LeanCompletion/UAV/TreeBudgetSubtreeBudgetQueries.lean) | `lookup_eq_auto`、`lookup_comparisons` | 现有多预算查询和比较计费继续独立有效 |
| [TreeBudgetSubtreeRouteOutput.lean](../LeanCompletion/UAV/TreeBudgetSubtreeRouteOutput.lean) | `round_trip`、`output_word`、`output_size`、`output_moves` | 稀疏证书和规范矩阵在需要显式路线时调用此桥 |
| [TreeBudgetRootFactorization.lean](../LeanCompletion/UAV/TreeBudgetRootFactorization.lean) | `matrix_iff_branch_matrices` | 根分支分解已证明，可以复用，不再作为新创新任务 |

以下三条旧工作继续各自收口：

- **#19 执行层**：继续统一已承诺的成本与执行语义，最终给出可复现验证；这是可靠性主线，和创新包并行，不成为无限扩展 A–C 范围的理由。
- **#21 表示层**：A 的重复行压缩证书与显式路线输出都应在这里明确表示差异。显式路线可能需要 `2M+m` 个顶点词，`M=ΣH(v)`；短证书不得暗中展开它。
- **#23 复杂度层**：A 的多项式长度证书只提供成员性路线的一部分。固定二进制语法、输入有效性检查和检查器位时间证明完成后，才与困难性方向对接。

## 2. 三项计划的依赖与工作顺序

| 计划 | 核心产物 | 首要依赖 | 允许独立结束的位置 |
|---|---|---|---|
| A：双稀疏界与短证书 | 两个不同来源的行类型稀疏界；已有检查器的二进制精化；成员性证明 | 四约束矩阵刻画、有符号线性费用、现有证书及编码层 | 新的短证书存在界可先交付；不必等待高效 sparsifier |
| B：可组合接口与代表规模下界 | 指定补全语义；五顶点单位矩阵例族；有标号与无标号下界 | 四约束矩阵刻画、整行重排、明确切口语义 | 完成有限例族与代表下界即可；不强求任意算法下界 |
| C：路线置换商 DP | 联合类型直方图、运输表 join、规范见证重建及新求解 API | 整行置换不变性；现有子树 DP 的语义接口 | 若全 DP 性能收益不足，保留正确的 join 内核和结构化实例加速 |

按本轮指示，当前顺序调整为 A 包优先，分两次完整交付：

1. A0–A2：完成行多面体、子集和界、奇偶界及同一原检查器证书，作为第一交付。
2. A3：固定独立路线数输入前缀及压缩证书二进制格式，证明解析与检查精化；同步证明实际长度 `L * (L / 2 + 1)` 和全部输入位串的短见证语言等价。
3. 剩余 A4：对当前验证器的全部输入/证书位串证明固定多项式位时间，包含拒绝路径；明确标准计算模型连接后再判断 NP 成员性是否闭合。
4. A 包之后推进 B 的指定补全定义与反例族，再固定 C 的联合类型和整行置换契约。
5. C 从单个运输表 join 接到完整 DP，另行验收正确性、见证和成本；A 的高效 sparsifier 不作为存在性定理的前置条件。

**共同的接口原则**：A 和 C 可以返回一份新的合法证书，并保持可行性和最小预算值；不承诺逐字保持旧求解器的 tie-breaking 证书。旧 API 的有序见证精化继续保留。若未来需要两者完全一致，必须作为额外性质独立证明，不能藏在“等价”一词里。

## 3. 计划 A：双稀疏界、压缩证书与二进制检查

### A.1 要回答的研究问题

二进制输入可能允许数值极大的 `m` 与 `H`。即使一个解的显式矩阵有 `m` 行、展开路线有 `Ω(M)` 长度，是否总存在只含多项式多个比特的可行性证书？如果有，这种短表示能否在不展开重复行、不生成路线词的前提下被认证？

这里研究的是**解的不同路线行类型数**，不要求每行本身只访问少量顶点，也不要求给定的旧证书已经稀疏。

### A.2 格式与单行多面体

复用现有 `TreeBudgetCertificate.Certificate`。它在数学上可写为有限列表

\[
\mathcal C=((\lambda_1,p^1),\ldots,(\lambda_k,p^k)),
\qquad \lambda_j\in\mathbb N_{>0},\ p^j\in\mathbb N^n.
\]

新的编码层将 `λⱼ` 和行坐标以二进制保存。已有检查器验证：

\[
\sum_j\lambda_j=m,\qquad
\sum_j\lambda_jp^j(v)=H(v),
\]

并对每个类型检查根约束、祖先正支持及费用约束。已有 `Certificate` 允许零重数和重复行；存在性证明可用现有 `compressCertificate` 得到 `Reduced` 表示后再讨论正重数与不同类型数。原检查器也检查零重数行，因此对任意畸形证书“删除零重数行保持布尔检查结果”并不成立；已有压缩定理的前提必须保留。空证书专门处理 `m=0`；不得用正路线情形的最小值或除法覆盖它。

定义有界有理多面体

\[
P_T=\left\{p\in\mathbb R^n:
\begin{array}{l}
0\le p_v\le H_v,\\
p_v\le H_vp_{\operatorname{parent}(v)}
\quad(\operatorname{parent}(v)\ne\mathrm{root}),\\
\sum_{v\in\operatorname{children}(\mathrm{root})}p_v=1,\\
\sum_vw_vp_v\le T
\end{array}\right\}.
\]

对于整数点，第二行与已有正支持约束等价：父坐标为零时子坐标必须为零；父坐标为正时 `p_v≤H_v` 已足够。这个线性化只在这里说明的整数点语义下使用，不把连续松弛误写成原问题。

可行矩阵对应把 `(H,m)` 表成 `P_T∩ℤⁿ` 中行向量附加计数坐标后的非负整数锥组合。需要明确空集、零流和 `m=0` 的边界情况。

### A.3 两个稀疏界与合并方法

目标命题：若存在可行矩阵，则存在压缩证书，其不同类型数满足

\[
k\le\min\!\left\{
2^n,
\left\lfloor\log_2\!\left((m+1)\prod_{v\in V^+}(H_v+1)\right)\right\rfloor
\right\}.
\tag{A1}
\]

对 `m=0`，直接取 `k=0`。Lean 首版可先使用避免实数对数的整数界

\[
k\le\min\left\{2^n,\ B\right\},\qquad
B=\operatorname{Nat.size}(m)+\sum_v\operatorname{Nat.size}(H_v).
\tag{A2}
\]

同时保留 `2^k ≤ (m+1)Π_v(H_v+1)` 的精确计数形式；之后再提供与对数式相符的引理，避免把浮点对数引入证明。

**界一：最小支持与子集和碰撞。** 在所有可行压缩表示中选不同类型数最小者。它的 `2^k` 个类型子集的增广和

\[
\left(\sum_{j\in A}p^j,\ |A|\right)
\]

必须两两不同；否则消去两个子集的公共部分，沿剩余两组的等和关系移动整数重数，直到至少一个正重数降为零。这保留列和、路线数和每种单行的预算合法性，却减少支持，矛盾。每个子集和位于 `0…H_v` 与 `0…m` 构成的盒中，得到 (A1) 的对数界。

**界二：奇偶类与平方势。** 在所有可行的 `m` 行矩阵中选

\[
\Phi=\sum_{i=1}^m\sum_v p_i(v)^2
\]

最小者。若有超过 `2^n` 种不同行，则两种不同行 `p,q` 具有相同逐坐标奇偶性。令 `z=(p+q)/2`，则 `z` 是整数点，且因 `P_T` 凸而仍是合法单行。把一份 `p` 和一份 `q` 换成两份 `z`，保留列和、路线数；并有

\[
\|p\|^2+\|q\|^2-2\left\|\frac{p+q}{2}\right\|^2
=\frac12\|p-q\|^2>0,
\]

与最小势矛盾。有符号费用没有障碍，因为这里只用线性费用和凸性，没有使用部分费用非负性。

**合并**：上述两种最小化未必由同一个构造同时取得。先证明存在 `≤2^n` 类型的可行表示，再取全局最小支持表示；它既不超过 `2^n`，又满足子集和盒界。不得直接断言最小平方势表示自动满足最小支持证明的前提。

### A.4 分阶段实施与建议 Lean 接口

| 阶段 | 工作与产物 | 建议接口名，均待实现 | 阶段验收 |
|---|---|---|---|
| A0：单行与证书契约 | 依托已有 `ValidPattern`/`RowValid` 作单行支持线性化、建立多面体整数点等价；复用 `Certificate`、`Reduced`、模式计数桥和检查器 | `row_mem_polytope_iff`、`Certificate.SupportBound`；其余优先复用已有入口 | 只加契约短引理；正、零路线及有符号费用均明确；不另造平行证书格式 |
| A1：二进制盒界 | 证明最小支持、子集和注入及交换消元；先做无对数版本 | `minimalSupport_subsetSums_injective`、`exists_compressed_card_pow_le_box`、`exists_compressed_card_le_bitSize` | 定理的界只依赖输入二进制规模；没有枚举 `m` 行的运行时主张 |
| A2：奇偶界 | 引用 A0 的多面体契约，证明整数中点合法、平方势下降；合并两界 | `row_midpoint_valid`、`midpoint_potential_lt`、`exists_compressed_card_le_min` | 给出 `2^n` 和位长界均可适用的精确假设 |
| A3：二进制检查精化 | 给已有 `checkCertificate` 接入二进制解析及明确规范化约定；证明新编码执行与原检查结果一致 | `decodeSparseCertificate`、`checkBinaryCertificate`、`checkBinaryCertificate_refines` | 输入含超大 `m/H` 时仍不分配 `m` 长向量；拒绝畸形编码；不重复现有 sound/complete |
| A4：位成本与成员性 | 固定语言编码、证书长度、整数/有理运算位宽和成本；与 #23 对接 | `compressed_encoding_size_bound`、`checkBinaryCertificate_bitcost_poly`、`exactTreeBudget_mem_NP` | 标准二进制语法下长度与检查时间均已证明，才声明成员性 |

接口名是设计建议，应在落地时复用现有类型和命名，不为配合本文新建平行模型。A4 的 `NP` 名称仅是预期最终接口，不表示仓库当前已有对应复杂度类形式化。

若完整输入编码长为 `L`，每种行类型及其重数可用 `O(L)` 位表示，A1 给 `k=O(L)`，因此证书可达 `O(L²)` 位。这个结论需要固定字段顺序、长度分隔和输入有效性约定；**短证书存在性本身不等于多项式时间构造算法，也不等于已经证明 NP-checker 的位时间。**

### A.5 回归族、成功标准与退出条件

必须覆盖：

- `m=0` 下可行/不可行两种语义；零费用、零流坐标、负费用和负预算。
- 二进制大重数但极少类型的族，例如同一合法行重复巨大次数；验证 checker 只读重数。
- 同奇偶不同行的中点替换；含负服务费的例子以排除错误的非负假设。
- 子集和碰撞、重数不相等以及交换时选择最小可减重数的例子。
- `2^n` 界更强与位长界更强的不同参数区间。
- 原检查器应接受满足所有条件的重复合法行及合法零重数行；规范化应按已有前提保留合法性。只有新二进制规范格式明确禁止这些表示时，格式层才可拒绝，并证明规范化后的表示仍存在。
- 错误列和、错误根出发数、断裂支持、费用超限及非法行（即使其重数为零）必须由原检查器拒绝；畸形二进制输入由解析层拒绝。
- 原矩阵检查器、压缩检查器与小规模独立枚举的语义比较；这些是未来本地执行任务，本文件不声称已跑过。

A 的最低新增产物是双稀疏存在性定理及其到已有检查器的桥；完整成果还需二进制解析/位成本精化与成员性闭合。已有检查器的 sound/complete 不作为新定理成果重复计算。结果只认证**可行性**。不据此声称存在同等长度的不可行证书、最优性证书或多项式时间求解器。

若高效 sparsifier 暂时不可得，保留存在性和 checker，明确把构造问题留待后续。若 `2^n` 奇偶证明的形式化成本过高，先合入 A1 的位长界；它已足够支撑短证书方向。若标准编码成本尚未完成，则使用“短证书及抽象检查器”表述，不抢先关闭 #23 的成员性任务。

## 4. 计划 B：指定补全接口、必要信息与代表规模下界

### B.1 先固定观察语义

一个切口处的局部证书可以有多种不同的等价概念，必须分开：

| 语义 | 保留的观察 | 本计划的地位 |
|---|---|---|
| 根部统一预算查询 | 已完成矩阵的最大路线费用，以及既有 API 的选证顺序 | 已有 profile 工作，不重复 |
| 指定外侧补全，有标号路线 | 对每个固定外侧部分和同号行配对，拼接是否可行 | B 的主下界 |
| 指定外侧补全，允许行置换 | 是否存在一个行配对排列使拼接可行 | B 的无标号下界，衔接 C |
| 外侧图实例仍可自由重新求解 | 量化全部外侧分配后的存在性 | 不由本文单位矩阵构造自动覆盖 |

“指定外侧补全”包括固定的路线行/外侧矩阵或已给定路线片段，不是只指定一张尚未分配的图。B 首先给出与 #19 supplied-walk / gluing 目标一致的精确定义，再证明哪些边界字段足够。

充分性引理的边界 metadata 必须覆盖当前 gluing 操作实际读取的接口，包括边界穿越、支持和费用。不要在未检验 join 假设前就宣布某个 `(support,cost)` key 对所有拼接足够。以下例族的作用，是在**逐路线边界穿越次数已经完全相同**时仍证明费用分配不能被任意丢弃。

### B.2 五顶点非负费用构造

取 `m≥2`、`K≥m`，令

\[
\mathcal C_{m,K}=\{c\in\mathbb N_{>0}^m:\ \sum_i c_i=K\}.
\]

树边为 `o–h`、`h–v`、`v–x`、`h–y`，根为 `o`；在 `h–v` 切开，内侧子树含 `v,x`。设

\[
H_h=H_v=m,\quad H_x=K,\quad H_y=(m-1)K,
\qquad s_h=s_v=0,\quad s_x=s_y=1,\quad T=K.
\]

对内侧索引 `c'∈𝒞_{m,K}`，令每路线 `p_i(v)=1`、`p_i(x)=c'_i`。对指定外侧索引 `c∈𝒞_{m,K}`，令 `p_i(h)=1`、`p_i(y)=K-c_i`。

由于 `c_i≤K-m+1≤K-1`，所有 `K-c_i` 都正；其总和是 `(m-1)K`。所有例子在切口 `h–v` 上逐路线穿越次数都是 1，活跃集相同，全部正支持合法。每条拼接路线费用恰为

\[
c'_i+K-c_i.
\]

因此

\[
\begin{aligned}
\text{compatible}(c',c)
&\iff \forall i,\ c'_i+K-c_i\le K\\
&\iff \forall i,\ c'_i\le c_i\\
&\iff c'=c,
\end{aligned}
\tag{B1}
\]

最后一步只用二者总和都等于 `K`。这给出了阶数

\[
N_{\mathrm{lab}}=\binom{K-1}{m-1}
\]

的单位兼容矩阵。任何保留所有指定外侧补全查询的接口，必须区分这些等价类；任何只能从这些候选中删除元素、仍须代表同一组查询的子集，必须保留全部 `N_lab` 个候选。该兼容矩阵在任意域上秩都为 `N_lab`。

这一构造使用非负费用。因此下界源于精确分配与指定补全的观察能力，不能把它归咎于负费用。可另收录 `H_y=K,s_y=-1,T=0,p_i(y)=c_i` 的有符号对消版本，但它不是主定理的必要前提。

### B.3 无标号版本与二进制参数

如果允许拼接时选择任意排列 `σ`，则

\[
\exists\sigma\in S_m\ \forall i,\ c'_{\sigma(i)}+K-c_i\le K
\iff \{c'_1,\ldots,c'_m\}_{\mathrm{multi}}
=\{c_1,\ldots,c_m\}_{\mathrm{multi}}.
\tag{B2}
\]

取非递减向量作为轨道代表，仍得到单位矩阵，阶数为 `p_m(K)`，即把 `K` 分拆成恰好 `m` 个正部的整数分拆数。

特别地，固定 `m=2` 时

\[
N_{\mathrm{unlab}}=p_2(K)=\lfloor K/2\rfloor.
\]

五顶点树、两路线均固定，输入只有 `K` 等重数需要增长。若 `ℓ=bitlength(K)`，该显式代表集合大小随 `ℓ` 指数增长。这说明路线置换能够消除标签冗余，却不保证把所有数值分配压成常数或二进制输入的多项式个数。

**下界的精确范围**：

- 它是等价类数、显式代表子集元素数和兼容矩阵秩的下界。
- 一个等价类标签可以只需要 `⌈log₂ N⌉` 位；`N` 个等价类不等于单个摘要必须占 `N` 位。
- 对固定 `m=2`，一个分拆代表本来就可用 `O(log K)` 位保存。不能从 `N=Θ(K)` 推导任意符号表示需要指数位存储。
- 不排除隐式集合、生成函数、整数规划、其他分解或完全不同的求解器；不推出任意算法的指数运行时间，也不自动得到 ETH/SETH 下界。
- 对某个受限的实际未来补全集，仍可能有更强压缩；B 量化的是构造中给出的全部指定补全查询。

### B.4 分阶段实施、回归与退出条件

| 阶段 | 工作与产物 | 建议 Lean 接口名，均待实现 | 验收 |
|---|---|---|---|
| B0：观察契约 | 固定切口、inside/outside 类型及 labeled/permutable gluing | `PrescribedCompletion`、`BoundaryEquivalent`、`OrbitBoundaryEquivalent` | 明确哪些数据固定、哪些变量可以重新选择 |
| B1：充分性 | 把现有 key 的字段与 gluing 读取项逐一对应 | `boundaryKey_eq_preserves_gluing` | 复用原合法性与费用定理，不依赖“直觉上足够” |
| B2：构造与分离 | 五顶点树、固定 `H`、两侧矩阵、非负费用及 (B1) | `fiveVertex_inside_valid`、`fiveVertex_outside_valid`、`fiveVertex_compatible_iff_eq` | 全部候选共享同一输入数据与同一边界穿越数 |
| B3：代表下界 | 正整数组合计数、代表子集必要性；秩作为可选加强 | `completionRepresentative_card_lower`、`compatibilityMatrix_eq_identity` | 不把元素数界改写成任意编码位长或求解时间下界 |
| B4：无标号版本 | 整行排列、分拆代表、`m=2` 的精确计数 | `fiveVertex_perm_compatible_iff_multiset`、`twoRoute_orbit_card` | 验证 `floor(K/2)`，并与 C 的轨道定义一致 |

回归族至少包括 `m=2` 的奇偶 `K`、`K=m`、重复部件和互异部件、非平凡排列可拼接、不同多重集不可拼接。可加总和和最大值均相同的分离例：`(1,4,5)` 与 `(2,3,5)`，以说明“总量+峰值”仍不足。所有这些都应使用真实五顶点矩阵与已有检查器验证，而不只验证抽象数值向量。

B 的成功标准是一个可组合接口的充分性定理，配一个完整可实现的必要信息例族。若现有 gluing key 还缺字段，先修正 key 或缩小所证 gluing 类，不为保持旧 key 而弱化问题定义。若任意表示/算法下界无法获得，不扩张本计划；单位矩阵的明确接口下界本身就是完整产物。

## 5. 计划 C：路线置换商 DP 与运输表拼接

### C.1 动机与保留的信息

当前同质路线拥有相同服务费规则和统一预算，路线编号通常不是语义信息。对矩阵施加同一个行排列，列和、根约束、祖先支持和最大费用均保持。因此可以在完整路线状态的置换轨道上工作。

必须排列**完整行及其全部关联字段**。不能分别排序费用、边界重数、活跃标记后再拼回去；这样的操作会破坏同一路线内部的相关性。异质预算、路线专属费用或外部固定身份会缩小甚至消除置换群；首版明确只支持当前同质模型。

设一条边界行的联合类型为

\[
\tau=(\text{boundary metadata},\text{cost},\text{other join-relevant fields}).
\]

完整 key 中的所有会影响相容性或费用更新的字段都必须进入联合类型。直方图记录每种 `τ` 的重数，payload 保存重建完整矩阵所需的见证信息。内部不同矩阵若对未来语义完全等价，可以选择一个规范 payload；选择策略是新 API 契约的一部分。

### C.2 先证明群作用，再实现规范化

第一组目标是对 `σ∈S_m` 证明

\[
\operatorname{Valid}(P)\iff\operatorname{Valid}(\sigma\cdot P),
\quad
\operatorname{costVector}(\sigma\cdot P)=\sigma\cdot\operatorname{costVector}(P),
\quad
\max_i C_i(P)=\max_i C_i(\sigma\cdot P).
\tag{C1}
\]

在此基础上建立有限可排序类型的直方图、规范代表及 witness 重排。首版输出新定义的规范证书，保证回到原检查器可接受。**不承诺返回旧求解器在费用并列时选中的同一个矩阵。**

### C.3 运输表：保留所有相对配对

左右子表的不同联合类型分别为 `a∈A`、`b∈B`，重数分别为 `μ_a`、`ν_b`，两侧总行数均为 `m`。用非负整数运输表 `N=(N_ab)` 表示有多少条路线把左类型 `a` 与右类型 `b` 配在一起：

\[
\sum_bN_{ab}=\mu_a,\qquad
\sum_aN_{ab}=\nu_b,\qquad
N_{ab}=0\quad\text{若 }a,b\text{ 不兼容}.
\tag{C2}
\]

这里“不兼容”由现有 join 的语义定义，不预设为只看费用。每个正格子通过现有单行 merge 得到新联合类型，其重数为 `N_ab`；相同新类型再合并。

核心定理是：**满足 (C2) 的运输表，等价于左右两族行之间某个保持兼容性的相对排列。** 从排列到表，计数每种配对即可；反向把每个左/右类型的索引集合分别分成大小 `N_ab` 的块，在相应块间建立双射，拼成全体行的双射。

反向重建时，必须移动整条局部矩阵行，而非只移动 cost key。运输表可消除重复的标签配对枚举，但不能只保留一种贪心配对，也不能假定所有表都导向相同最优值。

### C.4 两个必须失败的错误实现

1. **排序后同序相加**：左右费用都是 `(0,10)`。同序合并峰值为 20，交叉配对峰值为 10。只保留同序配对会丢掉最优解。这个例子针对相对配对，不代表单独证明完整树语义；回归应补上真实可实现上下文。
2. **只保留当前峰值最小的状态**：状态 `A=(4,4)` 当前峰值 4，`B=(0,8)` 当前峰值 8；未来费用 `(0,8)` 到来时，A 的最优配对峰值为 12，B 可交叉得到峰值 8。删掉 B 会删掉最终最优解。

固定精确边流与相同服务费时，一个已处理区域的全路线总费用固定。因此在相同语义组内，逐坐标费用支配经常只剩相等关系；不能未经证明就把一般 Pareto pruning 写成主要加速来源。C 的主要收益来自消除可交换路线标签，以及合并具有相同联合类型的配对。

### C.5 分阶段实施与复杂度承诺

| 阶段 | 工作与产物 | 建议 Lean 接口名，均待实现 | 验收 |
|---|---|---|---|
| C0：置换不变性 | 矩阵、边界状态和费用向量的整行作用 | `permuteRows`、`matrixValid_permuteRows_iff`、`rowCost_permuteRows` | 有符号费用与统一预算均覆盖 |
| C1：轨道表示 | 联合类型直方图、规范代表、payload 关系 | `JointRowType`、`OrbitState`、`normalizeOrbit`、`normalizeOrbit_sound` | 不独立排序相关字段；重复类型处理确定 |
| C2：join 内核 | 运输表枚举、相容性、合并及双射见证 | `TransportTable`、`transportTable_iff_relativePermutation`、`orbitJoin_sound`、`orbitJoin_complete` | 与全部相对排列比较，既不漏解也不加伪解 |
| C3：全 DP 与输出 | 接入根检查和最小预算；恢复可检查矩阵 | `solveOrbit`、`solveOrbit_feasible_iff`、`optimizeOrbit_value_eq`、`reconstructOrbitCert_valid` | 最小值相同、证书合法；旧 tie 不作为验收项 |
| C4：计费与收益 | 比较轨道数、运输表数、payload 重建、算术及内存成本 | 名称待 C3 实现后确定 | 成本模型明确；性能结论由数据支持，不从少几个key推断 |

若一个语义桶内联合类型字母表大小为 `d`，大小为 `m` 的直方图至多有

\[
\binom{m+d-1}{d-1}
\]

种。若左右实际不同类型数分别为 `a,b≥1`，固定边缘和的运输表至多有

\[
(m+1)^{(a-1)(b-1)}
\]

种，因为左上 `(a-1)×(b-1)` 个格子的取值决定其余格子；其中不少取值因负数、边缘和或不兼容性被拒绝。零路线和空类型集另行处理。

这些是枚举上界，不是紧界，也不是对二进制输入长度的多项式界。在 `m` 一元给定或把数值 `m` 计入规模的约定下，可以讨论相应类型参数的 XP 式枚举；在二进制 `m` 下，这类数值多项式界一般只是伪多项式，不能仅据此宣称 FPT，甚至不能仅据此宣称固定类型参数时关于位输入长度多项式。B 的上述推导说明，即使完全去掉标签，仍可有很多必要数值状态。A 目标中某个完整可行解的短表示，也不意味着 C 的全部中间状态表会短。

### C.6 回归族、成功标准与退出条件

未来本地回归和实验至少比较：

- 标签重复多、联合类型少的对称树族；预期显示状态和配对重复的减少。
- 几乎所有路线类型互异的反向族；报告规范化和运输表开销，而非只报告有利样例。
- 含负费用、负最优预算、费用并列、重复 row key 和 `m=0/1` 的已有回归。
- B 的五顶点分拆族，观察商表示确实合并排列，但不错误合并不同多重集。
- 上述两种错误算法的反例，以及相容性禁格、零格子和多种运输表对应同一输出直方图的情形。
- 原 DP 与商 DP 的可行性、最小预算相等；重建矩阵交给原检查器。证书字面不同必须允许。

记录输入二进制长度、`m,n,M`、不同联合类型数、标签状态/轨道状态数、运输表候选数、可接受 join 数、见证重建代价、峰值内存以及同环境墙钟时间。已证明的成本和实测时间分列，不相互代替。

C 的数学成功标准是完整 join 等价与全 DP 的 sound/complete/最优值保持。算法贡献还需说明在哪些结构参数或实例族上减少了工作；不能仅以实现了排序认定成功。如果全表运输枚举比旧方法更慢，先保留已验证的 join 内核，增加有证明的类型数门槛或回退选择；若收益只在对称实例出现，就明确声明适用范围。不得通过丢弃合法运输表来制造速度提升。

## 6. 原创性判断、文献对照与不作出的承诺

| 计划 | 已有通用思想 | 本项目应争取的具体新增结果 | 不能当作已证创新的内容 |
|---|---|---|---|
| A | 整数锥小支持、奇偶中点、凸格点和压缩见证 | 当前精确树流模型中两界同时成立；binary checker 与真实路线语义联结；表示差异进入 #21/#23 | 仅把一个通用锥定理改名；短证书等于快速求解或最优性短证明 |
| B | Myhill–Nerode 式补全等价、代表集和兼容矩阵 | 同一五顶点非负实例上固定逐路边界次数的单位矩阵；允许置换后仍有分拆下界；和充分性接口成对 | 任意算法、任意符号编码或指数存储位下界 |
| C | 群作用、直方图、运输表、treewidth DP 的类型计数 | 保留全部联合字段与整行见证的 verified quotient join；接入 signed exact-flow optimizer；明确收益条件 | 直方图或运输表本身首次出现；未经证明的 FPT、通用加速或旧 tie 完全一致 |

文献阅读起点（用于界定先例，不表示已经完成穷尽的 novelty search）：

- Eisenbrand–Shmonin，*Carathéodory bounds for integer cones*：[DOI](https://doi.org/10.1016/j.orl.2005.09.008)，A 的整数锥小支持背景；可访问的作者证明补充见 [Shmonin 2007 博士论文，第 5 章](https://www.epfl.ch/labs/disopt/wp-content/uploads/2018/09/Shmonin2007.pdf)。A 的输入盒界及奇偶势证明应直接写清假设，再逐项比较通用结果，不仅引用标题。
- Bodlaender、Cygan、Kratsch、Nederlof，*Solving weighted and counting variants of connectivity problems parameterized by treewidth deterministically in single exponential time*：[作者预印本](https://arxiv.org/abs/1211.1505)。其 representative-family 定义保留对未来补全的最优值；兼容矩阵低秩是另一个需要证明的条件，B 的单位子矩阵说明此处不能照搬普遍低秩压缩。
- Döring，IPEC 2025，Article 10：[论文](https://drops.dagstuhl.de/storage/00lipics/lipics-vol358-ipec2025/html/LIPIcs.IPEC.2025.10/LIPIcs.IPEC.2025.10.html)。其计数型边界描述及 fingerprint/bin-packing join 是 C 需要直接比较的先例；问题语义和参数不能仅凭“都是树路由”视为相同。
- 双陪集与 contingency tables 的联系是 C 的组合背景：[arXiv:2102.04576](https://arxiv.org/abs/2102.04576)。新增工作应落在当前证书、费用与 gluing 语义的精确保持。

提交论文或对外宣称“首次”前，应继续核验最贴近 exact multiplicities、convex integer row types、prescribed completion 和 quotient DP 的文献。若发现相同数学结论已有先例，应改成明确的特化/形式化贡献，并保留 checker、桥接定理或算法收益中确实新增的部分。

## 7. 交付、验收与任务关闭规则

三个新 issue 分别引用本文对应 A/B/C 节，保留各自的阶段清单，不用一个“创新提升”总 issue 混合全部验收。每个阶段交付：

1. 精确数学命题与适用假设；证明和反例写入可维护的理论笔记。
2. 复用现有语义的 Lean 接口；已实现与建议名称严格区分。
3. 针对边界和反例族的回归；只有实际运行后才记录结果、工具链及 commit。
4. 该阶段的公理审计和依赖说明；不得把其他模块的审计覆盖自动继承过来。
5. 若涉及成本或性能，区分抽象操作、位成本、地址执行模型与墙钟时间，写明测量环境。

阶段关闭以可检查结果为准，不以文档长度或新增定理数量为准。A 的存在性、B 的接口下界、C 的可组合商 join 可以分别成为完整成果；后续构造速度、标准机器成本或更一般模型不得无限延期已完成部分的收口。

本轮不新增时间窗、一般图、连续航迹、相关不确定性等模型。参数敏感性、signed-safe continuation cuts、进一步最优性反证证书可另立后续提案，待 A–C 的主命题与实际收益明确后再选择。
