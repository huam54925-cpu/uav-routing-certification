# 树上精确边流预算路由：文献核验与可推进的理论接口

检索日期：2026-11-18。研究分支：`research/structural-service-cuts-20261023`。本轮总任务核定的仓库基线：`f3ea0823be69ffa7152dec903069c2ba79ad20a4`。

本文是研究记录和待验证推导，不是新增 Lean 证明的完成报告。本文没有运行 Lean、Python 实验或冷启动构建；没有改变仓库既有定理的验证状态。数学推导、引用文献的算法结论、可执行代码、机器模型复杂度和编译后性能分别陈述。

## 1. 检索问题、范围和证据等级

本轮检索围绕四个问题展开：二进制访问重数是否必然要求巨大证书；已有单行矩阵语义能否接入整数锥算法；树上的结构参数怎样与已有装箱下界匹配；多重集、代表集与 rank-based 动态规划能为后续状态压缩提供什么，同时不能提供什么。

检索优先使用论文原文、作者机构保存的论文和会议出版页。检索词包括 `Caratheodory bounds integer cones Eisenbrand Shmonin`、`Goemans Rothvoss constant item types`、`high multiplicity bin packing FPT 2026`、`integer cone convex costs 2609.31328`、`Döring vehicle routing IPEC 2025`、`rank based weighted partitions Bodlaender Cygan Kratsch Nederlof`。这里列出的是可复查的检索范围，不宣称穷尽相关文献。

证据分为三类：

| 类别 | 本文含义 | 可以怎样表述 |
|---|---|---|
| 已发表文献结果 | 在原文中核对了模型、定理和必要假设 | 引用原作者及准确版本，不把结果计为本项目原创 |
| 新近预印本结果 | 已核对作者论文正文，但未视为完成同行评审 | 写明版本和检索日，明确依赖预印本 |
| 本轮模型推导 | 根据现有矩阵语义给出的归约、证明或接口设计 | 标为待 Lean 验证；不能写成仓库已经实现或证明 |

截至检索日，本轮取得的材料不足以证明“本项目首次提出”任何通用稀疏化、整数锥、运输表或代表集方法。论文贡献应落在精确模型的结构、形式化接口、构造性证书、可验证实现和必要的新定理，而不是依据关键词差异宣称首次性。

## 2. 当前问题必须固定的语义

设树根为 depot $o$，非根顶点集合为 $V^\circ$，$n=|V^\circ|$。每个非根顶点 $v$ 对应父边，给定精确重数 $H_v\in\mathbb N$。这里的精确边流不能改成边使用次数的上界。

车队有恰好 $m$ 条非空 depot excursion：路线从根出发返回根，内部不再出现根。重复经过非根顶点按每次访问计费；服务费和预算为有符号有理数。沿用仓库已有费用变换，将一条路线的费用写成

\[
C(p)=\sum_{v\in V^\circ}w_vp_v,
\]

其中 $p_v\in\mathbb N$ 是该路线在父边上的单向遍历重数。对父边双向遍历的计数约定必须与仓库已有路线—矩阵等价定理一致。

一个可行矩阵的行 $p^1,\ldots,p^m$ 满足：

1. 每列精确求和：$\sum_i p^i_v=H_v$。
2. 正支持向父亲闭合：当 $\operatorname{par}(v)\ne o$ 时，$p^i_v>0\Rightarrow p^i_{\operatorname{par}(v)}>0$。
3. 每行根孩子坐标和为 $1$：$\sum_{\operatorname{par}(v)=o}p^i_v=1$。
4. 每行费用 $C(p^i)\le T$。

非根坐标足以表达本文推导。若实现保留根坐标，应继续遵守已有根坐标归零的规范。把“给定访问需求”变换为 $H$ 时，仍需保留既有 `HasDegrees` 等前提，不能从本文件的固定 $H$ 结论跳过该层。

输入规模 $L$ 始终指树、$H,m,w,T$ 的总二进制编码长度。数值 $M=\sum_vH_v$ 或 $U=\max_vH_v$ 可以对 $L$ 指数大。显式路线的总移动数 $2M$ 因而可能是指数规模；这与短压缩证书存在不矛盾。

本文用 $n$ 表示全部非根顶点数，保留 $t$ 给仓库旧有正支持坐标参数，即正重数非根坐标数；本文不把新维数 $n$ 与旧 FPT$(t,U)$ 中的 $t$ 混用。若把新结论的参数从 $n$ 改为 $t$，必须先证零需求坐标删除或不可行拒绝保持语义；不能在父子闭包尚未核对前直接删掉零坐标的祖先。

配套 [LaTeX 草稿](TREE_ROUTING_RESEARCH_DRAFT_20261118_ZH.tex)已给出这一步的纸面版本：仅消去固定零坐标，所有父子约束仍按零扩展解释，正孩子遇到零父坐标仍会被拒绝。因此草稿写出较细的 $2^t$ 支持界及外部 FPT$(t)$ 推论；本说明与实施计划先保留按 $n$ 的通用表达。二者尚无本轮新增 Lean 验证。

## 3. 单行多面体：本轮推导的关键连接

定义有界有理多面体

\[
P_T=\left\{p\in\mathbb R^n:
\begin{array}{ll}
0\le p_v\le H_v &(v\in V^\circ),\\
p_v\le H_vp_{\operatorname{par}(v)}
  &(\operatorname{par}(v)\ne o),\\
\sum_{\operatorname{par}(v)=o}p_v=1,&\\
\sum_vw_vp_v\le T.&
\end{array}\right\}.
\]

该表达不引入 support 的二元变量。这里 $H_v$ 是输入常数，所以 $H_vp_{\operatorname{par}(v)}$ 对未知量仍是线性的。

**整数点等价的理由。** 在 $0\le p_v\le H_v$ 的前提下，若父坐标为零，不等式强制子坐标为零；若父坐标是正整数，则它至少为 $1$，已有上界 $p_v\le H_v$ 足以推出不等式。因而

\[
P_T\cap\mathbb Z^n
=\{\text{在预算 }T\text{ 下的合法单行模式}\}.
\]

此等价只要求整数坐标，不要求费用非负。不要把它说成所有实数点都具有离散的路线含义。添加常数坐标得到 $\widehat P_T=P_T\times\{1\}$，于是

\[
\operatorname{Feasible}(H,m,T)
\iff (H,m)\in\operatorname{int.cone}
       (\widehat P_T\cap\mathbb Z^{n+1}).
\tag{CONE}
\]

前向把相同行合并，反向按整数系数在数学上重复行，再用既有矩阵—路线定理。检查器不需要实际进行该重复。附加坐标 $1$ 是统一显式保留路线总数 $m$ 的方便编码，并非必须增加的一维：在已有 rootMass 守卫保证根孩子总重数等于 $m$ 时，每个模式根孩子坐标和为 $1$，列和关系即可推出总系数为 $m$，可复用 `pattern_count_total` 消去常数坐标。省略该坐标时应明确列出 rootMass 前提及此计数推导。

**适用范围。** 零路线时唯一空表示聚合为零，所以一般整数锥判定仍有定义；优化 API 应继续单独表达“全部预算可行”或“全部预算不可行”。正路线时若不存在合法模式，多面体没有整数点，并不会因线性松弛非空而得到可行证书。

## 4. Eisenbrand–Shmonin：双稀疏界和压缩证书

### 4.1 精确来源和原结果

[ES06] Friedrich Eisenbrand, Gennady Shmonin, *Carathéodory bounds for integer cones*, Operations Research Letters 34(5), 564–568, 2006，DOI [10.1016/j.orl.2005.09.008](https://doi.org/10.1016/j.orl.2005.09.008)。

原文 Theorem 1 给非负生成元的支持界 $\operatorname{size}(b)=\sum_j\log_2(b_j+1)$，以及一般整数生成元的 $2d\log_2(4d\Delta)$ 界，$\Delta=\max_{x\in X}\|x\|_\infty$。Theorem 2 对满足 $\operatorname{conv}(X)\cap\mathbb Z^d=X$ 的有限集合给 $2^d$ 支持界，并可保持原表示的总系数。

原论文 [EPFL 下载链接](https://infoscience.epfl.ch/bitstreams/57686095-3a21-4754-9525-80a75f08fe79/download)在此次抓取发生重定向失败；旧链接 `https://infoscience.epfl.ch/record/121640/files/conic.pdf` 也未成功打开。可直接访问的一手补充是作者 [Shmonin 2007 博士论文](https://www.epfl.ch/labs/disopt/wp-content/uploads/2018/09/Shmonin2007.pdf)：第 5 章明确源自 ES06；Theorems 5.1、5.2、5.3 分别重述上述三类界，并给出证明。印刷页 52、54–55 对应 PDF 页码约 60、62–63。

### 4.2 本模型映射和可自含证明的目标

压缩证书为不同模式及正整数重数

\[
\mathcal C=\{(p^j,\lambda_j):1\le j\le k\},\qquad
p^j\in P_T\cap\mathbb Z^n,
\quad\sum_j\lambda_j(p^j,1)=(H,m).
\]

**目标 A1：**存在证书满足

\[
2^k\le(m+1)\prod_v(H_v+1).
\tag{A1}
\]

取支持数最小的表示。其每个支持子集的增广向量和都在整数盒 $\prod_v[0,H_v]\times[0,m]$ 内。若子集数多于盒内点数，两子集同和；消去交集后，在一边减去该边最小系数、另一边加回同一系数，聚合量不变且支持严格缩小，矛盾。常数坐标保证等和的两边均非空。这是 ES 非负情形在本模型上的直接专门化，而非新的整数锥定理。

**目标 A2：**存在证书满足 $k\le2^n$。在所有可行矩阵中最小化 $\sum_i\|p^i\|_2^2$。若不同模式超过奇偶类数，有不同的 $p,q$ 坐标同奇偶。用两份整数中点 $r=(p+q)/2\in P_T$ 替换它们，保持聚合量和行数；费用是原两费用的平均，仍不超过 $T$，而平方势严格减小。此论证也适用于负费用。

两个存在性证明不一定选到同一个证书。最后选择全体可行证书中支持数最小者，才可同时写成

\[
k\le\min\left\{2^n,
\left\lfloor\log_2\left((m+1)\prod_v(H_v+1)\right)\right\rfloor\right\}.
\tag{SPARSE}
\]

形式化时可先避免实数对数，使用

\[
B_H=\operatorname{Nat.size}(m)+\sum_v\operatorname{Nat.size}(H_v),
\qquad k\le\min\{2^n,B_H\}.
\]

### 4.3 差异、可用结论和不能直接声称的内容

虽然 $w_v$ 可以负，增广生成向量 $(p,1)$ 全非负，因此不能因“有符号服务费”而误排除 A1。A2 利用的是合法模式的整数凸结构；任意历史残余状态集合不一定满足该条件，不能未经证明把同一平滑压缩用于 DP 中间表。

从 A1 可知 $k=O(L)$。每个 $p_v\le H_v$、每个重数 $\lambda_j\le m$，故存在 $O(L^2)$ 位的压缩可行证书。仓库 `TreeBudgetCertificate` 已有 `Certificate`、`checkCertificate` 及 soundness/completeness，且检查不展开 $m$ 条路线；应复用这些接口和已证语义，不重新制造一套检查器。新增工作是短证书存在性、二进制编码/解析精化、输入与证书位宽上界，以及现有检查步骤的多项式位时间。数学长度界本身仍不是标准机器模型中的 NP 成员性证明。

不能由 SPARSE 推出存在多项式时间求解器。把 $p^j$ 和 $\lambda_j$ 同时作为未知量会产生双线性项 $\lambda_jp^j$，并非直接得到 Lenstra 可解的固定维线性整数规划。也不能因此得到所有不可行实例或最优性的短独立证明。

压缩证书通常更改模式，因而不承诺与旧 `solve` 在 tie-breaking 下选中的矩阵相同。应保留原有精确顺序见证 API，复用已有 `Certificate`/`checkCertificate` 表达不同的合法压缩解；只为新的二进制序列化及最优值连接补充必要精化，不重复包装已有 soundness/completeness。

## 5. Goemans–Rothvoß：稳定的 XP 基线

### 5.1 精确版本与原结果

[GR14/20] Michel X. Goemans, Thomas Rothvoß, *Polynomiality for Bin Packing with a Constant Number of Item Types*。会议版 SODA 2014，830–839，DOI [10.1137/1.9781611973402.61](https://doi.org/10.1137/1.9781611973402.61)；期刊版 JACM 67(6), Article 38, 2020，DOI [10.1145/3421750](https://doi.org/10.1145/3421750)。本轮逐条核对的是 [SODA 完整论文](https://ethz.ch/content/dam/ethz/special-interest/math/operations-research/ifor-dam/documents/Polynom.pdf) 的 Theorem 2.2。

该定理对有界有理生成多面体 $P\subseteq\mathbb R^d$ 与目标多面体 $Q$ 求解整数锥交问题，时间

\[
\operatorname{enc}(P)^{2^{O(d)}}
\operatorname{enc}(Q)^{O(1)},
\]

并输出至多 $2^{2d+1}$ 个生成元的整数表示，或报告不存在。

### 5.2 本模型映射

在 CONE 中取 $P=\widehat P_T$、$Q=\{(H,m)\}$、$d=n+1$。所有定义不等式的数量和二进制长度均对输入为多项式。费用有符号不违反“有理多面体”假设；坐标上界 $H$ 提供所需有界性。

**可用：**得到本模型按 $n$ 参数化的压缩输出 XP 算法推论，为后续新近 FPT 结果提供稳定的已发表基线。

**不能直接声称：**XP 不是 FPT；指数含 $n$ 的 $L^{f(n)}$ 与 $f(n)L^c$ 不可混写。也不能把文献使用的几何算法视为已在 Lean 验证，或把其运行时等同于仓库已有地址存储执行器的成本。该推论本身是既有框架的应用，不是本项目发明的通用整数锥算法。

## 6. 2026 预印本：FPT 图景已经更新

### 6.1 Koana–Kumabe 的装箱结果

[KK26] Tomohiro Koana, Soh Kumabe, *High-Multiplicity Bin Packing is FPT*, [arXiv:2609.16923](https://arxiv.org/abs/2609.16923)，v1 提交于 2026-09-15。本轮搜索取得作者摘要；arXiv PDF/HTML 母站抓取失败，未逐节审阅该文完整证明。

摘要给二进制物品大小和重数下，按类型数 $d$ 的确定性 $O^*(2^{d^{O(d)}})$ 算法，并描述按坐标模 $d$ 分类、整数分解性质以及至多 $(d+1)d^d$ 个变量的 ILP。

**映射：**非负增量费用的严格 hub 模型可以映射为高重数装箱。**不能直接推广：**该摘要的装箱定理不自动覆盖任意树支撑闭包和负费用；一般树应使用下一项更一般的整数锥结果。检索日后不能再把“按物品类型数的高重数装箱 FPT”当作尚无人解决的问题。

### 6.2 Jansen–Ohnesorge–Schumacher v5 的完整结果

[JOS26] Klaus Jansen, Felix Ohnesorge, Björn Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs*, [arXiv:2609.31328v5](https://arxiv.org/abs/2609.31328v5)，2026-11-03。原始编号 v1 的标题为 *An ETH-Tight, Constructive FPT Algorithm for the Cone and Polytope Intersection Problem*，作者列表与 v5 不同；引用本轮使用结果时必须使用 v5 的标题、三位作者及版本。

母站 arXiv 的 abs/PDF/HTML 在本轮部分请求中无法抓取。正文核验使用 [作者原论文 PDF 的镜像](https://arxiv.cnoctave.top/pdf/2609.31328)，共 41 页，其首页标示 v5 和 2026-11-03。这里使用的是论文正文，不是镜像网站生成的解释性摘要；但下载出处和预印本状态应保留在记录中。

Theorem 1（正文 p4）覆盖多个有界有理生成多面体、整数/连续坐标、给定凸成本和聚合线性约束。本文只需要其最简单特例：一个生成类型、没有连续坐标、恒零成本。正文 p3 明确允许精确指定生成元个数 $m$，输入数值为二进制；结果构造整数重数和每类型至多 $2^{2d+1}$ 个生成元。单类型时间为

\[
2^{2^{O(d)}}|I|^{O(1)}.
\]

### 6.3 本模型映射与声明边界

将 CONE 的 $d=n+1$ 代入，可得到压缩输出的 $2^{2^{O(n)}}L^{O(1)}$ 判定/构造算法推论。也可直接使用文中的精确生成元计数约束，保留 $n$ 个模式坐标；两种写法不改变渐近分类。

这里每条路线费用不作为文中待最小化的凸目标，而是先放进 $P_T$ 的线性预算约束；文中成本取零。因此不存在需要假设“有符号服务费构成凸总目标”的额外步骤。

若 $m>0$，令共同分母 $D>0$、$a_v=Dw_v\in\mathbb Z$、$B=\sum_v|a_v|H_v$。可行时最小预算在 $D^{-1}\mathbb Z\cap[-B/D,B/D]$。先检查上端点，再在整数区间 $[-B,B]$ 二分，调用次数对二进制输入为多项式；$B=0$ 单独简化即可。于是最小预算和任意一份压缩最优解也有对应 FPT 推论。

**可以写：**“通过精确多面体编码，应用 v5 预印本得到本模型的 FPT 推论；本项目计划形式化归约和已有证书接口的二进制精化。”

**不能写：**“本仓库已证明/实现这一 FPT 算法”“本项目首创此双指数 FPT 方法”“全部 budget profile 可以在相同界内显式输出”。旧 profile 保留原表顺序与完整见证，其所有断点的输出规模需要独立分析。

## 7. 复用已有根分支分解，推出新的参数推论

仓库已在 2026-11-02 的 `docs/TREE_BUDGET_ROOT_FACTORIZATION_STATUS.md` 中记录根分支分解；现有接口包括 `pattern_unique_roon_child`、`pattern_branch_equiv`、`pattern_counts_iff_local_counts`、`matrix_iff_branch_matrices`、`zero_branch_iff` 和 `branchMultiplicity`。这些是已有成果，不能列为本轮新结构定理。下述结构事实用于说明这些接口与新的参数推论如何连接。

一条 excursion 的根孩子坐标和是 $1$，且正支持祖先闭合，因此它只能进入一个根分支。若根孩子为 $c$，属于该分支的路线数必须为 $m_c=H_c$。故必要条件为 $m=\sum_cH_c$，且在该条件下，总体可行性分解为各根分支在同一预算下分别可行。

设分支 $c$ 含 $n_c$ 个非根顶点，$k=\max_cn_c$。应用整数锥算法可以按分支分别求解，使参数从总数 $n$ 换为最大根分支规模 $k$，时间总和仍为 $2^{2^{O(k)}}L^{O(1)}$。若所有相关分支都有可行解，正路线情形的最小预算是各非空分支最小预算的最大值。

同一分支的根孩子坐标恒为 $1$，其他根分支坐标恒为零，所以奇偶类计数可从 $2^n$ 收紧到 $\sum_c2^{n_c-1}$。本轮候选增量是将新的稀疏界与整数锥参数推论接到上述已有接口，而不是重新证明并包装根独立分解。零路线、零需求分支和非法祖先支持仍应复用已有边界结论逐项覆盖。

## 8. ICALP 2026 与 ESA 2025：正确表达条件下界

### 8.1 原结果

[JOP26] Klaus Jansen, Felix Ohnesorge, Lis Pirotton, *A Tight Double-Exponential Lower Bound for High-Multiplicity Bin Packing*, ICALP 2026, LIPIcs 374, 116:1–116:20，2026-07-01，DOI [10.4230/LIPIcs.ICALP.2026.116](https://doi.org/10.4230/LIPIcs.ICALP.2026.116)。本轮核对 [正式 PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/LIPIcs.ICALP.2026.116/LIPIcs.ICALP.2026.116.pdf) Theorem 3（p3）：除非 ETH 失败，高重数装箱不存在 $|I|^{2^{o(d)}}$ 时间算法。紧接的正文明确讨论由此得到的 FPT 双指数参数障碍。HTML 元数据会丢失嵌套上标，引用公式应以 PDF 为准。

[JPT25] Klaus Jansen, Lis Pirotton, Malte Tutas, *The Support of Bin Packing Is Exponential*, ESA 2025, LIPIcs 351, 48:1–48:16，DOI [10.4230/LIPIcs.ESA.2025.48](https://doi.org/10.4230/LIPIcs.ESA.2025.48)。[正式出版页](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2025.48)说明所需模式支持可达 $2^{\Omega(d)}$。这排除了把一般模式支持界期待为 $\operatorname{poly}(d)$ 的方向。

### 8.2 到严格 hub 的参数保持映射

给定 $d$ 种物品的正整数大小 $s_j$、二进制重数 $a_j$、箱容量 $B$ 和箱数上限 $b$，构造根—hub—$d$ 个叶子的树：

\[
H_{\mathrm{hub}}=b,\quad H_j=a_j,\quad m=b,
\qquad s(\mathrm{hub})=0,\quad s(j)=s_j,\quad T=B.
\]

每条路线的 hub 坐标恒为 $1$，费用为所装物品大小之和。至多 $b$ 箱的装箱可以用 hub-only 路线补成恰好 $b$ 条非空 excursion；这些路线在图上非空，且预算内费用为零。反向读取叶坐标得到装箱。注意这里只使用 $B>0$ 的标准装箱输入，不能把“可补空箱”推广到任意负预算场景。

映射有 $n=d+1$，二进制长度增加多项式量。因此，在完成该归约的语义与编码长度证明后，可把相关参数下界转移到本模型，且已发生在高度为 $2$ 的树上。树高或树宽单独不是这里有用的求解参数。

### 8.3 推荐措辞与禁止跳步

推荐：“在 ETH 假设下，经参数保持的严格 hub 归约，本问题不能具有 $2^{2^{o(n)}}L^{O(1)}$ 时间算法；结合新近整数锥预印本，双指数参数依赖具有相应的条件性匹配。”若论文主定理只写稳定已发表结果，则先给 XP 基线和单独的条件下界，再将 FPT 更新列为预印本推论。

不要写“任何 FPT 函数逐点都满足 $f(n)\ge2^{2^{cn}}$”；复杂度下界的量词是排除指定渐近运行时类。也不要从 #23 的普通 3-PARTITION 归约直接宣称获得上述 ETH 参数下界：需要本节的高重数装箱归约和被引用文献的精确假设。预印本提到的更弱假设 `NP ⊈ SUBEXP` 不作为本轮默认主张；若采用，须一并写清其 SUBEXP 定义及单独的推导。

## 9. Döring 等：借鉴多重集 DP，不能搬运去重边引理

### 9.1 原结果与版本

[DF+25] Michelle Döring, Jan Fehse, Tobias Friedrich, Paula Marten, Niklas Mohrin, Kirill Simonov, Farehe Soheil, Jakob Timm, Shaily Verma, *Parameterized Complexity of Vehicle Routing*, IPEC 2025, LIPIcs 358, 10:1–10:17，DOI [10.4230/LIPIcs.IPEC.2025.10](https://doi.org/10.4230/LIPIcs.IPEC.2025.10)。本轮核对 [正式全文 HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol358-ipec2025/html/LIPIcs.IPEC.2025.10/LIPIcs.IPEC.2025.10.html)，其完整长版链接为 [arXiv:2509.10361](https://arxiv.org/abs/2509.10361)。

论文处理非负整数边费用、客户分配、至多给定车辆数和可能多个 depot。Theorem 3.9 给无容量 VRP 的树宽 FPT；Theorem 4.8 给容量版本按车辆数参数化的 W[1]-hardness，即使单位需求、单位边权、单 depot 且底图为树。§4.4 按路线特征计数，Definition 4.18 / Theorem 4.19 用异质多维 fingerprint 装箱组织组合；后续容量算法是相应参数下的 XP。

### 9.2 到本模型的映射、差异和可用部分

可借鉴的是“多个部分路线按共同特征形成多重集，再通过满足约束的匹配/装箱组合”的算法接口。这为本项目的行类型商、计数表和联结阶段提供具体先例，所以“把有标签行改成无标签计数”本身不能作为全新思想。

关键差异是精确 $H$、每次重复访问收费、有符号费用、恰好 $m$ 条不内部经过根的 excursion。该文减少边重复次数的 Lemmas 3.7/4.17 改变边使用量；在本模型会破坏 $H$，且负费用下删除访问也可能使预算条件变差。因此不能直接采用其删两份边、边重数至多二、非负费用剪枝结论。

其复杂度分类不自动成为本问题分类：树宽 FPT 对应无容量模型，而本模型仍包含高度二的装箱难例。文章对“多个最终连通分量”和“单一连通完成条件”的区分，也提醒后续代表集压缩必须先定义正确的未来完成关系。

## 10. Rank-based 代表集：先证未来等价，再谈低秩

### 10.1 原结果与准确出处

[BCKN15] Hans L. Bodlaender, Marek Cygan, Stefan Kratsch, Jesper Nederlof, *Deterministic single exponential time algorithms for connectivity problems parameterized by treewidth*, **Information and Computation** 243, 86–111, 2015，DOI [10.1016/j.ic.2014.12.008](https://doi.org/10.1016/j.ic.2014.12.008)。这篇文章不是 JACM 论文。

已核对 [TU/e 保存的期刊作者版本](https://pure.tue.nl/ws/portalfiles/portal/57608658/journaldeterministic_complete.pdf) 的 Definitions 3.4–3.5、Lemma 3.6、Theorem 3.7；相关早期版本为 [arXiv:1211.1505](https://arxiv.org/abs/1211.1505)。其代表性要求对每个未来分划 $q$，完成为一个连通块时的最小权重保持不变。`reduce` 给出小代表子集，且列出的若干 DP 操作保持这种代表性。

### 10.2 本模型映射和不能搬用的界

本项目可以先定义未来语义，例如

\[
A\equiv_{\mathrm{future}}B
\iff\forall E\in\mathcal E,
\operatorname{Answer}(A,E)=\operatorname{Answer}(B,E),
\]

其中环境 $E$ 必须包括合法剩余边流、支撑兼容、路线配对、预算及所需见证选择规则。定义代表集后，应逐个证明 union、孩子合并、根守卫等操作保持该关系，再研究兼容矩阵是否有可用秩界。

论文的 $2^{|U|-1}$ 代表集界来自特定分划连通矩阵的代数结构。本项目的逐路线数值资源、精确残余向量和 signed 费用并非同一矩阵，不能因为出现“树 DP”就直接获得该界。当前只有总访问量、总费用、当前最大负载等粗摘要通常不足；应利用已有分离反例或新构造明确刻画不可合并的状态。

论文代表性通常保最优数值。要保留本仓库原 solver 的第一份或最后一份并列见证，还需把顺序信息纳入答案语义。没有这一步，数值正确不等于完整证书逐字相同。

## 11. 后续算法包：联合类型和运输表的可研究接口

这一节是待验证设计，不是从前述文献直接获得的定理。左右子树的行类型必须联合包含支撑/边界元数据和负载，不可把结构与费用分别排序。设左、右类型重数为 $\mu_a,\nu_b$，可用非负整数运输表 $N_{ab}$ 表达相对配对：

\[
\sum_bN_{ab}=\mu_a,\qquad
\sum_aN_{ab}=\nu_b,\qquad
\neg\operatorname{Compat}(a,b)\Rightarrow N_{ab}=0.
\]

值得证明的接口是“存在这样的表，当且仅当存在相对置换实现兼容配对”，并从表构造整行子矩阵的双射提升。该存在性通常是经典运输表/双陪集现象的专门化；创新评价要落在本项目的语义、可执行提升和计费收益。

两项直接背景也收入草稿参考文献：Kaibel–Pfetsch 的 [Packing and Partitioning Orbitopes](https://arxiv.org/abs/math/0603678)研究置换作用下的规范矩阵代表；Diaconis–Simper 的 [Statistical Enumeration of Groups by Double Cosets](https://arxiv.org/abs/2102.04576)明确讨论对称群抛物子群双陪集与列联表的对应。这两项原作者页面的题名、作者与摘要已核对，本文只用作方法归属，不声称借此取得本项目的 DP 正确性或性能定理。

不能只把左右负载排序后同序相加：$(0,10)$ 与 $(0,10)$ 同序合并峰值为 $20$，交叉配对则为 $10$。也不能只保当前峰值最小的状态：$(4,4)$ 的当前峰值优于 $(0,8)$，但与后续 $(0,8)$ 配对后的最佳峰值分别为 $12$ 和 $8$。

若左右分别有 $a,b$ 类，边际固定的表由左上 $(a-1)(b-1)$ 个条目确定，粗界为 $(m+1)^{(a-1)(b-1)}$。这可减少显式排列枚举，但仍依赖 $m$ 的数值，不能据此声称关于类型数的二进制 FPT。需在具体实例上证明类型数或表的有效状态数下降，并明确成本包括类型生成、枚举、验证和见证恢复。

## 12. 建议的交付顺序及验收边界

本表按研究主题列出依赖和验收，不另设阶段编号；实施阶段以主路线图为准。

| 主题 | 数学验收 | 工程/形式化验收 | 不应扩大为 |
|---|---|---|---|
| 模式多面体接口 | 合法行 iff 整数点；CONE 双向 | 连接既有矩阵、费用公式和 rootMass 计数接口 | 已验证通用 ILP 求解器 |
| 子集和稀疏界 | 支持最小表示的整数盒界 | 有限支持交换与编码长度前提 | 高效找到最小支持解 |
| 奇偶稀疏界 | 整数中点平滑与平方势；两界同时成立 | 与已有矩阵语义连接 | 任意 DP 中间表可同样平滑 |
| 二进制证书精化 | 短证书存在，长解无需展开 | 复用 Certificate/checkCertificate 的 soundness/completeness；只补编码、解析和精化 | 重新实现或重新命名已有检查器 |
| NP 位复杂度闭合 | $O(L^2)$ 证书长度 | 对既有检查过程证明多项式位时间并选择明确机器模型 | 仅凭小例枚举宣布标准 NP 定理 |
| 参数复杂度图景（后续独立项） | GR 的 XP、JOS26 的 FPT 推论、hub 下界映射 | 形式化归约；外部算法依赖列明 | 自创或已形式化整套 FPT 算法 |
| 未来接口及下界 | 区分未来可区分状态；证明安全等价 | 接已有残余向量反例、signed 条件 | 套用别的问题的 rank 界 |
| 类型商与匹配提升 | 运输表—相对置换等价、完整证书提升 | 与原 DP 对照，另计生成和恢复开销 | 数值多项式枚举自动成为二进制 FPT |

现有 #19 的 ordered root table、预算 profile、breakpoint 必要性和实际 route output 为语义基线。二进制精化应复用已有 Certificate/checkCertificate，明确允许不同的合法证书，但保相同可行性和最小预算。现有 #22 的地址计费模型和 #19 的标量/堆模型不能仅因新增数学归约而自动统一。现有 #23 的 3-PARTITION 语义与编码结果可复用，但完整语言分类仍需与二进制 checker 和标准复杂度定义对接。

近期最小可审查结果是模式多面体接口和两种稀疏界：它们提供结构性接口和自含短证明，且不依赖实现整个几何整数锥算法。随后通过既有检查器的二进制精化与位复杂度补齐可认证性闭环；参数图景是后续独立项。未来接口和类型商方向应以反例、严格语义和可测的状态减少为继续投入的条件。

## 13. 主要风险与合稿检查表

- **首次性风险：**ES 稀疏化、GR 整数锥、2026 FPT、运输表和分划代表集均有既有文献。应区分“本模型推论”“新形式化证明”“新算法结构”和“通用原创定理”。
- **版本风险：**2609.31328 在 v5 已改标题和作者；以检索日版本为准，提交前再次核对。不要用旧摘要代替实际引用的 v5 假设。
- **模型风险：**精确边流、重复访问、有符号费用、非空路线及内部 depot 限制是核心语义，不能在与 CVRP 比较时省略。
- **量纲风险：**本文 $n$ 是全部非根顶点数，$t$ 保留为仓库旧有正支持坐标数，装箱 $d$ 是类型数，根分支参数 $k$ 是最大分支规模；新维数结论不能不加说明地写成旧 FPT$(t,U)$ 的改进。
- **编码风险：**$\operatorname{poly}(m,U)$ 不等于 $\operatorname{poly}(L)$。大重数证书必须直接检查，不应偷偷展开路线或矩阵。
- **证明状态风险：**本文件包含待验证推导，不能添加到“已编译无 sorryAx 定理”清单。证明接口签名也不是完成的 Lean 证明。
- **语义保持风险：**压缩解和代表集可能保值而不保 tie-breaking；完整旧证书相等需要更强的不变量。
- **下界风险：**只使用具有明示参数保持和多项式二进制长度的归约；避免把 ETH 下界写成无条件下界或逐点函数比较。
- **实验风险：**本轮没有实验。理论稀疏性不保证现有 solver 自动发现稀疏解，也不保证墙钟时间改进。
- **发表风险：**文献检索和严密推导能确定研究方向，不能保证论文录用或通用首次性。投稿主张应以最终实现、证明和比较结果为准。

## 14. 可复查参考文献索引

1. **[ES06]** Eisenbrand, Shmonin. *Carathéodory bounds for integer cones*. ORL 34(5), 2006. [DOI](https://doi.org/10.1016/j.orl.2005.09.008)。可访问的作者证明补充：[Shmonin 2007 thesis, Chapter 5](https://www.epfl.ch/labs/disopt/wp-content/uploads/2018/09/Shmonin2007.pdf)。
2. **[GR14/20]** Goemans, Rothvoß. *Polynomiality for Bin Packing with a Constant Number of Item Types*. [SODA 2014 PDF](https://ethz.ch/content/dam/ethz/special-interest/math/operations-research/ifor-dam/documents/Polynom.pdf)；[JACM 2020 DOI](https://doi.org/10.1145/3421750)。
3. **[KK26]** Koana, Kumabe. *High-Multiplicity Bin Packing is FPT*. [arXiv:2609.16923](https://arxiv.org/abs/2609.16923), v1, 2026-09-15；本轮核验限作者摘要。
4. **[JOS26]** Jansen, Ohnesorge, Schumacher. *A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs*. [arXiv:2609.31328v5](https://arxiv.org/abs/2609.31328v5), 2026-11-03；本轮已读的[原论文镜像 PDF](https://arxiv.cnoctave.top/pdf/2609.31328)。
5. **[JOP26]** Jansen, Ohnesorge, Pirotton. *A Tight Double-Exponential Lower Bound for High-Multiplicity Bin Packing*. [ICALP 2026 DOI](https://doi.org/10.4230/LIPIcs.ICALP.2026.116)；[正式 PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/LIPIcs.ICALP.2026.116/LIPIcs.ICALP.2026.116.pdf)。
6. **[JPT25]** Jansen, Pirotton, Tutas. *The Support of Bin Packing Is Exponential*. [ESA 2025 DOI](https://doi.org/10.4230/LIPIcs.ESA.2025.48)。
7. **[DF+25]** Döring, Fehse, Friedrich, Marten, Mohrin, Simonov, Soheil, Timm, Verma. *Parameterized Complexity of Vehicle Routing*. [IPEC 2025 DOI](https://doi.org/10.4230/LIPIcs.IPEC.2025.10)；[正式 HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol358-ipec2025/html/LIPIcs.IPEC.2025.10/LIPIcs.IPEC.2025.10.html)。
8. **[BCKN15]** Bodlaender, Cygan, Kratsch, Nederlof. *Deterministic single exponential time algorithms for connectivity problems parameterized by treewidth*. Information and Computation 243, 2015. [DOI](https://doi.org/10.1016/j.ic.2014.12.008)；[作者期刊版本 PDF](https://pure.tue.nl/ws/portalfiles/portal/57608658/journaldeterministic_complete.pdf)；[早期 arXiv](https://arxiv.org/abs/1211.1505)。

本索引未把普通搜索摘要、自动生成的论文解释页或聚合书目当作技术定理依据。新的数学推导和路线图应在后续提交中分别增加证明位置、检查器接口、编译记录和实验记录，而非修改这里的历史检索状态。
