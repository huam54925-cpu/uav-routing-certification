# 树预算路由：从信息充分性走向精确子树算法

**日期：2026-11-13（Asia/Tokyo）**  
**分支：research/structural-service-cuts-20261023**  
**源码核对基线：** [ca92c6c](https://github.com/huam54925-cpu/uav-routing-certification/commit/ca92c6c17e9eda26f89044f65399515380235da6)  
**性质：** 定向文献检索、模型对照与研究计划。候选递推是基于现有矩阵定理的纸面设计，尚无新增 Lean 定理、算法实现、有限枚举验证或性能结论。不是系统性查新或“首次提出”声明。

## 1. 这次调整的研究重点

“树上的路由已有大量研究”不等于“所有树路由模型都已解决”。图结构之外，精确访问次数、是否固定边流、逐路线资源、可否拆分需求、数值编码、车辆数和输出形式都会改变问题。2022、2025 年的树 CVRP 近似结果及 2025 年的参数化分类说明这个方向仍有具体问题在推进；也要求我们认真对照已有方法，而不能仅凭改变一个约束就宣布创新。

本项目的推进可以理解为：从一般路线与边流中识别丢失的信息，在明确的结构假设下寻找等价表示，再利用可重建的表示设计算法。**树支持是一个明确的模型限制；现有工作没有把任意原始网络无损、有效地转成树问题。** 树内的路线—矩阵 iff 与一般图到树的归约不是同一个结论。

若近期目标是提高精确求解能力，建议把 **#19 的状态语义、递推和见证重建** 作为主线。#23 的机器成本是另一条有价值的理论工作，不必先完成它才能研究 #19。此前“先完成 #23 成本”的建议适用于收拢复杂度证明链的目标；本次按“继续数学结构并发展精确算法”的目标调整优先级。

可评估的贡献应具体落在以下至少一项：更充分且更小的状态、闭合的递推和双向证明、可执行重建、严格受限模型上的状态/时间界，或有模型一致性保障的实际性能提升。仅有程序自动运行或新增代码行数不构成这些结论。

## 2. #19、#23 与自动化程序分别做什么

| 对象 | 输入、输出与数学问题 | 不能混同的结论 |
| --- | --- | --- |
| #19 子树接口与精确算法 | 部分矩阵/游程如何表示，哪些状态可实现，怎样合并并重建全局解 | 给定见证能拼接，不等于任意摘要可实现；状态有限，不等于状态少 |
| #23 归约 | reduceBits 把源实例变成目标实例，保持 YES/NO 答案 | 归约不会求出三划分，也不会搜索目标路线 |
| #23 证书验证 | 给定目标与分配，检查是否构成可行见证，并分析证书长度及检查成本 | 容易检查一个解，不表示容易找到解 |
| 搜索器/优化器 | 从实例自动寻找矩阵、分配或路线；失败结论需要完备性或其他证明 | 超时、没有找到解、外部软件报告无解，不自动成为 Lean 不可行性定理 |
| #22 执行精化 | 既有完整搜索对应实际存储、算术和所选收费模型 | 其模型内已证结果不是待补漏洞；标准机器模拟是进一步扩展 |

#23 不能概括为“对现有算法修修剪剪”。它研究的是**问题之间的难度联系，以及归约/验证程序的真实计算成本**。它有助于限定哪些普遍高效目标合理，但不会证明当前搜索算法最优，也不排除特殊参数算法、状态压缩或工程加速。

证书和算法可以协作：算法产生证书，检查器认证证书；它们仍是不同的数学任务。外部求解器产生候选见证是可选工程路径；#19 则可以进一步产生一个本身具有正确性与完备性证明的搜索器。

## 3. 文献选择与核对深度

围绕“子树状态—精确合并—压缩—重建”进行定向检索，优先使用论文正文、出版机构、作者或研究机构页面。只读到摘要或出版预览的文献明确标记，不据此断言其全部假设和证明已经核验。“借鉴/限制”是本项目的分析，不是作者对本模型的结论。

| 编号 | 文献 | 本次核对范围 | 优先用途 |
| --- | --- | --- | --- |
| R1 | Xu, Zhang, Hu, Guo (2021)，固定 k 的树上 k-depot CVRP | 出版社正文选段：模型、§2、Theorem 1、结论 | 状态定义与拆分/合并正确性 |
| R2 | Döring 等 (2025)，Parameterized Complexity of Vehicle Routing | 出版社 HTML：§4.4、Definitions 4.18/4.21、Join、Theorem 4.24 | 多段边界行为、类型和资源一起保存 |
| R3 | Xu, Xu, Xu (2013)，树上 min–max k-TSP | 出版社检索可见摘要/正文预览、R1 原文引用；全文直开受限 | 更接近逐路线预算的精确 DP |
| R4 | Bodlaender, Cygan, Kratsch, Nederlof (2015)，rank-based DP | 机构正文选段：§3.2，Definitions 3.4–3.5、Lemma 3.6、Theorem 3.7 | 保留外部可扩展性的代表集 |
| R5 | Brandão, Pedroso (2016)，压缩 arc-flow 装箱模型 | 作者项目页、摘要及接受稿正文入口 | 隐式表示模式集合，区别于输出去重 |
| R6 | Mbaraga, Langevin, Laporte (1999)，树路由精确算法 | GERAD 技术报告摘要及出版社目录 | 装箱下界、列生成等传统精确方法 |
| R7 | Mathieu, Zhou (2022)，树 CVRP PTAS | 出版社摘要与书目信息 | 区分精确判定和近似优化 |
| R8 | Mathieu, Zhou (2025)，不可拆分树 CVRP 近似 | 作者机构出版记录与摘要 | 同为树仍有不同模型和进展 |
| R9 | Cheung, Gleixner, Steffy (2017)，整数规划结果验证 | 作者报告正文选段：§1、§4、结论 | 求解与独立证书检查的分工 |
| R10 | You, Yang (2026)，RouteOpt | 作者论文页、期刊摘要与资源入口 | 工程候选，非本模型直接可用算法 |

### R1：流状态的精确定义比“树上 DP”这个名称更重要

Liang Xu, Tong Zhang, Rantao Hu, Jialing Guo, *A Polynomial-Time Exact Algorithm for k-Depot Capacitated Vehicle Routing Problem on a Tree*, Mathematical Problems in Engineering, 2021, 6648044。  
[DOI](https://doi.org/10.1155/2021/6648044) · [出版社全文](https://onlinelibrary.wiley.com/doi/10.1155/2021/6648044)

论文研究固定车辆/车库数、可拆分需求经单位客户表示后的最小总路长问题；Theorem 1 声明 $O(nQ^k)$。它采用流枚举和流拆分的 DP，且明确指出该方法不能直接用于 min–max 目标。

**借鉴：** 分别说明状态代表什么、子状态如何产生父状态、如何恢复解。  
**限制：** 我们约束精确访问和固定边流，每次经过任务点都计费；其 n、Q、目标和服务含义不能照搬。二进制重数不能免费展开为单位客户。树的二叉化会改变新增顶点的访问/服务账目，本项目宜先逐个合并孩子，避免未经证明地插入虚拟点。

### R2：多次切换与资源分配必须同时进入合并条件

Michelle Döring 等, *Parameterized Complexity of Vehicle Routing*, IPEC 2025, Article 10。  
[出版页](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.IPEC.2025.10) · [全文](https://drops.dagstuhl.de/storage/00lipics/lipics-vol358-ipec2025/html/LIPIcs.IPEC.2025.10/LIPIcs.IPEC.2025.10.html) · [完整版本](https://arxiv.org/abs/2509.10361)

§4.4 保存边界游走的端点、资源及相关类型；Join 允许父层游走在子区域之间多次切换，并用带 fingerprint 的广义装箱组织组合。Theorem 4.24 的 XP 结论针对其树宽和容量参数。

**借鉴：** 匹配对象不应只有费用，还要包含参与合并的结构身份。  
**限制：** 其 Lemma 4.17 删除重复边的简化不能直接用于我们的固定精确边流/访问次数任务。我们的边重数是约束，不是可任意删去的冗余。文献的参数化界不转移为本项目的 FPT/XP 定理。

### R3：min–max 目标是需要新增精读的对照

Liang Xu, Zhou Xu, Dongsheng Xu, *Exact and approximation algorithms for the min–max k-traveling salesmen problem on a tree*, European Journal of Operational Research 227(2), 284–292, 2013。  
[DOI](https://doi.org/10.1016/j.ejor.2012.12.023) · [出版社预览](https://www.sciencedirect.com/science/article/pii/S037722171200971X)

出版社预览报告固定 $k\ge2$ 的伪多项式精确 DP，时间 $O(nW^{2(k-1)})$，W 为总边权，并给出近似方案。完整假设和转移仍需精读；本次没有完整核验其证明。

**借鉴：** 每条路线的资源分配比只追求总费用更接近本项目。  
**限制：** 它优化边权意义的最大路线长度；尚未识别出与精确访问/固定重数模型的等价。伪多项式依赖数值大小，不能改写为二进制输入上的普通多项式时间。

### R4：代表集保留的是“所有外部补全”，不是随便合并相似状态

Hans L. Bodlaender, Marek Cygan, Stefan Kratsch, Jesper Nederlof, *Deterministic single exponential time algorithms for connectivity problems parameterized by treewidth*, Information and Computation 243, 86–111, 2015。  
[DOI](https://doi.org/10.1016/j.ic.2014.12.008) · [机构全文](https://pure.tue.nl/ws/files/57608658/journaldeterministic_complete.pdf) · [预印本](https://arxiv.org/abs/1211.1505)

§3.2 定义对所有外部分区保持最优补全值的表示关系，证明若干 DP 运算保持该关系，并给出小代表集算法。

**借鉴：** #19 可以把安全压缩写成“压缩前后，对每个允许上下文的可扩展性一致”，再证明转移保持这一关系。  
**限制：** 论文处理加权连通分区；这里还有精确边重数和逐路线费用向量。没有建立本模型的连接矩阵秩界，就不能声称 rank-based 方法直接给我们小状态集。它是后续参照，不是第一包的实现要求。

### R5：压缩候选空间与压缩已经找到的证书不同

Filipe Brandão, João Pedro Pedroso, *Bin packing and related problems: General arc-flow formulation with graph compression*, Computers & Operations Research 69, 56–67, 2016。  
[DOI](https://doi.org/10.1016/j.cor.2015.11.009) · [作者项目页](https://research.fdabrandao.pt/vector_packing_solver/) · [接受稿](https://research.fdabrandao.pt/papers/arcflow_manuscript.pdf) · [预印本](https://arxiv.org/abs/1310.6887)

该工作用图中的路径表示合法装箱模式，并研究保持模型的图压缩。这为“完整模式集合不一定要逐行物化”提供了研究入口。

**借鉴：** 可以研究能生成合法树行的有向无环状态图，并保留路径到行的解码。  
**限制：** 已有重复行证书压缩只压缩输出，没有减少候选生成。装箱的容量单调性不能直接处理有符号费用和祖先闭包。先完成合法行生成及双向对应，再讨论图压缩、列生成和性能。

### R6：树上的精确算法并非只有一种

Pontien Mbaraga, André Langevin, Gilbert Laporte, *Two exact algorithms for the vehicle routing problem on trees*, Naval Research Logistics 46(1), 75–89, 1999。  
[作者机构报告 G-97-06](https://www.gerad.ca/en/papers/G-97-06) · [期刊目录](https://onlinelibrary.wiley.com/toc/15206750/1999/46/1)

机构摘要涉及容量和时间约束变体，介绍基于装箱下界和列生成的两类精确方法。技术报告为 1997 年、1998 年修订，期刊版本为 1999 年；不要混淆日期。

**借鉴：** 理论递推之外，可比较模式模型、下界与分支搜索。  
**限制：** 本次仅核对摘要与出版信息，尚不能判断其时间约束与逐次访问服务费是否相同；不能凭摘要认定本模型已被解决。

### R7–R8：树结构研究仍在推进，但近似保证不能替代精确可行性

Claire Mathieu, Hang Zhou：

- *A PTAS for Capacitated Vehicle Routing on Trees*, ICALP 2022, Article 95。[出版页及 PDF](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2022.95)。摘要给出单位需求、并扩展到可拆分需求的 PTAS。
- *A tight (1.5+ε)-approximation for unsplittable capacitated vehicle routing on trees*, Mathematical Programming 212, 115–146, 2025。[DOI](https://doi.org/10.1007/s10107-024-02094-z) · [作者机构记录](https://researchportal.ip-paris.fr/en/publications/a-tight-15%CE%B5-approximation-for-unsplittable-capacitated-vehicle-ro/)。摘要针对不可拆分终端需求、最小总路线长度给出近似结果。

**借鉴：** 同为树，需求能否拆分等改变会导致不同算法与结论，不能把“树路由”当成已统一解决的问题。  
**限制：** 本次仅作模型和研究进展定位，没有移植近似技术。允许预算超出、舍入数值或改变服务分配可能改变这里的精确 YES/NO 问题；研究近似必须另立目标。

### R9：自动求解与可信验证可以形成不同大小的可信核心

Kevin K. H. Cheung, Ambros Gleixner, Daniel E. Steffy, *Verifying Integer Programming Results*, IPCO 2017, 148–160。  
[DOI](https://doi.org/10.1007/978-3-319-59250-3_13) · [作者报告全文](https://optimization-online.org/wp-content/uploads/2016/11/5740.pdf) · [项目](https://github.com/ambros-gleixner/VIPR)

文章研究可独立检查的整数规划证明格式，将生成与检查分开，并解释可行解与不可行性/最优性证据的不同困难。

**借鉴：** 外部搜索器输出分配/矩阵，接入已有检查器，是改善实践能力的一种途径。  
**限制：** 接受可行证书不等于认证外部求解器的所有结论；“没有找到解”不够。不能假定不可行性证书总是多项式长度。VIPR 的存在不表示它已接入本项目或已在 Lean 验证。

### R10：近期工程资料，仅作为候选工具研究

Zhengzhong Ricky You, Yu Yang, *RouteOpt: An Open-Source Modular Exact Solver for Vehicle Routing Problems*, INFORMS Journal on Computing, 2026。  
[作者页面与代码/文档入口](https://zhengzhong-you.github.io/papers/routeopt/) · [DOI](https://doi.org/10.1287/ijoc.2025.1415)

作者页面介绍可扩展的精确路由求解平台，面向 CVRP、VRPTW 等模型。

**用途：** 了解精确求解器的分支、割与变量管理结构。  
**限制：** 本次未运行或审计该工具，也未证明其模型能表达精确重复访问与有符号服务费；不建议直接移植作为近期任务，没有对本项目作速度承诺。

## 4. #19 的两个不同契约

现有 [单次游程契约](TREE_BUDGET_SINGLE_EXCURSION_CONTRACT.tex) 和 [任意内部子树 A/B 纸面推广](TREE_SINGLE_EXCURSION_GENERALIZATION.tex) 研究给定合法见证，仍是纸面结果；本次不改变历史验收状态。

### 4.1 给定见证的上下文替换

充分摘要 α 应满足

$$
\alpha(P)=\alpha(P')
\Longrightarrow
\forall E\in\mathcal C,\quad
\mathrm{Glue}(E,P)\iff\mathrm{Glue}(E,P').
$$

必须写清允许的匹配、出现次数归属及服务收费。边界点不能因为拼接被少算或重复算。原反例只否定某些摘要的逐见证充分性，不否定存在型 DP。自由排列条件下的费用多重集判据也不适用于固定身份匹配。

### 4.2 算法状态表示一组可实现的部分解

状态 σ 应有独立的 Realizes(P,σ) 语义：

$$
\sigma\in D_v
\iff
\exists P,\ \mathrm{PartialValid}_v(P)\land\mathrm{Realizes}(P,\sigma).
$$

右侧合法性必须独立于算法定义。若把 Realizes 定义为“由递推生成”，再证明递推生成合法状态，会变成没有连接原问题的自证。

需要证明：初始化精确、合并可靠且完整、根接受 iff 原问题可行、回溯产生有效证书。压缩表应保持对允许外部补全的存在性。

单次边界穿越的旧契约不是一般输入的无损规范化：若某行边界重数大于 1，删去穿越会改变精确边流和访问。递归使用单次游程接口之前，必须证明其受限类对转移封闭，或扩充边界状态。

## 5. 从已有矩阵定理出发的候选精确 DP

本节是**新的纸面设计草案**，不是已实现的新算法，也不声称首次发现。目的在于给下一轮讨论一个可检验的递推。

### 5.1 固定对象与状态语义

固定有限根树、舰队数 m、兼容的非根父边重数 H、费用 s 和预算 T。需求输入先沿已有 FlowCompatible 与 requirement 接口处理，不绕过兼容性检查。初版保留路线标签 $i\in\mathrm{Fin}(m)$。

已有 [TreeBudgetMatrix.lean](../LeanCompletion/UAV/TreeBudgetMatrix.lean) 定义四项矩阵条件；[TreeBudgetCriterion.lean](../LeanCompletion/UAV/TreeBudgetCriterion.lean) 接到需求输入的路线可行性。single_row_realization 已负责完整行的存在性重建，不应从头重做。

对非根 v，令 $T_v$ 为含 v 的完整后代子树。部分矩阵在每一列满足总和 H(u)，并在子树内部满足逐行祖先闭包。状态为

$$
\sigma_v=(q,c),\qquad q\in\mathbb N^m,\quad c\in\mathbb Q^m,
$$

其中

$$
q_i=n_{i,v},\qquad
c_i=\sum_{u\in T_v}s(u)
\left(n_{i,u}+\sum_{w\in\mathrm{Ch}(u)}n_{i,w}\right).
$$

q 是每条全局路线在父边上的重数；c 是该路线在子树内的服务贡献，不包含父顶点费用。内部矩阵、列账目和回溯见证由存在型语义保证。初版保留实现矩阵或构造回溯信息，不只保留裸数对。

**该状态针对固定 H、固定树的“存在部分矩阵”任务。** 它不声称任意给定游程在任意端口政策下都可互换，不覆盖新加的先后顺序、时间窗或不同车辆约束。

### 5.2 叶节点与合并

叶 v 枚举满足 $\sum_iq_i=H(v)$ 的自然数向量，取 $c_i=s(v)q_i$。

内部节点 v 选择 q 和每个孩子 u 的可实现状态 $(q^u,c^u)$，要求

$$
\sum_iq_i=H(v),\qquad
q_i^u>0\Longrightarrow q_i>0,
$$

并设

$$
c_i=s(v)\left(q_i+\sum_{u\in\mathrm{Ch}(v)}q_i^u\right)
+\sum_{u\in\mathrm{Ch}(v)}c_i^u.
$$

**不能附加 $q_i^u\le q_i$：已有模型只要求正支持祖先闭包，允许一次进入父区域后多次访问其孩子。**

可靠性证明：拼接互不相交的孩子部分矩阵，补上 v 列；列和保持，跨边正支持由蕴含式保证，费用按公式相加。完整性证明：将任一合法部分矩阵限制到每个孩子子树，得到相应状态，再由同一公式恢复父状态。这里证明矩阵存在性，不要求保存原路线访问次序。

可逐个合并孩子：固定 q，费用累计器从 s(v)q 开始，每个孩子增加 $c^u+s(v)q^u$，检查正支持。不必把原树改成二叉树。中间表也要有语义、回溯和成本界，不能只数最终表。

### 5.3 根接受与证书重建

根 o 不收费，不能套用非根费用公式。根选择各孩子状态，要求

$$
\forall i,\quad
\sum_{u\in\mathrm{Ch}(o)}q_i^u=1,\qquad
\sum_{u\in\mathrm{Ch}(o)}c_i^u\le T.
$$

这些条件给出逐行一次出库和预算。回溯得到完整矩阵，复用 MatrixFeasible 的路线对应。根的逐孩子合并可保存 0/1 出库计数，丢弃计数超过 1 的组合；这是结构约束，与费用正负无关。

m=0 单独处理：矩阵无行，所有非根 H 必须为零，不能套用仅对 m>0 的组合数公式。若需要完整路线的可执行展开，应接 #21；已有存在性定理不自动等于已计费的路线生成器。

### 5.4 状态界与不该期待的剪枝

有限性不要求费用非负：每个矩阵坐标在 0..H(u) 内，所以部分矩阵和状态集合有限，但未必小。

首个有数值状态界的版本建议取**非负整数费用、整数预算 B≥0、m>0**。未来费用不会抵消已产生费用，保留 $0\le c_i\le B$ 不会丢掉全局可行解。有理非负费用需精确清分母；所得整数数值必须计入界，不能自动视为输入位长的多项式。

边界 q 的候选数为

$$
\binom{H(v)+m-1}{m-1}.
$$

保守的最终表大小是该数乘 $(B+1)^m$。还能利用固定总账：

$$
\sum_i c_i=
C_v:=
\sum_{u\in T_v}s(u)
\left(H(u)+\sum_{w\in\mathrm{Ch}(u)}H(w)\right).
$$

前 m−1 个费用决定最后一个，所以最终表有纸面上界

$$
|D_v|\le
\binom{H(v)+m-1}{m-1}(B+1)^{m-1}.
$$

恢复最后一项仍需范围检查。这只是最终表的状态数界，**不是完整运行时间界，更不是 FPT(m)**。还要计算中间表、组合次数、位算术、去重和重建成本。H、B 的数值在二进制编码下可能很大。

固定总账还有一个后果：同一个完整子树、固定 H 和收费语义下，若 $c_i\le c'_i$ 对所有 i 成立，固定总和迫使 $c=c'$。**普通逐坐标 Pareto 支配在这种状态层通常不会删除不同向量。** 不能把它列为必然有效的优化。

有符号费用不能因 $c_i>T$ 提前删除。精确整数化后，可用

$$
A_v=\sum_{u\in T_v}|s(u)|
\left(H(u)+\sum_{w\in\mathrm{Ch}(u)}H(w)\right)
$$

得到 $|c_i|\le A_v$，作为有限性和范围证明的起点；它不是非负预算剪枝，也不保证数值界小。

## 6. 哪些压缩先做，哪些推后

| 候选改进 | 先证明的保持性质 | 定位与风险 |
| --- | --- | --- |
| 相同完整 (q,c) 合并 | 保留一个实现见证后，后续转移存在性保持 | 首个稳妥压缩；收益待测 |
| 固定总账删除最后一个费用坐标 | 编解码往返、范围与转移对应 | 表示压缩，不自动减少语义状态数 |
| 同时置换路线标签 | q、c、见证及保留标签一起变换，合并能恢复匹配 | 不能只排序 c；身份受限时只能用允许的置换 |
| 自由匹配的排序检查 | 所有双射允许且结构账目固定 | 消除匹配子问题，不解决可实现性 |
| 模式生成 DAG / arc-flow | 路径解码 iff 合法行，压缩保持模式集合 | R5 的参照，不等于已有输出压缩 |
| rank-based / 更小代表集 | 对全部外部补全保持，并有规模和计算界 | R4 的参照；目前没有本模型的秩界 |
| 部分费用超预算即删除 | 剩余费用非负或有可靠下界 | 通用有符号版本不成立 |

先有标签的完整递推，再考虑一项可解释的压缩。#22 的执行精化保持具体答案、缓存和计数；新算法不必保持这些内部细节，但必须保持数学可行性和有效证书契约。

## 7. 可执行的推进计划

### A. 规格与纸面双向递推

- 阅读顺序：R1/R3 的状态和目标差异 → R2 的边界合并 → 第 5 节矩阵递推 → R4/R5 的压缩。
- 固定部分矩阵、边界重数、收费和根接受，分开给定游程替换与存在型状态。
- 写出叶、逐孩子合并、根接受的 iff；检查父顶点收费、重复访问、零重数及 m=0。
- 接回 MatrixFeasible，不重证树流唯一性或完整行的数学可实现性。

**完成标志：** 独立于程序的状态语义及双向证明。本文是起始草案，仍需该轮审阅，不以“画出 DP 表”代替此目标。

### B. 标签版本的可信基线

- 实现有限表、去重和回溯，使用精确有理/整数运算。
- 先与既有完整搜索比较同一固定 H 接口，再接需求到 H 的包装器。
- 覆盖路径/分叉树、孩子重数大于父重数、空舰队、零费用、有解/无解；有符号版包括局部超预算而外部抵消。
- 拟新增接口：state_iff_partialMatrix、merge_sound、merge_complete、root_accepts_iff_matrixFeasible、reconstruct_valid。**这些只是计划名称，不是已有声明。**
- 输出矩阵接现有检查器；无解结论需完整搜索和完备性定理支持。

**完成标志：** 正确、完整、能输出可检查见证。即使没有提速，也已得到另一种具有明确契约的求解结构。

### C. 一项压缩与一次针对性对照

首选相同完整状态去重，再考虑路线标签同步置换。分别证明语义保持，记录生成状态数、唯一状态数、合并尝试、算术位宽、回溯大小和实际耗时。比较相同成本域与相同输出任务。

具体问题：子树局部化是否避免全局候选物化？规范化是否值得开销？小 m、稀疏正支持或较小整数预算是否更适合？没有改进也记录原因，不预先承诺提速。

### D. 选定一个参数化结论，再考虑推广

从 m、边界活跃路线数、H 数值、整数预算或费用取值中选择明确参数。状态数、完整时间、二进制长度分别说明；固定 m 的数值型 DP 不能直接叫 FPT(m)。

单边界递推稳定后，再研究保留给定游程的多次穿越接口、多个边界顶点或一般图结构。这些需要新证明，不能由树矩阵 iff 自动继承。

## 8. #23 保留为独立、有限的后续线

[#23](https://github.com/huam54925-cpu/uav-routing-certification/issues/23) 与 [编码验收记录](HUB_REDUCTION_ENCODING_STATUS.md) 已包含语义对应、编号模型、Gamma/EOF 解析、长度和总位串正确性。

值得继续的两项：

1. 为实际解析、有效性检查、构造和序列化选择标准机器实现，证明输出等于 reduceBits 并给运行时间。parseGamma 的后缀 length、规范性重编码，以及 ValidInput 的按索引列表读取，都应计费或通过已证精化替换。二次时间仍是待形式化目标。
2. 将自然数分配列表检查器接到明确的二进制证书格式，证明受限规范目标上的短证书和多项式验证时间。保持零费用、零预算和空行，不额外加入源的严格三划分承诺。

这能使复杂度解释与自动验证工具更完整，但不会自动发现高效路由算法，也不证明现有搜索无法改进。外部 3-PARTITION 强 NP 完全性仍须标识来源；一般二进制树语言 NP 成员性需要独立论证。

## 9. 仓库联系与证据边界

- 已有源码：[矩阵定义与路线对应](../LeanCompletion/UAV/TreeBudgetMatrix.lean)、[需求判据](../LeanCompletion/UAV/TreeBudgetCriterion.lean)、[行实现与费用](../LeanCompletion/UAV/TreeBudgetRow.lean)、[矩阵说明](TREE_BUDGET_MATRIX.md)。
- #19 历史依据：[原契约](TREE_BUDGET_SINGLE_EXCURSION_CONTRACT.tex)、[A/B 推广](TREE_SINGLE_EXCURSION_GENERALIZATION.tex)、[接口记录](HUB_INTERFACES_STATUS.md)。
- #22 已交付范围：[执行记录](TREE_BUDGET_STORED_EXECUTION_STATUS.md)、[成本模型对照](TREE_BUDGET_COST_MODEL_COMPARISON.md)。
- [2026-11-03 综述](TREE_BUDGET_LITERATURE_REVIEW_20261103.md) 保留为历史快照，其旧待办不能当成当前状态。

本次只新增研究文档并同步导航/近期方向；没有修改 Lean 证明、冻结数据或工具链，没有执行 Lean 构建、公理审计、算法实验或新的有限枚举。文献结果、已有定理和候选推导分别标明，未声称新数学优先权或已实现性能提升。#19/#23 的 issue 状态未因本文自动关闭或改写。
