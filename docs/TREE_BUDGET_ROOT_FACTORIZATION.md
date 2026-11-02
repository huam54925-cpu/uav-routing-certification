# 根子树预算分解：数学证明与 Lean 实现规格

日期：2026-11-02。对应 [研究任务 #16](https://github.com/huam54925-cpu/uav-routing-certification/issues/16)，
承接 [1418ac7](https://github.com/huam54925-cpu/uav-routing-certification/commit/1418ac7ab6df7db034004e9b1ede40864503583b)
的有限模式接口。

数学稿初版状态：本文给出完整数学证明、接口规格与边界算例；当时新增定理尚未写入 Lean，
本文不构成 Lean 构建或公理审计通过记录。既有构建记录仍只属于原来的证明批次。

后续实现已完成本地 Lean 构建与边界验证，详见
[Lean 实现与验证状态](TREE_BUDGET_ROOT_FACTORIZATION_STATUS.md)。
下文保留初版证明规格和任务次序；当前完成范围以状态文档及 Lean 源码为准。

## 1. 评价、范围及既有接口

今天先做根子树分解是合理的：它消除根分支之间的组合枚举，局部机队数由根边列和
直接确定。这个结论不解决单个根子树内的装箱问题，也不保证多项式时间。

固定有限根树 R，基地 o，父函数 parent，自然数边重数 h，费用 s : V → ℚ，预算 T : ℚ。
h(v) 表示父边在每个方向的次数，不是两个方向之和，也不是顶点的访问次数。
根坐标可规范化为 h(o)=0；所有现有可行性接口均忽略该坐标。
不对 s 或 T 加非负假设，也不预设 h 的正支撑祖先闭合。

使用以下既有接口：

- `TreeBudgetPatterns.Pattern R h s T`：根坐标为零、各非根坐标不超过 h、
  `rootCount = 1`、正支撑祖先闭合、逐路线费用不超过 T 的有限模式类型。
- `TreeBudgetPatterns.PatternCountsFeasible`：存在自然数模式计数，使全部非根列和等于 h。
- `TreeBudgetPatterns.matrix_iff_pattern_counts`：在 `m = rootCount R h` 下连接矩阵与模式计数。
- `TreeBudgetCriterion.budget_routes_iff`：路线存在等价于 `FlowCompatible` 与规范重数的矩阵可行性。

以下用 p(v) 简写 `TreeBudgetPatterns.values p.val v`。令 C = Ch(o)，P 为上述模式集合。

## 2. 根子树的精确定义及分割

对 c ∈ C，定义（父函数迭代零次为恒等函数）

\[
V_c=\{v\in V\mid \exists k\in\mathbb N,\;\operatorname{parent}^{[k]}(v)=c\}.
\]

这个定义包含 c 自己，不包含 o；因为 parent(o)=o，而 c≠o。

**父链终止。** 仓库中 `parent_rank` 的方向是
`R.rank v < R.rank (R.parent v)`，条件为 v≠o。设

\[
M=\sum_{w\in V}\operatorname{rank}(w),\qquad
\mu(v)=M-\operatorname{rank}(v).
\]

每个顶点的 rank 都不超过 M。因此 v≠o 时，μ(parent(v))<μ(v)。
对 μ 作良基归纳，任意顶点的父链在有限步内到达 o。
这与 `TreeFlowConnectivity.parent_path` 已采用的终止度量相同；可复用 `rank_le_sum`。

对非根 v，定义 b(v) 为父链首次到达 o 之前的那个顶点：若 parent(v)=o，
则 b(v)=v；否则 b(v)=b(parent(v))。上述度量使这个递归良定义。
b(v)∈C，且 b(c)=c 对每个 c∈C 成立。

若 parent^[k](v)=c∈C，则此前的父链不可能经过 o，否则之后永远停在 o；
沿这段非根父链 b 不变，所以 b(v)=b(c)=c。反之，b(v) 的定义给出相应迭代次数。
故

\[
v\in V_c\iff v\ne o\ \land\ b(v)=c.
\]

由此得到全部分割性质：

1. c∈V_c，且 o∉V_c。
2. 每个 v≠o 恰好属于一个 V_c，即 c=b(v)。
3. c≠d 时 V_c∩V_d=∅，并且 ⋃_{c∈C}V_c=V\{o}。
4. 若 v∈V_c 且 v≠c，则 parent(v)∈V_c；parent(c)=o。
5. 若 v∈V_c 且 w 是 v 的孩子，则 w∈V_c。
6. V_c 与 C 的交集恰为 {c}。

第一版可以用父链可达谓词表达 V_c；若需要可执行成员判断，则实现上述 b，
再用其等价定理转换。无需构造新的顶点子类型树或重新选基地。

## 3. 第一步：合法模式的唯一归属

### 3.1 根孩子坐标是唯一的单位向量

对任意 p∈P，合法性给出

\[
\sum_{c\in C}p(c)=1.
\]

每项是自然数。若全为零，则和为零，矛盾，因此存在 c 满足 p(c)>0。
又 p(c)≤1，故 p(c)=1。其余项的和为零，故每个 c'≠c 都有 p(c')=0。
这也证明了 c 的唯一性。记此根孩子为 owner(p)。

这里没有假设 C 非空：是合法模式的存在推出 C 非空。若只有基地，则 P 为空。

### 3.2 一步祖先闭合传播到整条非根父链

现有 `AncestorClosed` 的确切条件是

\[
v\ne o\ \land\ p(v)>0\ \land\ \operatorname{parent}(v)\ne o
\quad\Longrightarrow\quad p(\operatorname{parent}(v))>0.
\]

若 p(v)>0，由 p(o)=0 可知 v≠o。设 b(v)=d。从 v 沿父链到 d 的每个顶点
均不是 o；逐次应用上述条件，得到 p(d)>0。传播在根孩子 d 处停止，
无需也不能推出 p(o)>0。

由根孩子的唯一正坐标，d=owner(p)。因此

\[
\boxed{p(v)>0\ \Longrightarrow\ v\in V_{\operatorname{owner}(p)}.}
\]

等价地，若 v∉V_owner(p)，则 p(v)=0。证明只使用正性传播，不使用
`p(child) ≤ p(parent)`；后者不是模型条件。

### 3.3 模式分割及交叉坐标为零

定义

\[
P_c=\{p\in P\mid p(c)=1\}.
\]

它们两两不交且覆盖 P。每个 p∈P_c 在 V_c 外为零。
特别地，若 v∈V_c 且 p∉P_c，则 p(v)=0。

可供 Lean 求和使用的精确接口是有限类型等价

\[
P\simeq\sum_{c:C}P_c,
\quad p\longmapsto(\operatorname{owner}(p),p),
\quad(c,p)\longmapsto p.
\]

两个复合为恒等映射来自 owner 的唯一性；子类型证明字段用证明无关性处理。
这给出有限求和的分组公式，无需对模式重新编号或增加任意选择的机队分配。

## 4. 第二步：局部定义与固定路线数

对每个 c∈C 定义

\[
\operatorname{LocalCountsFeasible}(c):\iff
\exists z_c:P_c\to\mathbb N,\quad
\forall v\in V_c,\quad
\sum_{p\in P_c}z_c(p)p(v)=h(v).
\]

由于 c∈V_c 且 P_c 中所有模式的 c 坐标均为 1，把 v=c 代入立即得到

\[
\boxed{\sum_{p\in P_c}z_c(p)=h(c).}
\]

因此局部路线总数是推论，不是一个额外优化变量。
同样，对任意全局可行计数 z，利用交叉坐标为零可得

\[
h(c)=\sum_{p\in P}z(p)p(c)=\sum_{p\in P_c}z(p).
\]

### 局部问题确实只依赖本分支的重数

在原顶点类型上定义零延拓的局部输入

\[
h^{(c)}(v)=\begin{cases}h(v),&v\in V_c,\\0,&v\notin V_c.\end{cases}
\]

存在保持所有坐标的有限类型等价

\[
P_c\simeq\operatorname{Pattern}(R,h^{(c)},s,T).
\]

证明：从左向右，分支外坐标为零，故满足新的坐标上界；其余合法性条件和费用完全相同。
从右向左，h^(c)≤h 给出原上界；模式在分支外为零，且 C∩V_c={c}，
于是 rootCount=1 强制 p(c)=1。两方向仅重新包装有界自然数的证明，坐标不变。

这个等价说明使用全局 P 定义 P_c 没有引入其他分支的约束。
它还给出

\[
\operatorname{LocalCountsFeasible}(c)
\iff\operatorname{PatternCountsFeasible}(R,h^{(c)},s,T).
\]

右侧在 V_c 内就是局部列和；在 V_c 外的每个非根列两边都为零。
又 rootCount(R,h^(c))=h(c)，故由既有矩阵—模式计数定理

\[
\boxed{\operatorname{LocalCountsFeasible}(c)
\iff\operatorname{MatrixFeasible}(R,h^{(c)},h(c),s,T).}
\]

全程保留 R、o、s、T，尤其没有把计费顶点 c 改为免费基地。

## 5. 第三步：全局模式计数的分解充要定理

**定理。** 对任意自然数 h、任意有理数费用 s 与预算 T，

\[
\boxed{\operatorname{PatternCountsFeasible}(R,h,s,T)
\iff\forall c\in C,\ \operatorname{LocalCountsFeasible}(c).}
\]

**全局推出局部。** 给定全局计数 z，取 z_c 为 z 在 P_c 上的限制。
对 v∈V_c，其他组的模式在 v 处为零，故

\[
\sum_{p\in P_c}z_c(p)p(v)
=\sum_{p\in P}z(p)p(v)=h(v).
\]

这给出局部计数，且上一节已经推出其路线数为 h(c)。

**局部推出全局。** 为每个 c 取一个局部见证 z_c。有限个存在见证可以组合；
Lean 的纯存在性证明可用 `choose`。由模式分割定义

\[
z(p)=z_{\operatorname{owner}(p)}(p).
\]

任取 v≠o，令 c=b(v)。分组求和并消去交叉零项，得到

\[
\sum_{p\in P}z(p)p(v)
=\sum_{d\in C}\sum_{p\in P_d}z_d(p)p(v)
=\sum_{p\in P_c}z_c(p)p(v)=h(v).
\]

全部非根列和因此恢复。每个被使用的模式本来就满足 cost(p)≤T；合并计数不改变任何
模式的坐标或费用，也不把几条路线拼成一条。总路线数为

\[
\sum_{p\in P}z(p)=\sum_{c\in C}\sum_{p\in P_c}z_c(p)
=\sum_{c\in C}h(c)=\operatorname{rootCount}(R,h).
\]

两个方向均未使用费用的符号。根分支之间也不存在转移“剩余预算”的操作。

## 6. 与 MatrixFeasible、BudgetRoutes 的准确连接

### 6.1 任意给定边重数的矩阵接口

不能漏掉全局路线数的相容条件。无附加假设的完整表述为

\[
\boxed{\operatorname{MatrixFeasible}(R,h,m,s,T)
\iff \left(m=\operatorname{rootCount}(R,h)\right)
\land\forall c\in C,\operatorname{LocalCountsFeasible}(c).}
\]

必要的等式直接由矩阵的根孩子列和及每行 rootDegree=1 推出：

\[
\sum_{c\in C}h(c)=\sum_{c\in C}\sum_{r< m}n_r(c)
=\sum_{r< m}\sum_{c\in C}n_r(c)=m.
\]

得到该等式后，两个方向都调用 `matrix_iff_pattern_counts` 和第 5 节主定理。
将第 4 节的局部矩阵等价代入，还得到

\[
\operatorname{MatrixFeasible}(R,h,m,s,T)
\iff m=\operatorname{rootCount}(R,h)\ \land\
\forall c\in C,\operatorname{MatrixFeasible}(R,h^{(c)},h(c),s,T).
\]

若把 `m = rootCount R h` 作为定理参数，则结论中可省去这个合取项。

### 6.2 从原访问需求得到预算路线

令 q(v)=requirement(R,d,v) 为现有整数递推。定义

\[
\widehat h(v)=\begin{cases}0,&v=o,\\q(v).\mathrm{toNat},&v\ne o.\end{cases}
\]

保留既有 `FlowCompatible R d m`，即

\[
\left(\forall v\ne o,\ q(v)\ge0\right)
\land\left((m:\mathbb Z)=\sum_{c\in C}q(c)\right).
\]

此条件推出 m=rootCount(R,ĥ)。`budget_routes_iff` 的矩阵输入是未规范化的
`fun v => (requirement R d v).toNat`；它与 ĥ 在每个非根顶点相等，
故矩阵可行性相同。无需假设 q(o)=0，也无需限制基地自己的需求。

于是完整的需求接口是

\[
\boxed{\operatorname{BudgetRoutes}(R,d,m,s,T)
\iff\operatorname{FlowCompatible}(R,d,m)
\land\forall c\in C,\operatorname{LocalCountsFeasible}_{R,\widehat h,s,T}(c).}
\]

还可将右侧局部谓词逐项改写为
`MatrixFeasible R (mask ĥ c) (ĥ c) s T`。
证明就是依次使用既有 `budget_routes_iff`、根坐标无关性、整数非负转自然数求和、
矩阵—模式计数等价以及第 5 节定理。

局部计数覆盖的是边重数 ĥ，不是访问需求 d。整数递推非负性必须在自然数截断前检查；
不能用分支检查取代 `FlowCompatible`，也不能直接把 d 当成 h。

## 7. 边界、数值例子与不能推广的情形

下表为数学验收实例，尚未新增对应的 Lean 回归定理。

| 情况 | 结论及理由 |
| --- | --- |
| h(c)=0 且 V_c 内 h 全零 | P_c 为空，因为 p(c)=1 与 p(c)≤0 矛盾；空计数满足全部零列，局部零路线可行，即使 T<0。 |
| h(c)=0 但 V_c 内某个 h(v)>0 | P_c 仍为空，该正列的左侧为零，局部不可行；不能跳过这个分支。 |
| 只有基地 | C 与 P 都为空；模式计数可行，矩阵恰在 m=0 时可行；BudgetRoutes 也要求 m=0，基地需求和费用被忽略。 |
| 基地只有一个孩子 c | V_c=V\{o}，局部问题就是原问题；m=h(c)，没有搜索规模缩减。 |
| 多个根子树都可行 | 取局部计数的互不重叠并集，所有路线预算与列和保持。 |
| 某个根子树不可行 | 由全局到局部的必要性，全局不可行；其他分支无法补救。 |

**零根边、正深边即使相容也不可行。** 路径 o-c-v 上取 h(c)=0、h(v)=1。
令 d(c)=d(v)=1、m=0，则整数递推在 c、v 分别为 0、1，满足 FlowCompatible；
但局部模式不存在，不能覆盖 v。说明需求相容性和预算矩阵可行性均需保留。

**两个可行分支及预算等号。** 树只有两条边 o-a、o-b，取 h(a)=h(b)=1，
s(a)=10、s(b)=2、T=10。两个局部模式各用一次，组成两条合法预算路线。

**跨分支的负费用不能救助超预算路线。** 在同一棵两叶树取 s(a)=11、s(b)=-100、T=10。
虽然总费用为 -89，a 分支的唯一一条路线费用仍为 11，因此全局不可行。
逐路线的预算约束不能替换成总费用约束。

**分支内部允许负费用抵消。** 树边为 o-c、c-a、c-b，取 h(c)=h(a)=h(b)=1，
s(c)=0、s(a)=12、s(b)=-3、T=10。模式 p=h 的费用为 9，合法路线可取
o,c,a,c,b,c,o。若删除负费用的 b 访问，费用反而变为 12。
根分解保留完整模式，不做这种删除，故不需要非负假设。

**子边重数可以大于父边。** 路径 o-c-v 上取 p(c)=1、p(v)=2，所有费用为零，T=0。
合法路线 o,c,v,c,v,c,o 实现该模式；正支撑祖先闭合并未要求 2≤1。

**一般内部顶点不能照搬独立分解。** 树边为 o-c、c-a、c-b，取
h(c)=h(a)=h(b)=1、s(c)=0、s(a)=s(b)=6、T=10。唯一一条全局路线必须覆盖
两个孩子分支，费用为 12，所以不可行。若把 c 的两个孩子各自拿到完整预算 10
来独立判断，会把两个费用 6 的部分都判为可行，却忽略它们共享同一条路线预算。

费用一直使用现有公式

\[
\operatorname{cost}(p)=\sum_{v\ne o}
\bigl(s(v)+\mathbf1_{\operatorname{parent}(v)\ne o}s(\operatorname{parent}(v))\bigr)p(v).
\]

其中根孩子 c 仍收费；父顶点的重复访问也仍收费。保留原树可直接保证该语义。

## 8. Lean 工作包与完成标准

建议新增 `LeanCompletion/UAV/TreeBudgetRootFactorization.lean`，导入
`TreeBudgetPatterns` 与 `TreeBudgetCriterion`；边界例子放独立模块
`TreeBudgetRootFactorizationExamples.lean`。以下是拟定名称与规格，不是已存在声明。

| 顺序 | 接口/引理 | 必须交付的内容 |
| --- | --- | --- |
| 1 | `RootChild`, `InRootSubtree`, `rootBranch` | 根孩子子类型、父链定义、非根顶点归属；证明覆盖、唯一性、父子封闭及根孩子交集。 |
| 2 | `pattern_unique_root_child` | 自然数根和为 1 推出唯一坐标 1，其他根孩子坐标为零。 |
| 3 | `positive_at_rootBranch`, `pattern_zero_outside` | 沿非根父链传播正性，得出模式支撑只在所属分支。 |
| 4 | `BranchPattern`, `pattern_branch_equiv` | P_c 的子类型以及 P 与 sigma 类型的等价，用于有限求和。 |
| 5 | `LocalCountsFeasible`, `local_count_total` | 定义局部列和；用 c 列导出总计数 h(c)。 |
| 6 | `pattern_counts_iff_local_counts` | 先限制、再按 owner 合并，证明主 iff。 |
| 7 | `branchMultiplicity`, `branch_pattern_equiv`, `local_counts_iff_matrix` | 分支外置零输入、保持坐标的模式等价、固定 h(c) 的局部矩阵。 |
| 8 | `matrix_iff_root_local`, `budget_routes_iff_root_local` | 保留 m=rootCount 或 FlowCompatible；处理根坐标规范化。 |
| 9 | 例子模块与针对性审计 | 覆盖第 7 节实例，构建新模块并审计主定理公理。 |

建议的核心 Lean 规格（`BranchPattern` 等名称待实现）：

```text
RootChild R := {c : V // c ∈ TreeBudgetPatterns.children R R.root}
BranchPattern R h s T c :=
  {p : Pattern R h s T // values p.val c.val = 1}

LocalCountsFeasible R h s T c :=
  ∃ z : BranchPattern R h s T c → ℕ,
    ∀ v, InRootSubtree R c v →
      ∑ p, z p * values p.val.val v = h v

pattern_counts_iff_local_counts :
  PatternCountsFeasible R h s T ↔
    ∀ c : RootChild R, LocalCountsFeasible R h s T c

matrix_iff_root_local :
  MatrixFeasible R h m s T ↔
    m = rootCount R h ∧
    ∀ c : RootChild R, LocalCountsFeasible R h s T c

budget_routes_iff_root_local :
  BudgetRoutes R d m s T ↔
    FlowCompatible R d m ∧
    ∀ c : RootChild R,
      LocalCountsFeasible R
        (normalize R (fun v => (requirement R d v).toNat)) s T c
```

求和可优先通过 `pattern_branch_equiv`、`Equiv.sum_comp` 和 `Fintype.sum_sigma` 重排；
模式取值变化只发生在子类型包装层，应先证明坐标保持引理，避免后续反复拆解 `Fin`。
向父递归复用 `TreeFlowConnectivity.rank_le_sum` 与 μ 度量。
纯数学主定理可用经典有限选择；这不自动提供可执行分支搜索器。

数学验收以第 2–6 节的证明链及第 7 节边界为准。
形式化验收另需在现有环境针对性构建、主定理公理审计，无 `sorry`、`admit` 或新增未证公理；
原始输出保留在忽略目录 `verification/runs/`。不得将本文或历史构建记录称为本轮 Lean PASS。

## 9. 余力任务：证书合并，然后搜索优化

局部证书应由现有 `checkCertificate R h^(c) (h c) s T` 接口检验。
若各局部证书有效，将所有条目按根孩子拼接，保持每个条目的行与重数：
每行仍满足原全局上界和预算，重数总和为 Σ_c h(c)，全部非根列和为 h。
反向按每行的 owner 分组，同样得到有效局部证书。
零重数条目也必须满足现有行合法性要求；没有合法模式的零路线分支可使用空证书。

这是可执行证书合并的数学规格，本文没有实现拼接函数或新的验证器。
下一阶段依次为：证书合并接口、各分支的剩余需求搜索、重复模式压缩、记忆化。
任意一般树动态规划、复杂度承诺以及顶点序列路线生成仍是独立任务。
