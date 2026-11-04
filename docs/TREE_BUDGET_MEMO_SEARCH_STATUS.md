# Issue #18：完整记忆化递归与证书接入

日期：2026-11-04（Asia/Tokyo）。接续 [缓存契约](TREE_BUDGET_MEMO_STATE_STATUS.md)，
对应 [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18)。
本次在现有本地工程继续实施；远端 Issue 正文及其 df484ca 阶段评论作为计划参考，
实现以本地既有剩余搜索、缓存契约和本次 Lean 构建为准。

## 执行与证明

[TreeBudgetMemoSearch.lean](../LeanCompletion/UAV/TreeBudgetMemoSearch.lean)
提供 `scanCandidates`、`memoRowsWith` 和 `memoRows`。外层按 k 结构递归，内层按候选
列表结构递归。每次状态求解先查询完整 `(k,r)`；命中直接返回，未命中才展开。
零步检查整个 r=0，选择候选前检查逐坐标 p≤r，每层重用完整候选集。

扫描器接收子问题求解函数，只传递缓存和拼接成功见证。失败子调用的缓存继续传给
下一个候选；只有外层在完整扫描结束后才能缓存父状态失败。`ScanSpec` 的失败结论
仅排除给定列表，`memoRowsWith_spec` 要求候选成员与合法行双向等价，因而不能把
一个合法但不完整的候选集误当成完备搜索。

| 定理 | 保证 |
| --- | --- |
| `memoRows_spec` | 合法输入缓存产生合法输出缓存和 `AnswerValid` 答案 |
| `memoRows_sound` | 成功返回当前残量的合法剩余见证 |
| `memoRows_correct` / `memoRows_none_iff` | 成功 iff 可行，失败 iff 不可行 |
| `memoRows_isSome_eq_searchRows` | 与旧无缓存搜索的成功标志一致 |
| `memoRows_nodup` | 输入键无重复则输出键无重复 |
| `memoRows_lookup` | 返回时当前状态已经缓存 |
| `memoRows_extends` | 所有旧的可见命中及其原答案完整保留 |
| `memoRows_hit` / `memoRows_repeat` | 命中直接返回；重复调用答案和缓存均不变 |

语义结论需要固定 R,H,s,T 下的 `CacheValid`；原始缓存列表仍可被调用者装入错误
答案。表示和执行性质（无重复保持、命中、旧答案保留）不需要语义合法性前提。

## 初始输入、根分支和压缩

[TreeBudgetMemoIntegration.lean](../LeanCompletion/UAV/TreeBudgetMemoIntegration.lean)
提供 `searchMemo`、`searchByRootMemo`、`solveByRootMemo` 及相应 `Compressed` 入口。
初始输入规范化根坐标并使用空缓存；只有初始剩余见证通过 `initial_witness_valid`
转换为原输入证书。每个根分支独立调用初始入口，因此分别初始化缓存。

根分支入口保留 m=rootCount(h) 检查并复用 `mergeBranches`；原需求入口先检查
`compatible`，再使用 `multiplicities`。成功结果经原 `checkCertificate` 接受，
且与 `MatrixFeasible` / `BudgetRoutes` 等价；保留与旧入口成功标志一致的定理。
压缩只对最终成功证书调用既有 `compressCertificate`，不改变内部搜索或缓存见证。

## 可达性与规模

[TreeBudgetMemoReachability.lean](../LeanCompletion/UAV/TreeBudgetMemoReachability.lean)
从 `(rootCount R H,H)` 定义可达状态，允许所有合法且满足减法保护的转移，包括
最终失败的分支。可达状态满足 k=rootCount(r)、r≤H，根坐标保持初始值；规范化
输入的根坐标因此始终为零。

[TreeBudgetMemoBounds.lean](../LeanCompletion/UAV/TreeBudgetMemoBounds.lean)
将可达键编码到已有非根有界向量类型，建立
`S(H) = ∏ v≠root, (H(v)+1)` 的键数界。算法缓存界通过证明实际执行保持所有
缓存键可达，并结合 `KeysNodup` 建立；仅有无重复键不足以推出该界。
`initial_cache_length_le` 的起点明确为 `(rootCount R H,H,emptyCache)`，不是任意
k,r 或外来缓存。该计数编码不改变可执行搜索使用的完整 `(k,r)` 键。

## 回归与验证

[TreeBudgetMemoExamples.lean](../LeanCompletion/UAV/TreeBudgetMemoExamples.lean)
包含 30 项回归：零步全零/非零（含根坐标及深边）、同 r 不同 k、成功/失败重复命中、失败子
缓存保留且父状态成功、不同选择顺序共享失败状态、重复模式、减法保护、负虚拟费
预算边界、错误机队数、不相容需求、基地单点、根分支隔离及压缩后检查等回归。
计算证明使用 `decide +kernel`。

在现有工程根目录执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetMemoExamples LeanCompletion.UAV.TreeBudgetMemoBounds
```

本轮退出码 0，8358 jobs；上述五个新模块全部显示为 `Built`，其余依赖复用既有
缓存。30 项计算回归全部通过，新增模块无警告；旧依赖重放的非致命 linter 警告
不算新增警告。之前的开发失败运行不计为 PASS。

本轮另对全部 89 个新增定理汇总执行 `#print axioms`，退出码 0：其中 1 项不依赖
任何公理，其余 88 项的依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，
无 `sorryAx`，审计无错误或警告。
新增源码没有 `sorry`、`admit`、新增 `axiom`、`native_decide`、`partial` 或 `unsafe`。
本轮修改前的 88 个 UAV Lean 文件 SHA-256 均保持不变，已跟踪文件无差异。
使用固定 Lean 4.30.0-rc2 和既有工具链、依赖缓存，未创建新环境，不宣称干净克隆
或独立环境验证。原始开发/构建/审计日志和哈希快照统一留在 ignored
`verification/runs/memo-search-20261104/`。

## 边界与后续

本次目标为完整记忆化递归及其语义闭环。尚不声称 #18 的性能测量清单全部完成，
也不关闭远端 Issue。具体缓存条目计数回归不等于一般的首次展开或候选检查计数定理。
候选生成、关联列表查找/替换、算术、见证存储和耗时仍需单独测量；不宣称提速、
多项式时间、FPT 或 XP。完整后缀见证仍保存在缓存中。

本次按用户要求发布到 UAV 仓库的 `research/structural-service-cuts-20261023` 分支，基于 df484ca；未修改 GitHub Issue。既有 Lean 源码、冻结目标、
工具链和依赖锁保持不变；本轮依赖缓存重放不算新独立验证。

发布使用隔离工作区，仅复制上述五个模块及本文并更新首页导航。构建来自原本地开发工程；未重新构建发布工作区。
