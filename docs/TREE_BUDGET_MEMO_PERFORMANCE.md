# 小规模记忆化性能对照（2026-11-04）

对应 [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18)
在 2026-11-04 更新的最小测量包；一般操作数上界和困难性仍属于 #20。
本报告只讨论人工小实例。以下复现使用现有 Lean 环境与依赖缓存。

## 计数与等价证明

新增 [TreeBudgetSearchStats.lean](../LeanCompletion/UAV/TreeBudgetSearchStats.lean)。
两个执行器按原顺序、每层重用完整候选列表，成功立即停止。

| 字段 | 定义 |
| --- | --- |
| calls | 请求求解一个完整 `(k,r)` 状态一次，包括零步和热命中 |
| hits | 查表返回 `some answer`，包括成功和失败答案 |
| expansions | 无缓存每次调用；记忆化每次未命中，包括零步检查 |
| candidates | 每次执行一次整个 `∀ v, p v ≤ r v` 判断；不是逐坐标比较数 |
| lookupComparisons | 查询实际访问的关联表条目数，包含命中的那条；完整键比较内部的坐标和位成本未展开 |
| insertionScans | 原 `insert` 的 filter 扫描条目数，等于插入前缓存长度；不是插入次数 |
| witnessRows | 运行后所有成功缓存答案的后缀行数之和；失败和成功空列表贡献零 |

无缓存没有查表，hits/lookupComparisons/insertionScans 为零；expansions 可能重复
访问同一键。记忆化的 expansions 是 miss 次数，在本组从空缓存开始的运行中对应
首次展开。候选检查、键比较都按逻辑操作计数，不按 CPU 指令或有理数位成本计数。
插入统计调用原 insert 并用列表长度计数；计算该长度自身的统计开销不进入原执行器计时。

`memoStat_erase`、`memoRowsStat_erase` 证明删除计数后，答案及整张缓存分别等于
`memoRowsWith`、`memoRows`，对任意候选列表与原始缓存成立。
`searchStat_erase`、`searchRowsStat_erase` 对应已证明的无缓存
`searchRowsWith`、`searchRows`，保持具体答案而非仅成功标志。
辅助定理覆盖查表、插入和候选扫描的擦除。
这些定理不保证统计与原执行器的耗时相同。

`witnessRows` 是逻辑保留量，不是内存字节数：Lean 可共享列表尾部及行函数。
输出证书压缩只测最终成功证书的后处理，与搜索剪枝和缓存表示无关。

## 实例与执行入口

新增 [TreeBudgetBenchCases.lean](../LeanCompletion/UAV/TreeBudgetBenchCases.lean)
和 [TreeBudgetBench.lean](../LeanCompletion/UAV/TreeBudgetBench.lean)。
所有主实例都从 `(rootCount R H, normalize R H, emptyCache)` 开始，H 已规范化。
没有人工重排候选；无缓存和记忆化冷搜索共用同一份 `candidates` 列表。

| 名称 | 树；H；服务费；预算 | 目的 |
| --- | --- | --- |
| shared_failure | hubTree（根0，中心1，叶2/3/4）；[0,2,1,1,1]；[0,0,6,6,6]；10 | 两条路线不能容纳三片叶，完整不可行及共享失败 |
| shared_success | 同树；[0,3,1,1,1]；同费用及预算 | 默认首候选不访问叶，先回溯共享失败，最终成功 |
| early_stop | 同树；[0,1,0,0,0]；同费用及预算 | 唯一模式，立即成功 |
| repeated | centerThree（根1，叶0/2）；[3,0,0]；全零；0 | 同一模式重复三次，检查后处理压缩 |
| low_reuse | pathFour（0–1–2–3，根0）；[0,1,1,1]；全零；0 | 多个候选但无缓存复用的对照 |
| branches_global | centerThree；[2,0,3]；[10,0,2]；10 | 整体搜索与根分支分解 |
| branch_0 / branch_2 | 由 branchMultiplicity 构造，分别 [2,0,0] / [0,0,3] | 每个分支候选和缓存独立，额外报告局部存储量 |

`canonical_start` 对共享实例证明规范根坐标及 k=rootCount(H)。
`canonical_shared_failure` 验证两个合法选择顺序产生同一失败键并出现在实际冷缓存。
另有完整失败、回溯成功、确有命中、减少展开、成功/失败热命中计数的内核回归。

| 计时字段 | 原执行器与范围 |
| --- | --- |
| candidates | boundedVectors + RowValid 筛选，完整 candidates |
| search_uncached / search_cold | 预生成候选的 searchRowsWith / 空缓存 memoRowsWith |
| search_hot | 预生成候选的 memoRowsWith，使用冷运行所得缓存 |
| full_uncached / full_cold / full_hot | searchRows / memoRows 的完整包装入口，包含 candidates；hot 每次复用同一份合法缓存 |
| compress_only | 现有 compressCertificate，成功证书的后处理 |
| branch_full_uncached / branch_full_memo | 原 searchByRoot / searchByRootMemo，包含每分支候选生成、搜索、证书转换和合并 |

普通 full_* 是固定规范 H 的原行搜索入口，不含原始需求的 multiplicities/compatible
转换；分支完整入口另行标明。repeat 定理仅说明输出相等，不能推出 full_hot 恒定耗时。

## 可复现命令与资源边界

在仓库根目录执行（本次实测使用既有本地工程 `G:\lean666\jsp_001022_extension`）：

```powershell
lake build LeanCompletion.UAV.TreeBudgetBenchCases LeanCompletion.UAV.TreeBudgetBench
py -3 LeanCompletion/UAV/run_tree_budget_bench.py --reps 1 --output verification/runs/memo-performance-20261104/pilot-forced
py -3 LeanCompletion/UAV/run_tree_budget_bench.py --reps 21
```

[run_tree_budget_bench.py](../LeanCompletion/UAV/run_tree_budget_bench.py) 是新增复现工具源码，
不是生成输出；它属于本仓库允许发布的研究源码和复现工具。
默认一次进程运行全部实例，避免反复加载 Lean 模块。也可用 `--cases shared_failure`
等名称分进程运行。每阶段（含全部重复）5秒硬上限、启动/加载600秒上限。
测量前打印并 flush 阶段标记，监督器超时终止该子进程树并记录 timeout_unfinished；
后续未执行的阶段没有测量结果，不能解释为不可行。

原始 JSON/日志、环境和结果仅留在 ignored `verification/runs/`。
计时使用 `IO.monoNanosNow`，输入每次从 IO.Ref 读取，计算结果必须在结束时间戳前
写入 IO.Ref，随后才取回计算校验和，防止纯计算被编译器移出计时区间；
运行检查和统计不计入 timed samples。每阶段先预热一次，再测指定次数；
输出保留全部样本，报告中使用中位数及范围，未扣除计时器和结果引用写入开销。
这里的冷/热指算法缓存，不是操作系统缓存；未进行 CPU 绑核或原生可执行文件优化。

## 本次验证和结果

**结论：本组小实例中，缓存确实减少重复展开，但冷运行的收益不足以抵消当前
关联表维护开销。热命中有效，不过完整入口仍需重新生成候选。暂不改缓存表示，
也没有足够的见证存储压力支持立即改成后继指针。**

环境：Windows 11 家庭版 10.0.26200，Intel Core i7-14650HX（16核/24逻辑处理器），
系统可见内存约31.7 GiB；Lean 4.30.0-rc2 / x86_64-w64-windows-gnu Release，
Python 3.13.4。执行方式为上述 `lake env lean --run`，不是独立原生可执行文件。
只用本机 CPU 和内存，没有 GPU 或真实无人机数据。

完成一次单样本试跑后，每项正式测量预热1次、记录21次，共65个计时阶段、1365个
正式样本。正式进程墙钟51.94秒，包含 Lean 启动和模块加载；启动不进入下表。
所有阶段均完成，没有超时或未完成的算法实例。运行时逐坐标比较两执行器的具体
答案及统计/原执行器缓存快照，并检查原证书及压缩证书；全部通过。

初版计时校验曾得到0–100纳秒，检查发现纯计算可移动到结束时间戳之后。
这两次校准运行的耗时全部作废，没有用于下表。修正后检查生成的 C：求解函数
调用和结果引用写入确实位于两个 `lean_io_mono_nanos_now` 之间，再重新进行
单次试跑和21次正式测量。原始校准输出仍保留本地并标记无效。

### 操作次数

无缓存 calls=expansions，hits/查表/插入扫描均为0。记忆化 expansions=misses，
所有本次冷运行均满足 calls=hits+expansions 以及 expansions=最终缓存条目数。

| 实例 | 无缓存调用/展开 | memo调用 | 命中 | memo展开 | 候选检查：无缓存→memo | 查表比较 | 插入扫描 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| shared_failure | 18 | 18 | 6 | 12 | 20→20 | 74 | 66 |
| shared_success | 27 | 24 | 8 | 16 | 33→29 | 122 | 120 |
| early_stop | 2 | 2 | 0 | 2 | 1→1 | 0 | 1 |
| repeated | 4 | 4 | 0 | 4 | 3→3 | 0 | 6 |
| low_reuse | 4 | 4 | 0 | 4 | 3→3 | 3 | 6 |
| branches_global | 6 | 6 | 0 | 6 | 7→7 | 0 | 15 |
| branch_0 | 3 | 3 | 0 | 3 | 2→2 | 0 | 3 |
| branch_2 | 4 | 4 | 0 | 4 | 3→3 | 0 | 6 |

全部根状态热运行计数为 calls=1、hits=1、expansions=0、候选检查=0、
查表比较=1、插入扫描=0；缓存及后缀见证量不变。
shared_failure 是失败热命中，其他实例是成功热命中。这里根键位于表头，
不能推广成任意缓存键的一次比较。

| 实例 | 枚举向量→合法候选 | 缓存条目 | 后缀见证总行数 | 成功输出条目：压缩前→后 |
| --- | ---: | ---: | ---: | ---: |
| shared_failure | 24→4 | 12 | 0 | 无成功证书 |
| shared_success | 32→4 | 16 | 6 | 3→3 |
| early_stop | 2→1 | 2 | 1 | 1→1 |
| repeated | 4→1 | 4 | 6 | 3→1 |
| low_reuse | 8→3 | 4 | 1 | 1→1 |
| branches_global | 12→2 | 6 | 15 | 5→2 |
| branch_0 | 3→1 | 3 | 3 | 2→1 |
| branch_2 | 4→1 | 4 | 6 | 3→1 |

两个分支独立缓存的条目合计7、见证行合计9；相对于整体搜索的6和15，条目不一定
更少。这个合计不是同时存活或峰值字节数：原分支入口不保留各分支内部缓存。
最终合并证书的条目由5压缩为2，原检查器接受。

### 时间：原执行器，单位微秒

以下全为21次的中位数；完整入口与分段测量分别执行，不用相减声称精确成本归因。

| 实例 | 候选生成 | 无缓存搜索 | memo冷搜索 | 预生成热命中 | 完整无缓存 | 完整memo冷 | 完整memo热 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| shared_failure | 1079.1 | 606.2 | 2177.2 | 19.1 | 1642.6 | 3390.0 | 1120.0 |
| shared_success | 1357.7 | 1205.6 | 3685.8 | 19.3 | 2465.2 | 5527.3 | 1297.1 |
| early_stop | 115.9 | 33.6 | 35.0 | 19.8 | 154.2 | 155.3 | 138.7 |
| repeated | 70.4 | 29.0 | 33.5 | 7.5 | 103.7 | 110.7 | 81.4 |
| low_reuse | 239.8 | 62.1 | 147.6 | 13.5 | 318.7 | 415.5 | 272.6 |
| branches_global | 178.9 | 76.3 | 82.8 | 7.7 | 248.0 | 255.7 | 172.9 |
| branch_0 | 47.8 | 16.6 | 19.5 | 6.6 | 66.5 | 84.3 | 67.7 |
| branch_2 | 67.4 | 33.7 | 38.2 | 9.7 | 103.6 | 109.3 | 77.6 |

关键比较的最小–最大值如下，单位仍为微秒；全部样本在本地原始记录中。

| 实例 | 无缓存搜索范围 | memo冷搜索范围 | 预生成热命中范围 | 完整memo热范围 |
| --- | ---: | ---: | ---: | ---: |
| shared_failure | 561.6–648.7 | 2055.0–2817.3 | 19.0–19.8 | 1081.6–1175.6 |
| shared_success | 1129.9–1324.3 | 3144.4–4204.4 | 19.0–19.6 | 1290.7–1333.7 |
| early_stop | 33.4–38.5 | 34.8–38.9 | 19.6–23.7 | 137.4–144.2 |
| repeated | 28.6–30.1 | 33.0–40.3 | 7.3–7.9 | 80.2–92.8 |
| low_reuse | 58.1–64.2 | 144.8–153.5 | 13.4–14.0 | 269.7–277.9 |

原完整根分支入口：无缓存262.0（230.5–288.2），memo258.6（255.4–268.9）。
两者范围重叠，这点差异不作提速证据；它们与整体行入口的计时范围也不同。
最终输出压缩中位数：shared_success 25.2、early_stop 1.2、repeated 15.6、
low_reuse 1.3、branches_global 27.0、branch_0 8.4、branch_2 15.5。

### 解释与下一步

shared_failure 的展开从18降至12（减少33.3%），但20次候选检查完全没有减少：
复用的是廉价的零步失败判断。同时增加74次查表和66次插入扫描，原冷搜索中位
耗时变为3.59倍。shared_success 的展开从27降至16（减少40.7%），候选检查只从
33降至29（减少12.1%），冷搜索中位耗时为3.06倍。这说明“少展开多少状态”
必须和所省状态的实际工作量一起理解。

预生成候选的热命中很便宜，完整热入口仍在候选生成上付出约毫秒级成本。
对重复求解同一固定输入，现有 `memoRowsWith` 接口已经允许调用方保留候选；
若后续研究完整入口提速，应先测候选生成复用的效果。对一次性冷运行，本组数据
支持优先审查关联表查找/插入与低复用场景的选择，而不是假定记忆化总是更快。
这些计数不是精确 CPU profile，不能把全部耗时差都归因于某一种扫描。

本组最多16个缓存条目、15行逻辑后缀见证，尚未显示需要后继指针的存储压力。
本包没有更换关联表，也没有加入哈希表、路线提取、一般内部子树DP或困难性归约。
结果仅适用于这里的人工小输入、当前解释执行方式和这次环境，不推出大实例趋势、
渐近复杂度、FPT/XP、内存位界或优化后原生程序的速度。

### 构建与审计记录

本轮定向 `lake build LeanCompletion.UAV.TreeBudgetBench` 成功，退出码0，8354 jobs。
统计模块、实例证明、运行器均在本轮实际 Built；最终构建对前两个已通过模块复用缓存。
9项统计擦除定理、10项实例定理均通过，文件内及独立汇总公理审计覆盖全部19项。
其中1项无公理，其余仅使用标准三公理的子集；无 sorryAx。新增模块无警告，
既有依赖重放的警告不算新增。开发中的失败构建不计为通过。

原有93个 UAV Lean 文件的 SHA-256 全部保持不变；工具链、依赖锁、冻结目标和
既有受保护源码未修改。新增源码未使用 sorry/admit/native_decide/unsafe/partial
或新增公理。复用现有环境，不声称干净克隆或独立环境验证。

原始记录目录：`verification/runs/memo-performance-20261104/`，有效正式样本在
`measured/`，有效试跑在 `pilot-forced/`。发布包仅包含源码、复现工具和本精炼报告；原始日志及 JSON 保留本地。未修改远端 Issue。

本包从原实验工程移入 UAV 研究分支，新增 Lean 源码保持一致；上述构建与测量均来自原实验工程，未在发布工作树重新构建，不宣称新的独立验证。
