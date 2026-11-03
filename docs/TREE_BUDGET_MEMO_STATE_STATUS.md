# Issue #18 第一小包：完整剩余状态缓存契约

日期：2026-11-03（Asia/Tokyo）。对应 [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18) 的第一小包；代码基线为 `2466e0b`，本次发布基于研究分支 `499ed3f01f7f078a4610c8c90886c2de1b655e23`。

本批实现缓存状态、语义契约与回归，并一并提交此前的[状态分离、旅行费用编码及三篇论文对照](TREE_BUDGET_STATE_AND_LINEAR_COST_20261103.md)。完整记忆化搜索仍为第二小包。

## 数据与语义

核心模块为 [TreeBudgetMemoState.lean](../LeanCompletion/UAV/TreeBudgetMemoState.lean)，保持 Issue 指定接口：

```lean
abbrev Rows (n : ℕ) := List (Fin n → ℕ)
abbrev Key (n : ℕ) := ℕ × (Fin n → ℕ)
abbrev Answer (n : ℕ) := Option (Rows n)
abbrev Cache (n : ℕ) := List (Key n × Answer n)
```

`emptyCache`、`lookup cache q`、`insert cache q answer` 均为可执行定义，比较整个 `(k,r)`，包括剩余向量的每个坐标。底层接受任意状态，未以根计数替代 k，也未在缓存层静默规范化根坐标。

| 查询结果 | 意义 |
| --- | --- |
| `none` | 无记录，尚不知道答案 |
| `some none` | 缓存的答案为不可行；需要语义契约保证 |
| `some (some [])` | 缓存的成功见证为空列表 |
| `some (some rows)`，rows 非空 | 缓存的成功见证是若干合法行 |

对固定 R,H,s,T，`AnswerValid q (some rows)` 就是既有 `ResidualWitness R H s T q.1 q.2 rows`；`AnswerValid q none` 则是 `¬ ResidualFeasible R H s T q.1 q.2`。`CacheValid` 要求所有查询命中均满足这个契约。

缓存本身是普通列表，不在类型中携带 R,H,s,T。输入隔离由调用方保持相同的 `CacheValid R H s T` 来保证；不能把某个输入下的证明移用于另一个输入。下一阶段各根分支应各建空缓存。本批未实现分支缓存执行器。

插入删除全部同键旧项，再把新答案放到表头。因此旧缓存即使含有该键的重复项，也会在这次插入时清除。其他键的重复项不会自动被清理；从空缓存出发，通过 `KeysNodup` 的保持定理保证全表键始终无重复。

## 已证明接口

| 定理 | 保证 |
| --- | --- |
| `lookup_empty` | 空缓存必定未命中 |
| `lookup_insert_same` | 插入键查询得到新答案，包括失败和空见证 |
| `lookup_insert_other` | 其他完整键的查询结果不变 |
| `cacheValid_empty` | 空缓存的语义契约成立 |
| `cacheValid_insert` | 插入 `AnswerValid` 的答案保持 `CacheValid` |
| `keysNodup_empty`、`keysNodup_insert` | 空表键无重复，替换插入保持该性质 |
| `insert_length_le` | 一次插入后的条目数不超过原长度加一 |
| `insert_preserves` | 合并语义合法性与键无重复的单步保持接口，可用于下一阶段归纳 |

这些定理约束缓存操作，不会凭空认证一个 `none`。原始列表可以装入错误数据；只有获得 `AnswerValid` 证明后才能使用保持定理。`CacheValid` 按可见查询结果定义，`KeysNodup` 则是独立的表示不变量。

## 回归

[TreeBudgetMemoStateExamples.lean](../LeanCompletion/UAV/TreeBudgetMemoStateExamples.lean) 包含 18 个命名定理，计算回归使用 `decide +kernel`：

- 同一合法缓存同时产生未命中、失败命中、空成功和非空成功四种查询结果。
- `r=0` 时 `(0,r)` 保存成功空列表，`(1,r)` 保存已证失败；两键不能混淆。
- 复用同输入的 good/bad 反例：摘要相同，但完整键不同；good 保存两条费用为 10 的合法行，bad 保存不可行答案，并证明整个缓存合法。
- 将 good 的见证替换为相反行序，证明新答案合法、其他键保持、表长不变。
- 对同键重复的原始列表执行清理；连续替换同键不增加条目数。
- 错误地给 good 写入失败、或给 bad 写入成功空列表，均不满足 `CacheValid`。

这里的缓存命中是对显式插入后的查询回归，没有声称已运行带缓存递归或实现跨搜索路径的自动复用。

## 验证与发布范围

在既有本地工程根目录执行针对性构建：

```powershell
lake build LeanCompletion.UAV.TreeBudgetMemoStateExamples
```

2026-11-03，核心模块定向构建退出码 0（8339 jobs）；修正两处例子证明的化简/参数推断问题后，上述例子构建退出码 0（8348 jobs）。核心模块在本轮编译，最终例子命令复用其未变源码缓存并编译例子模块。9 项核心与 18 项例子公理报告共 27 项，仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；两个新模块无 linter 警告，无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。旧依赖重放的非致命警告不计为新增警告。

86 个本轮修改前已有的 UAV Lean 文件哈希不变，其中包含一并发布的三个前阶段模块。它们的先前构建与 20 项公理报告见单独状态文档，不把缓存重放计为新独立验证。验证使用固定 Lean 4.30.0-rc2、既有依赖与缓存，未创建新的 Lean 环境。最终日志留在 ignored `verification/runs/memo-state-20261103/`，失败的开发运行不计 PASS。

发布采用从远端研究分支建立的隔离工作区，通过本机既有代理进行普通提交和非强制推送。本地开发工程与远端的 83 个既有 UAV Lean 文件已逐一比较：75 个规范化换行后相同，其余 8 个差异仅为注释或尾部空行，证明正文未见差异；mathlib 及远端所有锁定依赖的提交一致。开发工程额外含 Prim、LeanArchitect、repl；不据此宣称独立发布工程或干净环境构建通过。

只发布新增 Lean 源码、精炼状态/文献文档和首页导航。原始日志、API 响应、依赖比较、哈希快照、PDF 提取与图片均留在 ignored `verification/runs/`；不上传用户下载的参考 PDF，也不改动冻结 Case1 模块、数据、根入口或工具链/依赖锁。

## 第二小包的接入要求

下一步实现 `memoRows` 时，命中使用缓存契约，未命中才展开；按 k 和候选列表证明终止。失败子调用产生的缓存必须传递，当前状态只有在全部候选都失败后才能写入失败。零步必须检查整个 r=0，选择前必须检查 p≤r，每层继续使用固定完整候选集。

成功见证仍覆盖当前 r；初始输入接口才将它转换为原 h 的证书。保留旧无缓存搜索作为语义参照。关联列表的查询和替换需要扫描列表，完整后缀见证也占用空间；本批无搜索性能测量或运行时间改善承诺。
