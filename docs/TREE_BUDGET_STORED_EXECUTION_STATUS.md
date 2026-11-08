# 共享存储执行：A–E 的实现与证明边界

本包使用原有固定 Lean 环境，为 `executeStored` 建立真实输入比特串到输出的表示精化和自身成本界。原执行器保留为语义参照；新执行器的工作量不由旧 `memoCost.work` 转移而来。

## 验收接口

| 工作包 | 实现及验收接口 |
| --- | --- |
| A：共享答案 | `RowsRep`、`SharedAnswerRep`；前置行节点分配 3 槽，连同成功外壳为 5 槽，不复制尾链；失败与成功空矩阵不同 |
| B：收费缓存 | 实际带地址读头、读键、首命中查找、稳定过滤和插入；保留顺序、重复键与失败缓存的行为 |
| C：具体搜索 | `memoD_correct`、`memoD_preserves` 同时保持答案、有序缓存、六事件、堆良构与旧表示 |
| D：完整执行 | `executeStored_refines`、`executeStored_no_storage_error`、`executeStored_output_correct`；从实际输入位串接通检查、规范化、整数缩放、候选物化、存储初始化、搜索和收费序列化 |
| E：资源与总成本 | `executeStored_heap_bound`、`input_envelope`、`input_width_bound`、`executeStored_work`、`executeStored_time_and_allocations`，以及覆盖所有位串的两个 `executeStored_fpt_*` 定理 |

**状态：A–C 已完成，D 已完成，E 已完成（在本文指定的带地址位成本模型内）。** 各接口的最终检查结果在下方记录；没有使用容量或总成本公理。

## 执行模型与成本范围

持久对象使用既有追加式随机访问的比特／引用槽模型。新搜索中每次读取和写入均走带地址收费原语；分配先计算实际端点，再测量位宽。键、向量和候选引用进入存储，控制帧在子调用返回后重新读取。共享答案只在最终输出时物化，缓存观察器是证明用观察，不是输出执行步骤。

长度头、缓存链、候选链和输出链均使用收费的二进制游标：`cursorStep` 执行零测试和减一；初始化游标也调用 `addNatD`。这修正了 A–C 初版采用未收费堆大小控制游标的边界。向量读取的分配计数还补入了实际长度比较产生的辅助分配。

`work = Costed.steps + Costed.allocations`。其中 allocations 是累计收费的辅助工作区及对象构造分配，包含解析、编码、比较等缓冲区；它不等于持久堆槽数。六个逻辑事件是验证仪器，不作为需要序列化的运行结果。时间结论适用于这里明确定义的带地址位成本执行模型，不是 Lean 编译器生成程序的秒数、操作系统内存或独立图灵机模拟定理。

## 分配先于地址宽度和时间

令 `ell` 为实际输入比特串长度，`S` 为规范化重数状态盒的大小。对合法输入：

- 实际最终持久堆不超过 `4096 * S^3 * (ell+1)^2` 槽。
- `memoD_growth` 对实际递归、共享答案和过滤重建作归纳，限制累计追加的堆槽。`rowsWrite_size` 和 `initializeStore_size` 给出初始化的精确槽数。
- `input_envelope` 先证明初始化堆加整个搜索的分配预算；`Extends` 保持已有地址和对象。缓存长度由实际表示限制，过滤重建时的临时追加端点也计入宽度预算。
- 所有局部收费原语所需端点都落在 `8*(N+B+1)` 内，其中 `N` 是已经证明的分配预算，`B` 是已由输入位长限制的对象负载界。`input_width_bound` 证明统一位宽不超过 `11*ell+24`。已完成最终堆中任何前缀的有效地址还有 `executeStored_address_width` 的 `11*ell+20` 界。

随后 `scanD_work`、`memoD_work` 沿实际程序分支合成成本。它们的通用容量前提在 `executeInput_work` 中由 `input_envelope` 消去。预处理、候选生成、初始化、最终输出和前端检查也分别收费；没有以参数化时间假设证明时间结论。

## 总时间与参数代入

`TreeBudgetStoredTotalWork.executeStored_work` 的仅有数据前提是实际解析和检查成功的等式，结论为：

```text
steps + allocations <= 2^50 * S^3 * (ell+1)^7
```

`executeStored_time_and_allocations` 分别给出步骤与累计分配的同一上界。拒绝输入的完整执行满足 `262144*(ell+1)^3`，包含语法拒绝以及父环、非法索引或零分母等检查失败。

由 `S <= 2^M` 和 `S <= (U+1)^t`，得到：

```text
work <= 2^50 * 2^(3*M) * (ell+1)^7
work <= 2^50 * (U+1)^(3*t) * (ell+1)^7
```

`executeStored_fpt_mass` 与 `executeStored_fpt_support_maximum` 对所有位串成立，拒绝输入按参数零处理，输入多项式指数固定为七。这给出所选带地址位成本模型下的 FPT(M) 和 FPT(t,U)。这里采用较宽松、便于组合的七次输入多项式，未宣称复现旧纸面界的较紧次数或常数。

范围仍是从重数 H 输入开始的规范初始层数、根坐标归零、空缓存和显式行矩阵输出。需求到 H、实际顶点路线展开、其他输出压缩以及标准机器模拟不是本包执行器。仅参数 t 的分类不由这些结论推出。#22 还包括文献模型对照等更广的验收项，本次不自动关闭该 issue。

## 可复现检查

复用原有 Lean 4.30.0-rc2、依赖版本及本地缓存，不新建环境。执行入口：

```powershell
lake build LeanCompletion.UAV.TreeBudgetStoredTotalWork LeanCompletion.UAV.TreeBudgetStoredSearchExamples LeanCompletion.UAV.TreeBudgetStoredExecutionExamples
lake env lean verification/AuditTreeBudgetStoredExecution.lean
```

公开审计入口只包含 Lean 审计源。原始构建、逐项公理报告和生成清单仅在忽略目录 `verification/runs/stored-execution-de/`，不上传。既有历史 PASS 不作为这次执行记录。

2026-11-08 的最终联合构建退出 0，完成 **8422 项构建任务**（包含缓存复用）。A–C 的 11 个和 D 的 14 个可执行回归本次重新编译通过，共 **25 个边界回归**。公开入口的 **89 个接口**审计退出 0；另对本包 27 个模块中的 **311 项显式声明**逐项运行公理审计，退出 0、无遗漏，公理均只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx`。新增源码扫描没有 `sorry`、`admit`、新 `axiom`、`unsafe` 或 `native_decide`。仍有未使用简化参数、行长和既有模块文档样式等非阻断警告，不声称无警告构建。

本包的本地导入闭包为 110 个模块。与发布前已获取的远端研究分支逐文件对照，已有依赖仅 `TreeSupportExact` 与 `TreeRouteDecomposition` 的末尾空白不同；这两处差异不发布。固定工具链及公开仓库九项依赖的 URL、提交版本一致。开发目录另有 Prim、repl、LeanArchitect；它们不在本包导入闭包中。发布目录的配置和依赖固定版本保留原样，不以开发目录配置覆盖。

原始日志仍留在本地忽略目录。迁移后的验证复用范围由实际迁移结果另行记录。
