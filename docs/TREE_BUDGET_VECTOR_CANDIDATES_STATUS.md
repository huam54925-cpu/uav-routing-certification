# Issue #22 候选列表小包：本地验收与发布核对

> 历史记录范围：下文记录 [1bc9924](https://github.com/huam54925-cpu/uav-routing-certification/commit/1bc992475a9bd515d77245e2bc0471e5ecab2fd5) 的候选列表包及其当时交付。随后 [e576911](https://github.com/huam54925-cpu/uav-routing-certification/commit/e5769113868b75a38016a30c2f6a8a016a14060e) 已实现 #21 第一包，并将表示契约更新为英文；其构建与后续 PDF 审阅见 [表示桥接状态](TREE_BUDGET_REPRESENTATION_BRIDGE_STATUS.md)。下文关于中文 LaTeX、#21 尚无新 Lean 模块及未修改议题的陈述仅描述原包，不代表当前状态。本次状态同步没有重复原验证。

日期：2026-11-06（Asia/Tokyo）。本轮完成候选生成的精确列表对应，并交付 #21 第一包的数学规格。以下记录开发阶段实际执行的本地验收，发布核对见文末；未修改远端议题。

## 交付与范围

- [TreeBudgetVectorCandidates.lean](../LeanCompletion/UAV/TreeBudgetVectorCandidates.lean)：直接构造物化向量的递归枚举器、根上界规范化、稳定过滤、正比例整数费用入口和原始正分母分数入口。保留有符号费用、负预算和未约分分数。
- [TreeBudgetVectorCandidatesExamples.lean](../LeanCompletion/UAV/TreeBudgetVectorCandidatesExamples.lean)：8 项具名边界回归。
- [TREE_BUDGET_REPRESENTATION_CONTRACT.tex](TREE_BUDGET_REPRESENTATION_CONTRACT.tex)：#21 的假设表、存在性组合、规范化单行的投影／重建契约及信息损失例子。数学推导在此 LaTeX 源码中；新组合仍是纸面结果，没有新增 #21 Lean 桥接模块。

主模块的 9 个定理：

1. `decode_emptyV`
2. `decode_tailV`
3. `decode_consV`
4. `map_decode_boundedVectorsV`
5. `decode_normalize_eq_bound`
6. `map_filter_decode`
7. `rowValidB_eq_decide`
8. `map_decode_candidatesV`
9. `map_decode_candidatesV_scaled`

两个候选对应出口证明完整列表相等，包含顺序与出现次数。枚举前将上界的根坐标归零，检查器继续接收原始 `H`，不要求原始 `H(root)=0`。通用过滤对应复用 `List.filter_map`，不附加解码单射或输入无重复的假设。

## 本轮实际执行的验证

在 `G:/lean666/jsp_001022_extension` 的现有锁定 Lean 环境执行：

```powershell
lake build LeanCompletion.UAV.TreeBudgetVectorCandidates
lake build LeanCompletion.UAV.TreeBudgetVectorCandidatesExamples
```

两条最终命令均退出 0。主模块最终构建实际编译新模块，显示 `Build completed successfully (8334 jobs)`；回归模块构建实际编译新模块，显示 `Build completed successfully (8339 jobs)`，并复用已通过的主模块及其他依赖缓存。并非全新环境构建，也未运行远端 CI 或性能实验。

全部 **17 个新增定理**的 `#print axioms` 输出已逐项核对，依赖仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx`。新增源码没有 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`；两个新模块没有编译警告。既有依赖重放的警告不算新模块警告。

8 项回归覆盖：零维枚举恰有一个空向量；上界 `[1,2]` 的完整六项顺序；零坐标上界；非首位置根且原根上界非零；过滤后的完整候选顺序；负整数费用与负预算的接受／拒绝边界；未约分有符号分数的三种预算边界；一般重复项过滤。具体计算使用 `decide +kernel`，重复项回归为一般类型上的证明。

首轮主模块构建因归纳步骤中的尾向量解码改写失败，不计为 PASS；修正后以上最终构建通过。开发中另一个只读直接 Lean 检查曾启动后停止，不计为完成验证。最终验收使用上述实际成功构建及其中的公理输出，没有把历史记录或中止运行计作新通过。

原始日志位于 ignored `verification/runs/issue22-candidates-20261106/`：`core-build-final.log`、`examples-build.log`。失败／中止输出也仅留在同一目录。所有 **110 个既有 UAV Lean 文件**以及根导入、工具链、Lake 配置、依赖锁定和冻结验证输入这 **5 个文件**经本轮前后 SHA-256 核对未改变。

## LaTeX 验收和停止点

LaTeX 是可独立上传 Overleaf 的中文源文件，选择 **XeLaTeX**。已独立审阅数学声明与引用定理，静态检查环境／大括号配对、12 个唯一标签、15 处内部引用，以及 13 个源码模块链接。固定基线为 `5114dc8`；其中 `FixedFlowObstruction` 本地与该基线仅有历史验证说明注释差异，所引用证明代码一致。未运行 LaTeX 编译，未生成或检查 PDF。

#22 本轮止于候选列表小包验收；完整搜索、缓存和逻辑事件计数的表示对应、位成本语义仍留待后续。#21 本轮止于数学规格与纸面推导，不标为整个议题完成。既有执行器、缓存协议、README 和历史验证记录均未改动。

## 发布核对 — 2026-11-06

按用户要求发布到 `huam54925-cpu/uav-routing-certification` 的既有 `research/structural-service-cuts-20261023` 分支，基于 `06077788fc4a211126de98db7c75b88c9ef20db7` 建立独立发布工作区。变更限定为上述两个 Lean 模块、LaTeX 源码及本验收说明四个文件；原始日志、运行快照和构建产物留在本地。

两个 Lean 模块及 LaTeX 源码与开发验收后的文件逐字节一致，本说明仅更新发布口径。两个新模块的导入闭包共 27 个 `LeanCompletion` 模块，其中 25 个既有模块在忽略换行格式与末尾空白后，与目标分支源码一致。目标分支的工具链、9 个依赖锁定版本和 Lean 编译选项与本地验证环境一致；目标项目保留原有直接依赖 Mathlib 的配置，本地工程另有这些模块未使用的 Prim 等依赖。

本次发布核对复用前述已执行的本地构建和公理审计，没有重新执行 Lean 构建、远端 CI 或 LaTeX 编译，也不将发布工作区称为独立重建验证。
