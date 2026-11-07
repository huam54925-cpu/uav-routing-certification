# 单次游程推广、分配检查器与编号模型 — 2026-11-07

本批以研究分支 `86993ec790cb6c7ab3f28ed61805dcb783aa7f0f` 为发布基线，
复用现有 Lean 开发环境。完成用户指定的数学小包 A/B、状态同步与公开有限检查入口、
#23 分配证书检查器、编号目标对应。用户允许省略的二进制编解码及长度 Lean 包不在本批范围内。

> 已发布版本：[2a64246](https://github.com/huam54925-cpu/uav-routing-certification/commit/2a64246acd8e5fe323e8d6bbe3fd3399cdedd3df)，既有研究分支，共 13 个变更文件（本说明包含在内）。下文开发、构建及发布段落保留各自发生时的记录；本次文档整理不构成新验证。二进制编解码/长度包按用户允许暂缓，不作为本批未交付项。

## 当前证据分层

| 对象 | 当前完成范围 | 仍未完成 |
| --- | --- | --- |
| #19 | 原单次游程纸面契约；本批推广给定合法见证到任意内部子树，并证明自由交换下的排序预算 iff | Lean 拼接接口、一般摘要可实现性、多次穿越及递归状态 |
| #23 语义 | `dcc3db8` 的三划分语义 Lean iff；本批的分配检查器与编号对应 | 二进制表示与运行成本的 Lean 形式化 |
| #23 编码与复杂度 | `86993ec` 的长度、多项式变换和受限语言强 NP 完全性的纸面论证；一般树仅强 NP 困难性 | 一般二进制树语言 NP 成员性、形式化复杂度层 |
| #21 | 第一表示桥梁包完成 | 完整见证转换与约定的往返契约 |
| #22 | 候选列表的顺序、重数对应完成 | 完整搜索/缓存模拟及位成本 |

GitHub #19、#21、#22、#23 的状态已同步到上述已发布基线，保留旧计划为历史记录，
四个 issue 均保持开放。以上同步发生在本批开发验收阶段，当时新增文件尚未提交或推送；
随后按用户要求发布本批文件，发布范围与证据边界见文末。

## 数学小包 A/B：纸面证明

[独立 LaTeX 文稿](TREE_SINGLE_EXCURSION_GENERALIZATION.tex)给出七个引理、定理或推论。

A 把内部星形放宽为单条割边后面的任意子树。前提仍是**已经给出的合法内部游程**，
每条参与路线只有一次进入、一次离开。保留出现次数、实际有向边流、逐游程费用及匹配元数据后，
拼接访问/边流/费用的三个恒等式、提取、给定见证的拼接 iff 与上下文替换均成立。
星形专有的叶计数矩阵可实现性没有被推广；文稿给出内部路径反例说明其公式不能照搬。

B 对降序外部费用 `b`、升序内部费用 `c` 证明：
存在全体预算均可行的排列，当且仅当逐项 `b[j]+c[j] ≤ T`。
证明用前 `j` 个排列像的鸽巢论证，允许负费用、并列值及空匹配。
费用多重集只在所有匹配都允许且其他结构账目固定时决定剩余预算匹配；
文稿另给固定归属反例，未宣称任意摘要可实现或一般树 DP 完备。

## Lean 分配证书检查器

源码：[HubAssignmentChecker.lean](../LeanCompletion/UAV/HubAssignmentChecker.lean)，
[回归模块](../LeanCompletion/UAV/HubAssignmentCheckerExamples.lean)。

- `assignmentLoad` / `AssignmentValid`：每项分配到恰一个路线标签，只检查每行负载至多预算。
- `checkAssignment_eq_true_iff`：布尔接受 iff **该给定分配**满足预算。
- `routing_iff_exists_accepted_assignment`：原路线目标可行 iff 存在被接受的类型化分配。
- `decodeAssignment`：原始 `List Nat` 必须长度为 `3*m`，所有标签小于 `m`。
- `decodeAssignment_encode` 与 `decodeAssignment_eq_some_iff`：列表往返及成功解码的规范性，保留项顺序。
- `checkAssignmentList_eq_true_iff` 与 `routing_iff_exists_accepted_list`：原始列表接受及存在证书的完整契约。

这些契约没有 `ValidInput` 前提，也不检查每行三项。证明复用已有单位列分配、行负载对应和
`routing_iff_unitMatrix`。零预算、零费用、空行、空舰队以及不满足三划分源条件的规范目标均在定义域内。
这里的列表编解码不等于二进制编解码。

19 条回归定理覆盖有解实例的正确和错误分配、无解实例不存在任何接受证书、空族和零预算、
零费用、空行的 hub-only 路线、短/长/越界列表以及欠重源仍有可行目标。

## Lean 编号目标对应

源码：[HubNumberedInstance.lean](../LeanCompletion/UAV/HubNumberedInstance.lean)，
[回归模块](../LeanCompletion/UAV/HubNumberedInstanceExamples.lean)。

`nodeEquiv` 显式对应 `Fin (3*m+2)` 和已有 `Option (Option (Fin (3*m)))`：
`0` 是基地，`1` 是枢纽，`i+2` 是叶项。编号边流、需求和服务费先用独立数值分段定义，
再证明与已有 `canonicalFlow`、`required`、`service` 逐坐标相等；基地需求明确为零。

小型 `Relabel` 接口直接映射路线访问列表，保留顺序与重复次数，并证明合法性、访问计数、
有向边流、有符号服务费用及 `ExactFeasible` 的保持。`numbered_routing_iff` 合成编号目标与旧目标的
精确可行性 iff，同样不要求 `ValidInput`。10 条回归定理覆盖空族的两个顶点、编号数据、
正反实例、欠重源、重复访问及负费用；基地费用非零仍不计入路线服务。

## 公开检查入口与本次有限检查

[复跑说明](REPRODUCING_BOUNDED_CHECKS.md)提供三个纯标准库 Python 入口。
原始结果只写到 ignored `verification/runs/hub-interfaces-20261107/`，脚本本身只输出到 stdout。

本次重新运行的编码模型通过：630 个有效小源（598 有解、32 无解）、37,926 次分配比较、
37,929 次实际路线列表重建、8,191 个长度不超过 12 的二进制输入；另有 5,124 次整数往返、
945 次结构往返、943 个有效源长度检查及非法输入边界检查。

原星形游程模型重新通过 57,600 次路线恒等式/提取、172,800 次预算/匹配 iff、
28,800 次错误目标拒绝、537 次同接口比较及 27 组矩阵/游程可实现性像比较。
上述两个公开入口还在仅复制交付源码的研究分支工作区根目录成功运行，输出与开发区一致，
不依赖私有检查脚本。这不是该工作区的 Lean 重建。

新 A/B 模型通过两种非星形子树的 141 条内部游走、1,692 次拼接/提取、234 次同接口比较、
92,160 次族级拼接 iff、16,082 次排序预算 iff、125,216 次鸽巢比较及 1,741 次非空 minimax。
完整有限范围见复跑说明和文稿。这些检查不是通用定理的内核证明或运行时间证明。

新文稿通过环境、括号及引用静态检查，没有编译或审阅新 PDF。
旧文稿源稿准备时的检查与后来单独发生的 PDF 审阅仍按各自历史记录理解；本批没有重写其历史结论。

## 定向构建与公理审计入口

在仓库根目录执行：

```powershell
lake build LeanCompletion.UAV.HubAssignmentChecker LeanCompletion.UAV.HubAssignmentCheckerExamples
lake build LeanCompletion.UAV.HubNumberedInstance LeanCompletion.UAV.HubNumberedInstanceExamples
lake env lean verification/AuditHubInterfaces.lean
```

前两条在现有锁定工具链 `leanprover/lean4:v4.30.0-rc2` 的开发环境完成，四个新模块实际编译。
最终新模块无警告；旧依赖的历史警告/审计输出可能被 Lake 回放，不计为新增警告或本次重新验证。
这不是全库、全新环境、独立发布工作区构建或远端 CI。

公开审计源 [AuditHubInterfaces.lean](../verification/AuditHubInterfaces.lean)覆盖所有显式新增声明，
不包含原始运行输出。

最终统一审计命令实际退出 0，覆盖 **78 个显式新增声明：57 个定理（含 29 个回归定理）、
20 个定义及 1 个缩写**。逐项输出与源码声明名一一核对，无遗漏；公理依赖仅为
`propext`、`Classical.choice`、`Quot.sound` 的子集，没有 `sorryAx` 或 `Lean.ofReduceBool`。
新 Lean 源码未使用 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。
分配检查器另有 10 项可执行 `#eval` 检查通过；有限回归证明使用内核归约。

初轮局部 Lean 类型推断/改写错误及最后的格式警告已修复；失败运行不计为通过。
最终成功记录为 `assignment-build-final.log`、`numbered-build-2.log`、
`numbered-examples-build-1.log`、`audit-all-final.log` 和 `assignment-eval-final.log`，
均留在上述 ignored 运行目录，未作为交付源码。

本批开始时快照的 **126 个既有文件**逐项 SHA-256 核对均未改变，包括既有 Lean、
根导入、工具链、Lake 配置、依赖锁定、冻结输入和两份旧 LaTeX 文稿。
旧状态文档只添加当前导航，README 在以研究分支为基线的独立本地工作区更新，
没有覆盖开发项目原有 README。所有运行输出、构建产物及下载材料继续留在本地。

交付工作区位于 `verification/runs/hub-interfaces-20261107/review/`，本地分支
`codex/hub-interfaces-20261107`，基于 `86993ec`。其中 13 个交付文件限于源码、
文稿与导航说明；12 个共享文件与已验收开发版本逐字节一致，README 仅在该工作区更新。
四个新 Lean 模块的项目导入闭包共 15 个模块，与该工作区在忽略行尾空白/换行差异后全部一致，
外部导入仅 `Mathlib` 和 `Mathlib.Tactic`；目标的 9 个依赖 URL/锁定版本及工具链相符。
三个公开 Python 入口均已在该工作区成功复跑，结果与开发区一致；没有在此重新构建 Lean。

## 发布核对 — 2026-11-07

本次发布目标为 `huam54925-cpu/uav-routing-certification` 的既有
`research/structural-service-cuts-20261023` 分支，以 `86993ec` 为父提交，
通过既有系统代理使用普通提交和非强制推送。发布内容为四个新 Lean 模块、
一个公开审计源、三个有限检查 Python 源、新 A/B LaTeX 文稿、两份新说明、
原语义状态文档的导航补记及 README，共 13 个文件。

发布复用本记录中的成功构建、78 声明公理审计和有限检查；此次上传没有重新执行
Lean 构建、远端 CI、性能测量或 LaTeX 编译。交付 Lean、审计和 Python 源与验收版本
逐字节相同，状态文档仅补充发布说明。原始日志、生成 JSON、构建产物和下载材料不纳入提交。
旧 Lean、工具链、依赖锁定、冻结输入及两份旧 LaTeX 文稿保持不变；
编解码/长度形式化及其余未完成项按前述范围保留。
