# 材料来源与分支归并

整理日期：2026-10-18。目标仓库为 [uav-routing-certification](https://github.com/huam54925-cpu/uav-routing-certification)，原项目为 [Drone-Issues](https://github.com/huam54925-cpu/Drone-Issues)。核对时原仓库有下列九个分支，以下均使用固定提交链接。

| 原分支 | 固定提交 | 本仓库处理 |
| --- | --- | --- |
| `codex/uav-lean-proofs-20261018` | [`0d4466c`](https://github.com/huam54925-cpu/Drone-Issues/tree/0d4466cbfacf3fe01ca98494663742f9a612b645) | 13 个 Lean 模块、两份证书辅助脚本和五份证明阶段说明。 |
| `docs/alns-six-hour-results-20261015` | [`bd9fa53`](https://github.com/huam54925-cpu/Drone-Issues/tree/bd9fa5317220a8f9b5adda9a7d90467d636c9553) | 六小时研究报告及快照验证源码；原始 ZIP/快照仍在旧档案。 |
| `fix/alns-remote-supervision` | [`36bd8b0`](https://github.com/huam54925-cpu/Drone-Issues/tree/36bd8b0d9c4bc0a8e846c0cb965bc6eb29352cee) | 远端守护、校验和恢复改进；采用后续结果分支中的版本。 |
| `fix/repeated-visit-bound-audit` | [`c5a93f6`](https://github.com/huam54925-cpu/Drone-Issues/tree/c5a93f6cbda182263d687483672004dad5e89197) | 修正论文 main.tex 单独保存；下界程序及审计材料采用后续结果分支中的版本。 |
| `main` | [`01f0b0a`](https://github.com/huam54925-cpu/Drone-Issues/tree/01f0b0a1e12d37c9cf56cb06a4b0a559ed36a126) | 原论文、图件、题目和问题一至三交付包的基线。 |
| `research/alns-neighborhood-ablation-v2` | [`bd5ccbb`](https://github.com/huam54925-cpu/Drone-Issues/tree/bd5ccbb84ef7259336809c772696494e775c5c89) | 邻域与消融研究源码；采用后续结果分支中的版本。 |
| `research/alns-six-hour-queue` | [`9295ae5`](https://github.com/huam54925-cpu/Drone-Issues/tree/9295ae52b876a97a5acfb6bc19b150bb4d102e00) | 六小时队列源码与指南；采用后续结果分支中的版本。 |
| `research/alns-three-hour` | [`6844290`](https://github.com/huam54925-cpu/Drone-Issues/tree/6844290aa15c40eb6163c05dcd2afe9cb8c5c669) | 三小时队列的运行代码基线；其相关源码与结果分支一致。 |
| `results/alns-three-hour-20261016` | [`5cd608f`](https://github.com/huam54925-cpu/Drone-Issues/tree/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68) | ALNS 研究目录、边界审计、精选证书和候选路线，以及问题一下界修复的整合基线。 |

## 文件与版本对应

- `paper/original/`：原 main 提交中的 `main.tex`、`main.pdf`、附录、参考文献、`figures/` 和 `generated_figures/`，原字节保留。
- `paper/revised/main.tex`：重复巡检边界修正提交的原文件，未重写原论文、未重新生成 PDF。
- `source_materials/problem_A/`：原 main 的 PDF 和 Excel 输入/模板，README 增补迁移说明；原文件清单通过固定提交链接保留。
- `submission_package/`：原 main 的问题一至三程序和已发表参考结果；问题一的 `program/run.py`、`program/src/uav_q1/lower_bounds.py`、`program/tests/test_lower_bounds.py` 使用 `5cd608f` 的下界修复版本。原始 `search_report.json` 未迁入。
- `research/`：通常取 `5cd608f` 的源码与文档；`SIX_HOUR_REPORT_20261015.md`、`results/20261015_six_hour/validate_snapshot.py` 来自 `bd9fa53`。移除运行产物后，历史文档增补范围提示，缺失附件的 Markdown 链接改指原固定提交。
- `LeanCompletion/UAV/*.lean`：13 个文件来自 `0d4466c`，证明正文不改动。证书辅助脚本 `bind_case1_data.py`、`verify_case1_costs.py` 同源。
- `LeanCompletion/UAV/certificates/bound_Case1.json`、`instances.json`、`verify_bound_certificate.py`：对应 `5cd608f` 的固定证书、实例和独立验证器；保留邻接目录是原脚本接口需要。
- `LeanCompletion/UAV/certificates/verify_case1_feasible.py`：来自原本地验证工程；此前证明分支尚未收录。它读取已发表的 `submission_package/question1/results/solution.json`。
- `verification/Case1Audit.lean`：来自原本地证明阶段的十项公理审计源码；不附原始输出。
- 五份旧证明状态文档来自 `0d4466c`，保留历史正文并增补迁移提示。首页、目录导航、来源、时间线、模型对照、复现说明和阶段报告提纲为此次整理新增。

## 工具链与独立工程

保持 Lean `4.30.0-rc2`，mathlib 固定为 `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。新 Lake 工程只声明 UAV 证明实际使用的 mathlib 依赖，不迁入无关的 JSP/Prim 证明。锁文件使用原验证环境的 mathlib 提交及其八个依赖提交；独立工程入口与包名是此次新增，尚未执行新环境构建。

## 保留的证据边界

这次汇集文件，没有将九个分支机械合并或重写原历史。旧分支源码仍可由上表追溯。原 ZIP、完整队列状态、日志、运行清单、聊天/API 内容、LaTeX 临时文件、依赖源码和编译缓存不随迁移发布。

程序运行产物不会因为改名变成可提交材料。本次保留的参考 JSON 用于原交付包、候选见证或精确证书输入，详见[发布规则](REPOSITORY_POLICY.md)。迁移检查仅确认文件与选定来源对应，不能替代数学验证或全新环境复现。

创建新仓库时已有的 Apache-2.0 许可证保持不变；原论文、题目及附件的作者和来源说明保留，第三方材料不据此重新授权。
