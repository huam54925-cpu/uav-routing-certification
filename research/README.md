# 后续研究材料

本目录保存从启发式探索到严格下界证明的研究过程。当前 Case1 最小机队结论见[首页](../README.md)；旧文档中的目标和状态属于各自日期。

| 材料 | 作用 |
| --- | --- |
| [重复巡检边界审计](boundary_audit_20261016/README.md) | 修正原邻接下界，保留反例和重算程序 |
| [六小时研究报告](alns_next/SIX_HOUR_REPORT_20261015.md) | 记录早期 ALNS 结果与局限 |
| [三小时研究记录](alns_next/results/20261016_three_hour/README.md) | 保存后续实验结论及精选见证、证书 |
| [连通性证书说明](alns_next/BOUND_PROOF_20261016.md) | 从搜索转向可检验的距离下界 |
| [ALNS 原始指南](alns_next/README.md) | 算法、邻域、远端队列与消融研究的历史说明 |

研究代码采用 `results/alns-three-hour-20261016` 的已发表版本，另收录六小时报告分支的报告和快照验证脚本。原九个分支的精确来源见[来源表](../docs/SOURCES.md)。

固定的 `best_Case1.json`、`best_Case3.json` 是历史任务副本格式的候选档案，不能当成四机物理点编号的可行见证。`bound_Case*.json` 与 `case*_connectivity_bound.json` 是原研究中选定的证书记录。Case3 不因此获得最小机队的证明。

旧指南中的 ZIP 快照、状态/进度 JSON、校验输出和自动生成的运行清单没有迁入；对应链接指向原固定提交。`start_three_hour.sh` 保留为历史启动代码，它依赖旧环境的 `inputs/*.zip`、`THREE_HOUR_INPUTS.json` 和校验清单，**不是本仓库开箱即用的启动入口**。若要重建该历史实验，须先从原档案恢复输入并按旧指南准备环境；本次没有重启队列或补跑实验。

新仓库可直接定位的独立验证命令见[复现说明](../docs/REPRODUCIBILITY.md)。以后的实验输出放在忽略的 `verification/runs/`，不要覆盖这些历史参考材料。
