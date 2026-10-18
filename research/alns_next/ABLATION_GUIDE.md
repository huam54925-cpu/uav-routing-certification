> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68/research/alns_next/ABLATION_GUIDE.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# 邻域第二版：接入修复与小预算消融

基于运行版本 36bd8b0，保持原题约束、输入和独立校验器不变。本提交只修改代码与指导，不上传用户原始六小时快照，不启动远端长实验。

## 修复内容

- `alns_solver.main(solver_cls=Solver)` 接收求解器工厂。`run_variant.py` 导入同一入口及同一 Solver 模块，不再复制整个求解器；初始化超时由同一个 BudgetExpired 类捕获。
- 联合破坏是第 5 类独立破坏算子，分别与 greedy/regret2 配对并维护独立权重。空间破坏不再混入随机联合分支。
- 四组：baseline（原邻域）、joint（仅联合破坏）、cross（仅交换强化）、both（组合）。默认原入口及 run_remote.py 仍运行 baseline；本提交未把新算法自动接入远端守护器。
- joint 保留原强化次数；cross/both 把 120 次强化提案预算分成原强化 60 次和 Cross-exchange 60 次。这比较的是预算重分配政策，不是保持旧强化全部调用后额外新增交换的纯增量效果。可在后续增加半预算旧强化对照，进一步区分算子与预算影响。
- 小实例质量检测只从明确非最优路线出发；300 次修复直接触发 mode=4，避免未覆盖联合分支。

## 统计含义

每个输出中 `operator_names` 与 `operator_stats` 一一对应：attempts、repair_successes、repair_failures、accepted、archive_improvements、destroy_repair_seconds、intensify_seconds。

这些 accepted/archive_improvements 是该破坏修复组合经过整个强化流程后的接受和档案贡献，不可归因于某一个局部移动。截止时间可能打断一个尝试，因此 attempts 不必等于修复成功与失败数之和。

`diagnostics.cross` 单独记录 proposals、legal、score_improvements、seconds。合法率为 legal/proposals，局部改善接受率为 score_improvements/legal（分母为零记 NA）。局部接受标准是加权评价 F，不能直接当作 Tmax 降低或最终档案刷新。joint_calls 给出联合破坏调用数，修复成功率与后续档案贡献在对应独立 pair 的 operator_stats 中查看。

## 本轮已做检查

- 原有七项测试全部通过（本环境约 9.26 秒）。
- 修订小实例：30 个非最优起点全部观测到 Tmax 严格下降，300 次修复检查通过；穷举最优 Tmax=0.3377895840862944 h，观测最好值在浮点容差内相同。只说明该五副本两机实例的行为。
- 四组入口的极小初始化预算均正常退出码 2，提示预算不足，无 Traceback；不再使用重复异常类。
- 从 Case 3 六小时档案启动四组各 2 秒的接入检查，结果均经独立校验；该预算不用于评价算法收益。
- 用户提供的第一版三种子、每版每种子 30 秒记录：两版 Tmax 均为 9.403611015410183 h，未改善；属于用户反馈，未将其本地文件冒充为本仓库已读取原始记录。

## 本地运行

使用 Python 3，标准库即可。在本目录执行：

```bash
python3 -m unittest -v test_solver.py test_remote.py test_neighborhood_entry.py
python3 check_neighborhood_core.py
```

先单独跑新版（将路径替换为本机真实的 best.json 路径）：

```bash
python3 run_variant.py --variant both --case Case3 --fleet 4 \
  --warm /absolute/path/to/Case3/best.json --seconds 30 --seed 0 \
  --out /tmp/case3_both_check.json
python3 validate.py /tmp/case3_both_check.json
```

再做三种子、四组、每次 600 秒的串行对照：

```bash
python3 -u run_ablation.py \
  --warm /absolute/path/to/Case3/best.json \
  --out /absolute/path/to/NEW_ablation_output \
  --seconds 600 --seeds 0 1 2
```

总搜索预算约 2 小时，外加启动、保存、校验开销。输出目录必须不存在，防止覆盖实验。所有运行均从同一冻结热启动档案出发，不交换新结果；每个种子轮换四组执行顺序，三个种子无法完全平衡四种位置。相同种子并不保证不同算法走相同随机轨迹。

每次结束写入 summary.json；各组完整输出、检查点及日志分别保存，experiment.json 保存源码指纹和预算。非零退出记录并继续其他组，最终比较前应检查每一条 validated=true；非零退出不代表数学不可行。本脚本开启原入口的检查点 I/O，与用户此前关闭 I/O 的 30 秒试验不是同一吞吐测量条件。预算超时后的外部兜底杀进程只用于异常执行，已有检查点保留。

暂不建议再次六小时长跑。先核对单项是否有收益、耗时占比与候选合法率，再决定扩大预算；代码正确不等于算法有效，局部得分改善也不等于九小时可行。
