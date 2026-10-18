> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68/research/alns_next/SIX_HOUR_QUEUE_GUIDE.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# 16 vCPU 六小时无人值守队列

本方案适用于 Linux / Python 3，只用标准库，CPU 计算，不使用 GPU。建议 16 vCPU 实例，默认最多 8 个计算进程。实例标价 $0.61/h 时六小时约 $3.66，平台存储等费用另计；脚本不会代替用户购买或关闭云实例。

## 算法与预算

总截止时间为首次启动后的六小时，包含各任务开销及中途暂停时间，恢复不重新获得六小时预算。正常到时结束计算、保存最终结果，不关机、不删除实例；云实例继续计费，用户需在控制台处理。

1. Case 3 四组比较：baseline / joint / cross / both，各种子 0/1/2，每次 600 秒。每批四个变体并行，同一个种子全部结束再启动下一批；正常约 30 分钟。并行共享资源会影响吞吐，这不是隔离硬件性能测试。失败任务最多尝试两次，重试会增加耗时并减少后续预算。
2. 剩余约 5.5 小时探索：默认 8 条轨迹，Case 3 六条、Case 1 两条；每段 600 秒。按轨迹交替使用 max/violation 侧重，部分轨迹定期冷启动，其余继承本轨迹档案。全局最好结果持续聚合保存，但不反向覆盖所有轨迹的起点。
3. 自动分配只是预算启发式：增强版本至少在两个种子上同时优于对应 baseline 和冻结初解，才向它分配两条 Case 3 额外轨迹。若无此证据，维持轮换配置。失败或被总截止时间截短的比较不参与优选。三个种子不构成统计显著性证明。
4. 所有阶段保持原题约束。未找到九小时方案记 UNKNOWN；找到后独立校验并保留见证，默认继续优化至总截止时间。没有在此队列中声称实现下界证明、精确求解或 Ejection chain。

每次任务输出独立目录及独立日志；约每五秒聚合合法检查点并写状态，每小时快照，结束或暂停时另存 final_*。一个进程失败不立即结束整个队列；探索轨迹连续三次失败后停用该轨迹，其他轨迹继续。所有探索轨迹都失败则保存为 paused，不能误报完成。磁盘耗尽、宿主机故障仍可能中断整个程序。

## 获取代码和昨天的输入

建议在新实例使用 Ubuntu 24.04 LTS；安装 Python 3 与 Git 后，在用户可写且持久化的目录执行。下面使用 ~/uav-queue（已存在时请换一个新目录）。

```bash
git clone --single-branch --branch research/alns-six-hour-queue \
  https://github.com/huam54925-cpu/Drone-Issues.git ~/uav-queue
cd ~/uav-queue
git fetch origin docs/alns-six-hour-results-20261015
mkdir -p inputs
git show FETCH_HEAD:research/alns_next/results/20261015_six_hour/snapshot_1792064931712292139.zip > inputs/case1.zip
git show FETCH_HEAD:research/alns_next/results/20261015_six_hour/snapshot_1792064928918013842.zip > inputs/case3.zip
cd research/alns_next
sha256sum -c SHA256SUMS.txt
python3 -m unittest -v test_solver.py test_remote.py test_neighborhood_entry.py test_six_hour_queue.py
```

上述每条命令确认成功再继续，或放在带 `set -e` 的子 shell 中执行。队列可直接读取快照 ZIP，无需解压；启动时验证 Case1/3、机队数、实例指纹及档案合法性。

## 启动六小时任务

在 research/alns_next 中执行；建议输出目录包含日期且与其他运行分开。

```bash
mkdir -p runs/queue_20261016
nohup python3 -u run_six_hour_queue.py \
  --case1-warm ../../inputs/case1.zip \
  --case3-warm ../../inputs/case3.zip \
  --out runs/queue_20261016 --hours 6 --workers 8 \
  --paired-seconds 600 --slice-seconds 600 --port 8765 \
  > runs/queue_20261016/console.log 2>&1 < /dev/null &
```

一分钟后查看：

```bash
cat runs/queue_20261016/progress.json
```

paired 阶段通常 4 个工作进程，exploration 阶段通常 8 个；换轮时数量会短暂变化。关注 remaining_hours、completed_jobs、failed_jobs、issues 与 best。不要因看见 main 分支没有脚本而换回旧入口；本脚本基于邻域第二版分支。

HTTP 状态只绑定服务器 127.0.0.1:8765。可以通过 SSH 转发查看：本机执行 `ssh -N -L 8765:127.0.0.1:8765 用户@服务器IP`，然后访问本机 http://127.0.0.1:8765 。无需为此向公网开放 8765。

## 暂停、恢复和完成

```bash
touch runs/queue_20261016/STOP
```

等待 progress.json 的 status=paused。恢复时删除 STOP，再执行相同启动命令（输入已被冻结；已有配置优先）。截止时间沿用首次启动时刻，离线期间也计入六小时窗口。status=completed 的目录不会重新启动；开展新实验必须换输出目录。

启动目录有互斥锁；不会同时运行两个同目录队列。突然杀死监督进程后，如果先前子进程仍在运行，新启动会拒绝重叠，请等其有限时段完成后再恢复。没有配置宿主机重启后的自动启动服务，脚本不会暗示已经运行六小时或自动恢复了整机故障。

总时限到达时允许约 15 秒收尾。最后一段可能标记 interrupted，但已通过校验的检查点仍会聚合保存。重启不会覆盖已完成的对照任务。

应下载整个运行目录，至少保留：

- best_Case1.json / best_Case3.json：内部任务编码，供独立校验与续算。
- physical_Case1.json / physical_Case3.json：真实巡检点编号路线。
- paired_summary.json：四组对照及失败记录。
- state.json：各任务预算、种子、变体、路径、退出状态及代码指纹。
- progress.json、final_*、jobs/：完成状态、最终备份、各轮详细输出和日志。

这一队列比较的是既有核心算法和不同起点，不能替代下界审计。六小时结束后先检查对照与新起点是否有收益，再决定是否继续租机。
