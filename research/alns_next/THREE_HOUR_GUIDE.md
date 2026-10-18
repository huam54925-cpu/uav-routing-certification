> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68/research/alns_next/THREE_HOUR_GUIDE.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# 三小时研究队列（2026-10-16）

适用此次已核查的Runpod：CPU配额12.75核、内存约109 GiB。最多12个单线程工作进程；不要按宿主机nproc=120设置。启动器核查cgroup配额，低配时拒绝过量并发。50 GB空间足够本实验，但overlay目录不是已确认的持久化存储，删除Pod之前必须下载结果。

## 新发现与计算分配

本轮开发短测已得到**Case1 N=3 的有效下界9.020600633 h**。在原题固定模型下超过9小时；结合原有小机队排除结果和已验证的4架可行方案，Case1可确定Nmin=4。独立、仅标准库的精确有理数证书验证通过，详见BOUND_PROOF_20261016.md。Case3下界升至8.321550885 h，仍未确定N=4是否可行。

因此不应机械耗费两路算力继续找Case1三架方案。实际调度如下：

1. 首先两路分别重算Case1/Case3连通性下界，单任务上限600秒，完成或没有新割即结束。其余槽位立即开始路线搜索，不等下界任务、不留空闲批次。
2. 下界经过独立精确证书校验，若确认对应固定N不可能在9小时完成，则终止该N的活动搜索并把槽位分配给另一个未决算例。按本地已验证结果，远端很快会将全部12路投入Case3。
3. 路线变体轮换：baseline（原ALNS）、both（此前联合破坏+段交换）、regional（两路线同区域成组移除）、balanced（两路线同时移除片段）、wide（较大成组破坏及最大8任务段交换）。5个变体按lane取模分配，有原版对照。新增变体在同一次操作中调整两路线，并在修复与评价中计入服务时长和超时。
4. Case3的点10及11—36—57—47区域有40%机会成为新增区域破坏中心，其他中心随机选择；路线对偏向共享巡检点，但仍允许其他配对。全局最优档案每三轮共享，其余轮次延续本轨迹档案；种子随lane和轮次变化。每轮10分钟，可调slice-seconds；不是精确随机状态恢复。
5. 约每10秒写工作进程检查点、每5秒聚合独立校验后的结果；每小时快照。失败任务不覆盖好结果，连续失败2次的轨迹回退原算法，5次停止该轨迹；下界进程失败则释放槽位，不把数值失败当不可行证明。没有新割时也释放槽位，不反复重算同一LP。
6. 总时间是正式队列首次启动后的3小时（依赖安装、测试不占这3小时）。暂停期间计入截止时间。到期停止计算，允许约15秒子进程收尾及结果压缩时间，生成download_results.zip。**不关机、不删除Pod，不自动处理云平台计费。**

并行探索不是严格配对消融；种子、变体、迭代、算子效果、每轮预算均记录。只比较可靠改善，不能把短测无改善解释为算法无效。新增邻域尚无完整Case3收益证据。

## 下载、准备并启动（Runpod root终端）

```bash
set -e
git clone --depth 1 --single-branch --branch research/alns-three-hour \
  https://github.com/huam54925-cpu/Drone-Issues.git /root/uav-three-hour
cd /root/uav-three-hour
bash research/alns_next/start_three_hour.sh
```

分支包含最新远端监督、邻域第二版、下界审计、本次代码及inputs/case1.zip、inputs/case3.zip。两个ZIP直接复用仓库已有快照blob，未改内容。启动器校验代码与输入SHA256，创建独立venv，安装numpy2.1.2/scipy1.15.3，执行短测试，再用nohup启动12路队列。若/root/uav-three-hour已存在，不要覆盖正在运行的代码；先检查现有目录。

若系统提示venv不可用，先安装python3-venv后重试。无需安装GPU库、OR-Tools或单独highspy。

## 查看与下载

```bash
RUN=$(cat /root/uav-three-hour/LATEST_RUN)
cat "$RUN/progress.json"
tail -n 30 "$RUN/console.log"
```

progress的bounds显示经过精确校验的下界及excluded_9h。best_makespan_violation_h与best_violation_h分别对应不同档案，不可拼成同一方案。原始启发式档案可能仍标UNKNOWN；排除结论单独在bound_Case1.json，不篡改历史搜索档案的状态。

脚本通过nohup、后台运行和标准输入重定向启动；终端回到提示符后，可以关闭网页。Ctrl-C只会影响当前前台命令，例如tail -f，不会正常地向已分离的后台队列发送信号；它不是防止Pod关机、进程被杀或平台中断的保障。

完成后在Jupyter文件页进入LATEST_RUN指向的目录，下载download_results.zip。该ZIP包含最终内部编码路线、物理点编号路线、下界证书、任务日志和状态，可供之后复核或继续研究。每小时及结束时还有独立快照。所有数据下载后再释放实例。

## 暂停和恢复

```bash
RUN=$(cat /root/uav-three-hour/LATEST_RUN)
touch "$RUN/STOP"
```

等待progress.status=paused后下载结果。需要继续且原3小时窗口尚未结束时：

```bash
RUN=$(cat /root/uav-three-hour/LATEST_RUN)
rm "$RUN/STOP"
nohup /root/uav-three-hour/.venv-research/bin/python -u \
  /root/uav-three-hour/research/alns_next/run_three_hour_queue.py \
  --out "$RUN" --workers 12 --port 0 \
  >> "$RUN/console.log" 2>&1 < /dev/null &
```

原预算与参数保存在state.json，恢复不会重新获得3小时。输出目录互斥锁防重复启动；突然杀死监督器留下的工作进程尚未结束时，拒绝重叠恢复。子进程有切片期限，等结束后再恢复；不是宿主机重启自动恢复服务。源码变化要求新输出目录。

## 验证范围

新增测试覆盖成组破坏的副本完整性、删除接缝、修复/强化后合法性、随机不可行对偶的保守修正、证书篡改拒绝；真实进程测试覆盖子进程被杀、同目录重复启动拒绝、暂停恢复、原截止时间、最终ZIP与独立路线校验。实际Case1/Case3短测下界记录随代码保存。本地短测不等于已运行三小时，不保证Case3一定改善。
