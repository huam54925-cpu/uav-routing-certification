> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../../../../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68/research/alns_next/results/20261016_three_hour/README.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# 2026-10-16 三小时远端结果归档

原始用户上传ZIP逐字节保存，未重打包或修复历史数据。运行代码提交：6844290aa15c40eb6163c05dcd2afe9cb8c5c669。CPU配额12.75、12个worker，运行3.001639小时。208个任务done，12个interrupted，0个failed；这些计数不包括最终打包异常。

## 已复核的核心结果

- Case1/3最佳路线档案结构、访问次数、邻接规则及重新计算时间通过独立验证；均没有9小时可行见证。
- 两份连通性下界证书通过独立精确有理数验证。Case1 N3下界9.020600633333334h，排除3架；结合之前已验证4架可行方案，当前模型下Nmin=4。
- Case3 N4下界8.321550884848484h，已知最好Tmax仍9.403611015410183h，未观察到实质改善，仍4≤Nmin≤5。V最后几位变化不计为改善。
- ZIP中215个路线任务result.json逐一通过独立校验，208个已完成任务的结果全部存在。两个bound结果另行验证。

## 打包异常及完整性限制

用户服务器日志显示程序最后在zipfile.write → shutil.copyfileobj → read期间抛出FileNotFoundError。ZIP正常关闭、CRC测试通过，但归档提前结束；CRC通过不等于完整备份。

已确认：jobs/00216_exploration_Case3_balanced_1792157286279009645/result.json.checkpoint.json为0字节，无法解析；同任务的result.json存在且通过校验。217、218、219号任务均为截止中断任务，它们的result.json未收入本包。不能根据本包判断这些文件在服务器上是否存在，也不能从报错确定底层文件系统原因。

核心best、bound、progress、state均存在，另以普通JSON存放，方便查看。原始ZIP、全部条目清单和缺失清单见manifest.json。该归档不应称为“无异常完成”或“全部末轮日志完整”。原console.log按原打包规则未收录，用户已提供上述异常栈。

SHA256：`556f01282f1d4f0b83a78d9574f05b0cade7b3f3edc8503eaeeec442cff66a1f`。
