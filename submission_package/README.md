# 问题一至三：程序与历史参考结果

| 目录 | 内容 |
| --- | --- |
| [question1/program](question1/program/README.md) | 模型、启发式/精确模型、输入、测试和运行入口 |
| [question1/results](question1/results/README.md) | 原论文四个 Case 的已发表路线和结果表 |
| [question2/program](question2/program/README.md) | 固定问题一机队与时间上界的均衡优化 |
| [question2/results](question2/results/README.md) | 均衡结果、JSON、CSV 和工作簿 |
| [question3/program](question3/program/README.md) | 算法 A/B、逐事件验证和图表构建 |
| [question3/results](question3/results) | 算法 B 正式结果、算法 A 对照及路线明细 |
| [question3/results_enhanced](question3/results_enhanced) | 原增强版附件，保留程序兼容路径 |

材料以原 main 提交 `01f0b0a` 为基础。问题一 `run.py` 与 `lower_bounds.py`、`test_lower_bounds.py` 使用后续 `5cd608f` 的重复巡检下界修复版本。其余源文件和参考结果保留原字节；本次没有运行程序或重生成结果。

问题二读取 `question1/results/solution.json`。该文件也包含已独立验证的 Case1 四机见证；原文件中机队最优性等状态字段是历史算法状态，没有为了匹配今天的结论而改写。当前数量证明见[仓库首页](../README.md)。

问题三固定机队 `N0=(4,2,5,4)`，算法 A 为对照，额外机队用于敏感性分析。已有结果的可行性核验不等于全局最优性证明。

各目录中的历史说明仍可能引用当时的运行输出；未迁入的日志、搜索汇总等通过[原提交](https://github.com/huam54925-cpu/Drone-Issues/tree/01f0b0a1e12d37c9cf56cb06a4b0a559ed36a126)追溯。新运行应将输出保存到忽略的 `verification/runs/`，不要覆盖已归档参考文件。
