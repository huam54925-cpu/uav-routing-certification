> 历史材料迁移说明（2026-10-18）：下文保留原阶段的研究结论与检查记录，不代表此次迁移重新运行。当前状态见[新仓库首页](../../README.md)；原始版本见[固定提交](https://github.com/huam54925-cpu/Drone-Issues/blob/5cd608f837569d447b2ebc0d3c4d5e1b919dfa68/research/alns_next/BOUND_PROOF_20261016.md)。未迁入的运行产物仍在原档案，文中的旧启动命令可能需要恢复原环境。

# 连通性下界与Case1三架排除证书

## 模型

沿用附件1坐标、基地0、单位0.1 km、速度55 km/h、每次巡检5分钟、访问次数3/2/1、同机允许A→B→A、不同机访问同点各计一次、每条非空路线出发与返回基地且中途不回库。所有结果只针对这一模型。

令物理点i所需访问次数为r_i，基地度r_0=N。将N条实际路线的有向边按物理端点聚合为x_ij。无相邻同点访问，因此无自环；每点流出和流入均为r_i，且0≤x_ij≤min(r_i,r_j)。对不含基地的任意非空物理点集合S，至少有一条边离开S，否则这些访问不能属于基地往返路线。因此Σ_{i∈S,j∉S}x_ij≥1是必要约束。允许前后邻居同一物理点，没有使用错误的“两个不同邻居”假设。

放松x的整数性并仅加入部分这样的割，最小化总飞行距离，可得原问题总距离的下界。按当前LP解的各任务点到基地最小割，寻找被违反的集合，重复求解。任意选择的合法非空集合都是有效割；分离的浮点误差最多影响找到哪些割，不使割无效。

## 数值证书怎样成为严格下界

距离先用精确十进制有理数和整数平方根向下取整到10^-6 km。写松弛为Ax=b、Gx≤h、0≤x≤u。对任意等式乘子y和不大于0的不等式乘子z，令q=c−Aᵀy−Gᵀz，则

L=bᵀy+hᵀz+Σ_e min(0,q_e)u_e ≤ cᵀx。

这是直接代入约束得到的不等式，不要求浮点对偶“近似可行”。程序将求解器乘子的实际二进制浮点值精确转为有理数，对偶不等式乘子投影到非正半轴，逐边计算残差补偿。独立脚本verify_bound_certificate.py不导入SciPy、生成器或其距离代码，重新计算距离、上下界、乘子符号、每条残差及最终时间分数。

## 实测

| 算例/固定N | 初始循环覆盖时间界/h | 新有效时间界/h | 割数 | 结论 |
|---|---:|---:|---:|---|
| Case1/3 | 8.458415479 | 9.020600633 | 32 | 3架不可能全部≤9h |
| Case3/4 | 7.863543494 | 8.321550885 | 90 | 尚不能排除4架 |

Case1得到总距离下界1158.3991045 km，服务总时长6小时，因此平均单机时间至少

(6+1158.3991045/55)/3 = 9.020600633333… h > 9 h。

已有更小机队排除证据、4架可行方案重新通过原独立校验，因此在上述模型下Case1的Nmin=4。Case3仍为4≤Nmin≤5。Case2和Case4维持2和4。没有证明已知路线Tmax全局最优，也没有使用“搜不到”作为不可行依据。

记录在research_results_20261016/case1_connectivity_bound.json、case3_connectivity_bound.json。开发机器上运行时间分别约0.34秒和0.96秒（不含Python导入时间），是有限松弛的计算，不是穷举原问题。Case1首次严格超过9h即停；Case3没有新连接割即停。不同SciPy版本可能产生不同最优对偶与割顺序，但任何被用于排除的结果必须独立通过同一有理数证书校验。

复核命令（在research/alns_next下）：

```bash
python3 verify_bound_certificate.py research_results_20261016/case1_connectivity_bound.json --case Case1 --fleet 3
python3 verify_bound_certificate.py research_results_20261016/case3_connectivity_bound.json --case Case3 --fleet 4
```

LP接口依据：[SciPy linprog官方文档](https://docs.scipy.org/doc/scipy/reference/optimize.linprog-highs.html)。这里的数学保证来自上述残差修正公式及独立验证，不来自求解器的success标志。失败、超时、数值infeasible不自动视为原题不可行。
