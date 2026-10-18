# 固定版本、核验入口与实际状态

## 历史结果和本次迁移的区别

Lean 证明基线是原仓库提交 `0d4466cbfacf3fe01ca98494663742f9a612b645`。13 个模块在原固定依赖环境中已有编译及公理审计记录，最后四个模块使用已有前序产物完成检查；十个关键定理的传递公理仅有 `propext`、`Classical.choice`、`Quot.sound`。见[历史报告](CASE1_KERNEL_CLOSURE_STATUS.md)。

四机可行性采用用户在 2026-10-18 提供的独立验证 PASS，退出码为 0；本次补收验证器及其固定输入。迁移不重新运行这些检查，也不声称已经完成干净环境重建。

本仓库新增独立 Lake 配置，沿用 Lean `leanprover/lean4:v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 及其原锁定依赖。新包只包含 UAV 模块，原 JSP/Prim 工程不迁入。配置已按现有依赖整理，但下述新包构建流程尚未在本次迁移中执行。

## Python 独立核验（命令供复现）

在仓库根目录执行。Windows 用 `py -3`，Linux/macOS 可换成 `python3`。下列四项只使用 Python 标准库，不需要求解器、SciPy 或 Lean。

```powershell
py -3 LeanCompletion/UAV/certificates/bind_case1_data.py --check
py -3 LeanCompletion/UAV/certificates/verify_case1_costs.py
py -3 LeanCompletion/UAV/certificates/verify_bound_certificate.py LeanCompletion/UAV/certificates/bound_Case1.json --case Case1 --fleet 3
py -3 LeanCompletion/UAV/certificates/verify_case1_feasible.py --instances LeanCompletion/UAV/certificates/instances.json --solution submission_package/question1/results/solution.json
```

依次检查 JSON 与 Lean 字面量绑定、保守整数距离对应、三机精确下界证书和四机可行见证。任何一步的退出码非零都应停止并调查；`--write` 会改写固定 Lean 字面量，不用于复现已冻结结论。

## Lean 构建与公理审计（尚未在新仓库执行）

安装 elan 后，从仓库根目录执行：

```powershell
lake exe cache get
lake build LeanCompletion.UAV.Case1Infeasible
lake env lean verification/Case1Audit.lean
```

Lake 将按锁文件获取依赖；缓存用于 mathlib，具体证书数值仍需 Lean 内核归约。数值模块可能需要较多时间与内存。保留命令退出码及完整输出到本地 `verification/runs/`，不要把旧 PASS 当作这次构建的输出。将来若新包构建失败，应记录失败并修复配置，不能反向声称旧环境证明失效或新包已验证。

## 固定输入身份

| 对象 | SHA-256 |
| --- | --- |
| `LeanCompletion/UAV/certificates/instances.json` 文件 | `f9b2286f61c3878629ae3f2ba1f3764133c5b8051e884a97fecb22110c7904c7` |
| `LeanCompletion/UAV/certificates/bound_Case1.json` 文件 | `d2edb19ba8e1f741c4af05a4636798520a25b219580c0102621946d2d3dd849a` |
| `submission_package/question1/results/solution.json` 文件 | `344769068ebac95a32613ebb33caee785878b44fe3371c68d59d04d8d570d77a` |
| Case1 规范化对象（`json.dumps(case, sort_keys=True)`） | `8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8` |

文件哈希和对象指纹是不同对象。固定 JSON 保留原始字节，包括换行；`.gitattributes` 禁止自动转换这些输入，避免破坏绑定注释中的文件哈希。

## 原论文程序和历史研究

问题一至三分别保留自己的 requirements、输入、程序与参考结果；按各目录 README 使用。历史源码中的外部 Node 库或服务器路径需要按原说明准备，不声称所有研究命令无需配置即可执行。

ALNS 研究源码、已选择的证书和候选档案在 `research/`。旧的三小时自动启动脚本依赖未迁入的原始 ZIP 和运行清单，具体限制见[研究材料说明](../research/README.md)。本次没有重启搜索，也没有以搜索失败作为不可行性证据。

论文 PDF 是已发表的参考文件，未重新生成。原稿与修正稿的排版输入说明见 [paper/original](../paper/original/README.md) 和 [paper/revised](../paper/revised/README.md)。
