# 原论文档案

本目录保存原仓库 `main` 的固定提交 [01f0b0a](https://github.com/huam54925-cpu/Drone-Issues/tree/01f0b0a1e12d37c9cf56cb06a4b0a559ed36a126) 中的论文、附录、参考文献和图件。

- [main.pdf](main.pdf)、[main.tex](main.tex)：当时发表的论文版本。
- [附录 PDF](appendix%20%282%29.pdf)、[附录源码](appendix%20%282%29.tex)。
- `figures/`、`generated_figures/`、`references.bib`：原有支撑材料。

原 PDF 是历史产物，本次没有重新排版。原论文中 Case1 的候选状态、部分旧下界推导应结合[修正稿](../revised/README.md)及[后续证明时间线](../../docs/RESEARCH_TIMELINE.md)阅读，不能作为当前最终数学结论。

TeX 源码保留原字节和相对路径；其中代码清单还会引用 `submission_package/`。若以后重排，请将所选 TeX、参考文献和图件复制到忽略的构建目录，并在该目录放置所需版本的 `submission_package/`。要精确复原原始代码清单，应取上述固定提交的程序；新仓库的问题一程序包含后续下界修正。此次没有执行 LaTeX 构建。
