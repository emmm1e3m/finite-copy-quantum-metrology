# 作者校阅说明

本稿按 PRA Regular Article 整理。主线是：通过宽度随自旋位置变化、逐列严格归一的高斯种子，构造每个有限拷贝数都完备且局部无偏的测量方案，确定最大混合态处双参数量子比特估计的首个有限拷贝修正系数 √(8/π)。

本轮优化了摘要与引言的推进关系，在正文解释宽度选择、完整性和 Schur 平均之间的联系；新增独立“讨论”，结论压缩为中心问题的回答。完整技术证明保留在附录。图采用共用的英文矢量文件和英文图注，文献由共用 `references.bib` 与 `apsrev4-2` 样式生成。

科学结论、适用条件、展示公式和原有数值保持一致。本轮未发现需要作者改变结论的实质矛盾；有限 N 最优种子的闭式表达、更高阶系数及严格间隙的精确衰减幂律仍属原稿的后续问题。

## 作者待填

- `[ACKNOWLEDGMENTS AND FUNDING TO BE COMPLETED]`：致谢与资助。
- `[DATA AND CODE AVAILABILITY TO BE CONFIRMED]`：确认最终数据、代码共享方式及拟引用的版本；已有公开仓库为 https://github.com/emmm1e3m/finite-copy-quantum-metrology 。
- `[DECLARATIONS TO BE CONFIRMED]`：核定适用的期刊声明。PRA 要求披露实质性 AI 使用，具体内容由作者确认；本稿仅保留声明占位位置。[PRA 作者指南](https://journals.aps.org/pra/authors)

两位作者及通讯信息沿用指定版本。本稿供作者校阅，以上行政性内容需在正式投稿前补全。

## 重建

在本文件所在的 `paper/` 目录运行：

```text
pdflatex manuscript.tex
bibtex manuscript
pdflatex manuscript.tex
pdflatex manuscript.tex

xelatex manuscript_zh.tex
bibtex manuscript_zh
xelatex manuscript_zh.tex
xelatex manuscript_zh.tex
```

需要 REVTeX 4.2；中文另需 ctex。论文共用 `references.bib`、`figure_caption.tex` 和 `precision_scaling.pdf`。从仓库根目录运行 `python verify_construction.py --plot-only` 可使用已保存数据重绘图表。

## 本轮验证

英文9页、中文8页，均完成LaTeX—BibTeX—LaTeX两遍编译并逐页查看。75个展示公式与编辑前一致，两版82个源码标签同序，公式与定理编号对应；引用可解析，五条参考文献保留文章题目，无越栏、缺图或未定义引用。三处行政占位符可见。图由已有数值数据重新绘制，数值计算和Lean证明未改动。
