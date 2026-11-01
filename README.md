# Finite-copy quantum metrology: paper and proofs

- [English PDF](paper/manuscript.pdf) / [LaTeX](paper/manuscript.tex): English PRA manuscript for author review.
- [Chinese PDF](paper/manuscript_zh.pdf) / [LaTeX](paper/manuscript_zh.tex): Chinese author-review manuscript.
- `lean/README.md` and `lean/COVERAGE.md`: proof reconstruction and paper-to-theorem map.
- `lean/verification/`: successful build, 1439-declaration axiom audit, and independent semantic coverage review with reproducible checks.
- [Author review notes](paper/AUTHOR_REVIEW.md): editorial changes and placeholders to complete.
- `verify_construction.py`, `verification_results.json`, `requirements.txt`: numerical diagnostics and figure generation.

Authors: Tingyu Zhang (23300190021@m.fudan.edu.cn); Yan Cen (corresponding author, cenyan@fudan.edu.cn). Department of Physics, Fudan University, Shanghai, China.

## Reproduction

Install the numerical dependencies with `python -m pip install -r requirements.txt`, then run `python verify_construction.py`. Use `python verify_construction.py --plot-only` to redraw the figure from the saved data. The saved numerical data and the shared English figure in `paper/` are already included. Floating-point diagnostics are separate from the Lean proofs.

Enter `paper/`. For English, run `pdflatex manuscript.tex`, `bibtex manuscript`, then `pdflatex manuscript.tex` twice. For Chinese, run `xelatex manuscript_zh.tex`, `bibtex manuscript_zh`, then `xelatex manuscript_zh.tex` twice. REVTeX 4.2 is required; the Chinese version also uses ctex. Both manuscripts use `references.bib`, the `apsrev4-2` style, and the same vector figure and English caption. Administrative statements contain author-review placeholders.

For Lean, install the toolchain specified by `lean/lean-toolchain`, enter `lean/`, obtain the pinned dependency cache with `lake exe cache get`, then run `python verify.py` (or the Windows command in `lean/README.md`). Dependency commits are fixed in `lake-manifest.json`; build caches are not included. The 129 project modules do not import mathematics from another research project.

The theory audit uses only `propext`, `Classical.choice`, and `Quot.sound`; no placeholder proof or additional mathematical axiom is used. Independent review checks the physical definitions and theorem assumptions as well as compilation.

中英文论文的理论命题与关键计算已完成形式化，有限N的最优值取得与显式高斯方案的渐近最优性分别证明。两版公式及编号一致，PDF已逐页检查。尚未向期刊投稿。
