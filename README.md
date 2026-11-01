# Finite-copy quantum metrology: paper and proofs

- `manuscript.pdf` / `manuscript.tex`: English PRA manuscript, 9 pages.
- `manuscript_zh.pdf` / `manuscript_zh.tex`: complete Chinese manuscript, 8 pages.
- `lean/README.md` and `lean/COVERAGE.md`: proof reconstruction and paper-to-theorem map.
- `lean/verification/`: successful build, 1439-declaration axiom audit, and independent semantic coverage review with reproducible checks.
- `verify_construction.py`, `verification_results.json`, `requirements.txt`: numerical diagnostics and figure generation.

Authors: Tingyu Zhang (23300190021@m.fudan.edu.cn); Yan Cen (corresponding author, cenyan@fudan.edu.cn). Department of Physics, Fudan University, Shanghai, China.

## Reproduction

Install the numerical dependencies with `python -m pip install -r requirements.txt`, then run `python verify_construction.py`. The saved numerical data and both figure images are already included. Floating-point diagnostics are separate from the Lean proofs.

Run `pdflatex manuscript.tex` twice for English, and `xelatex manuscript_zh.tex` twice for Chinese. REVTeX 4.2 is required; the Chinese version also uses ctex. Both manuscripts contain their bibliography and use the same English figure. Acknowledgments are placeholders awaiting completion.

For Lean, install the toolchain specified by `lean/lean-toolchain`, enter `lean/`, obtain the pinned dependency cache with `lake exe cache get`, then run `python verify.py` (or the Windows command in `lean/README.md`). Dependency commits are fixed in `lake-manifest.json`; build caches are not included. The 129 project modules do not import mathematics from another research project.

The theory audit uses only `propext`, `Classical.choice`, and `Quot.sound`; no placeholder proof or additional mathematical axiom is used. Independent review checks the physical definitions and theorem assumptions as well as compilation.

中英文论文的理论命题与关键计算已完成形式化，有限N的最优值取得与显式高斯方案的渐近最优性分别证明。两版公式及编号一致，PDF已逐页检查。尚未向期刊投稿。
