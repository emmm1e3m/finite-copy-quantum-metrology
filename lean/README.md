# 有限副本量子计量的 Lean 证明

本项目使用 Lean 4.35.0 和 mathlib v4.35.0。具体提交锁定在 `lean-toolchain` 与 `lake-manifest.json`，不依赖其他研究项目的数学定理。

论文理论命题与关键计算的形式化已完成：原始N比特模型、全POVM最优风险、共同方差凸屋顶、有限最优种子取得、显式Gaussian测量和渐近、原NH算子优化及严格差均有完整证明。正式库共129个模块，1439个导出定理与引理通过统一构建和公理审计；独立覆盖审查通过。

逐项对应见 [COVERAGE.md](COVERAGE.md)，独立审查见 [coverage_review.md](verification/coverage_review.md)。

## 重建与审计

在已有锁定依赖的本目录运行：

```powershell
.\compile.ps1 -LakeArguments @('env','python','verify.py')
```

`compile.ps1` 在Windows上为本项目所有代理共用两个编译名额，并设置 `LEAN_NUM_THREADS=2`。单独构建可执行 `lake build`；在其他系统可用 `LEAN_NUM_THREADS=2 python verify.py`。

`verify.py` 重建正式库，生成 `PublicationAudit.lean`，逐项打印所有公开定理的公理依赖。结果在 `verification/build.log`、`verification/axioms.log` 和 `verification/summary.json`。源码检查拒绝 `sorry`、`admit`、新增数学 `axiom` 和 `native_decide`；公理审计仅允许 Lean 常规基础 `propext`、`Classical.choice`、`Quot.sound`。

干净源码副本需要先按 `lean-toolchain` 安装Lean，再运行 `lake exe cache get` 获取锁定依赖的编译缓存，随后执行上述审计。Python审计脚本只依赖标准库。

## 主要入口

| 内容 | 具体定义或定理 |
|---|---|
| 原始张量态及实际参数导数 | `TensorModel.rhoTensor`、`rhoTensor_hasDerivAt_x/y` |
| 一般集合POVM的密度表示 | `Risk.exists_density_of_operator_povm` |
| 真实局部无偏与矩条件的双向等价 | `MainTheorem.tensor_locally_unbiased_iff_moments` |
| 原模型所有局部无偏测量的风险下确界 | `MainTheorem.C`、`C_eq_true_unbiased_inf` |
| 共同方差凸屋顶、全POVM最大Fisher及取得 | `Optimization.exact_sector_reduction`、`commonVarianceRoof_isLeast`、`sectorFisher_isGreatest` |
| 精确有限N风险公式及最小值取得 | `Optimization.C_exact_fisher`、`C_exact_roof`、`C_minimum_attained` |
| 至多2j+1种最优种子 | `ConvexRoof.exists_uniform_support`、`Optimization.rawSeed_isGreatest` |
| 最优风险首项 | `MainTheorem.optimal_risk_first_correction` |
| 每个正N的完整Gaussian测量和估计器 | `MainTheorem.gaussianMeasurement`、`gaussianEstimator`、`finite_N_gaussian_locally_unbiased` |
| 实际Gaussian风险首项与最优性的次阶余量 | `MainTheorem.gaussian_risk_first_correction`、`gaussian_excess_littleO` |
| 固定正C²宽度的真实能量率泛函 | `FixedWidth.fixed_positive_C2_energy_limit` |
| 原始NH算子SDP的真正最优值和达到 | `NHOperator.originalNH_minimum`、`originalNH_formula` |
| N≥10严格NH差及其较小量级 | `MainTheorem.actualNH_strict_gap`、`actualNH_gap_littleO` |

前三类物理对象的完整命名空间见各源码；自旋及Gaussian分析使用 `CopyQuantumMetrology`，风险/算子优化主要使用 `FiniteCopy`。自旋参数采用自然数 `n=2j`，维数为 `n+1`，`J=(n+1)/2`。论文的N是实际副本数，末端定理直接量化N，不以形式上的自由方差序列替代物理模型。

## 开发缓存

本工作区 `.lake/packages` 借用相邻项目的锁定缓存目录联接，只为减少下载；不得在联接目录修改依赖或升级版本。源码发布时排除 `.lake`、`.olean` 等构建产物，保留源码、工具链锁、依赖清单和审计脚本即可。完整审计之后仍需对照论文检查定义和定理的前提；编译本身不能代替语义覆盖核查。
