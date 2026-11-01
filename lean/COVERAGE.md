# 论文与形式化对应

下表对应 `manuscript.tex` 和 `manuscript_zh.tex` 的同名标签。代码以自然数 `n=2j` 表示自旋；`N`始终为实际副本数。完整命名空间主要为 `CopyQuantumMetrology`（自旋与Gaussian分析）及 `FiniteCopy`（风险与优化）。

| 论文结果 | 正式源码与入口 |
|---|---|
| 原始N比特态、实际参数偏导、圆盘内PSD | [TensorModel.lean](FiniteCopy/TensorModel.lean)、[TensorDensity.lean](FiniteCopy/TensorDensity.lean)、[ExpectationIntegrability.lean](FiniteCopy/ExpectationIntegrability.lean) |
| 任意普通POVM与真实期望局部无偏条件 | [POVMDensity.lean](FiniteCopy/POVMDensity.lean) `exists_density_of_operator_povm`；[MainTheorem.lean](FiniteCopy/MainTheorem.lean) `tensor_locally_unbiased_iff_moments`、`C_eq_true_unbiased_inf` |
| Schur分块及真实二项式多重度 | [Resolution.lean](FiniteCopy/Resolution.lean) `blockResolution`；[ActualPaths.lean](FiniteCopy/ActualPaths.lean) `actual_path_multiplicity_card`；[PathSchur.lean](FiniteCopy/PathSchur.lean) `path_schur_average` |
| 精确最优Fisher、共同方差凸屋顶及取得（引理1、附录A） | [OptimizationObjects.lean](FiniteCopy/OptimizationObjects.lean)独立定义两个优化对象；[ExactOptimization.lean](FiniteCopy/ExactOptimization.lean) `exact_sector_reduction`、`sectorFisher_isGreatest`、`commonVarianceRoof_isLeast` |
| 原始非负种子商式与至多2j+1种种子取得 | [UniformSupport.lean](FiniteCopy/UniformSupport.lean) `exists_uniform_support`；[ExactTensorOptimization.lean](FiniteCopy/ExactTensorOptimization.lean) `rawSeed_isGreatest` |
| 每个正N的精确最优风险及最小值取得 | [ExactFiniteN.lean](FiniteCopy/ExactFiniteN.lean) `C_exact_fisher`、`C_exact_roof`、`C_minimum_attained`；[SeedBlocks.lean](FiniteCopy/SeedBlocks.lean)构造有限结果的实际达到者 |
| V_j=j/2+o(j)（定理2第一式） | [ExactFiniteN.lean](FiniteCopy/ExactFiniteN.lean) `roof_sandwich_W`、`commonVarianceRoof_spin_littleO` |
| C_N=2+sqrt(8/pi)/sqrt(N)+o(N^(-1/2))（定理2） | [MainTheorem.lean](FiniteCopy/MainTheorem.lean) `optimal_risk_first_correction` |
| 显式完整Gaussian测量、每个N精确局部无偏与达到首项 | [MainTheorem.lean](FiniteCopy/MainTheorem.lean) `gaussianMeasurement`、`gaussianEstimator`、`finite_N_gaussian_locally_unbiased`、`gaussian_risk_first_correction`；[GaussianOptimality.lean](FiniteCopy/GaussianOptimality.lean) `gaussian_excess_littleO` |
| SOS、真实cap根与下界渐近（附录B） | [Algebra.lean](FiniteCopy/Algebra.lean)、[LowerBound.lean](FiniteCopy/LowerBound.lean)、[SpinInterface.lean](FiniteCopy/SpinInterface.lean) |
| 任意固定正C²宽度的真实能量率泛函（附录C） | [FixedC2Limit.lean](FiniteCopy/FixedC2Limit.lean) `fixed_positive_C2_energy_limit`；[FixedIdentification.lean](FiniteCopy/FixedIdentification.lean) `U_regularized_eq` |
| 显式对数宽度、完整端区/内部误差和W极限 | [GaussianLimit.lean](FiniteCopy/GaussianLimit.lean) `actual_U_limit`、`actual_W_limit`；[PaperBounds.lean](FiniteCopy/PaperBounds.lean) `actual_paper_uniform_error`，论文统一常数可取40000 |
| Schur精确矩、均值首项与little-o平均（附录D） | [Schur.lean](FiniteCopy/Schur.lean)，真实二项式权重及奇偶精确公式，经Wallis极限完成首项 |
| 全NH算子SDP精确值及达到（附录E） | [NHBlockSDP.lean](FiniteCopy/NHBlockSDP.lean) `originalNH_block_minimum`；[BlockNH.lean](FiniteCopy/BlockNH.lean) `block_NH_minimum`；[OriginalNH.lean](FiniteCopy/OriginalNH.lean) `originalNH_minimum`、`originalNH_formula` |
| N≥10严格NH差与o(N^(-1/2))（推论3） | [FullNH.lean](FiniteCopy/FullNH.lean) `actualNH_strict_gap`、`actualNH_gap_littleO` |

风险对象直接遍历原模型的测量与估计器。最优值公式、Schur等价、Gaussian误差界和NH算子等价均有内部证明；最终主定理不把这些研究结论作为额外假设。

最优有限种子通过紧性和支持超平面证明存在，不提供一般有限N的闭式最优种子。论文明确给出的Gaussian方案独立定义，并对每个正N证明完整性、真实局部无偏性及同一渐近首项。

形式证明使用与稿件等价的证明路线：NH采用全矩阵对偶证书和raising达到；位置项采用全实轴根式余量；Schur首项使用Wallis极限。对应定理对象与结论保持一致。浮点图表由数值程序核对，未用作无限序列证明。

最终编译、公理依赖和公开声明数以 [verification/summary.json](verification/summary.json) 为准。审计允许的基础公理只有 `propext`、`Classical.choice`、`Quot.sound`；无需项目新增数学公理或占位证明。
