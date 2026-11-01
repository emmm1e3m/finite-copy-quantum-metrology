# 本稿理论命题逐项验收

最终结论：**本稿理论命题与关键计算的形式化覆盖验收通过。** 直接核对本包`manuscript.tex`、对应中文源及正式`lean/FiniteCopy`实际定义和证明；019最后19项终端审计exit=0。历史未完成判断已被本表替代。

| 稿件声明 | 实际形式化证据 | 验收 |
|---|---|---|
| Model：原N-qubit态、参考态与两参数导数 | `TensorModel.rhoTensor/rhoTensor_zero/rhoTensor_hasDerivAt_x/y`，`BornExpectation` | 通过，真实张量模型 |
| Schur分解及块概率、局部切向 | 实际CG路径双边酉与intertwining，`Resolution.blockResolution`，`PathSchur` | 通过，路径细分重数是等价实现 |
| 任意复杂/连续结果POVM | `POVMDensity.exists_density_of_operator_povm`，`OrdinaryRisk`逐事件恢复，`OrdinaryFisher`集合相等 | 通过，无已有密度或有限结果假设 |
| 真局部无偏与C定义 | `TensorLocallyUnbiased`使用真实rhoTensor期望偏导；与矩条件双向等价；`C_eq_true_unbiased_inf` | 通过，有限二阶风险不改变有有限达到者的最优值 |
| Lemma reduction：全POVM最大T_j | 独立`fisherValues/sectorFisher`，`sectorFisher_isGreatest`与`ordinary_sectorFisher_maximum` | 通过，最大值真实取得 |
| 同引理：T_j=8j(j+1)/3−4V_j | 独立`PureEnsemble/varianceValues/commonVarianceRoof`，`exact_sector_reduction` | 通过，同一复纯态分解的共同方差 |
| 同引理：T_N=ΣP T_j | 独立原模型`modelFisherValues`，实际块压缩与最优方案抬升，`ordinary_tensorFisher_maximum` | 通过，全joint POVM最优值 |
| 同引理：C_N=4N/T_N及有限N达到 | `C_exact_fisher/C_exact_roof/C_minimum_attained`，019`checked_C_trueLU_minimum` | 通过，所有N>0，普通POVM且真实LU最小值取得 |
| 主定理：V_j=j/2+o(j) | `roof_sandwich_W`、`commonVarianceRoof_spin_littleO` | 通过，n=2j覆盖整数及半整数 |
| 主定理：C_N首项 | `MainTheorem.optimal_risk_first_correction` | 通过，真实风险inf，未假设目标渐近 |
| 实际Gaussian测量每N合法/完整/真LU | `Construction`、`GaussianLift`、`finite_N_gaussian_locally_unbiased` | 通过，L=N+3合法，零自旋随机恒等细化等价 |
| 实际Gaussian估计器风险及首项 | `gaussianRisk`实际Born风险，`gaussianRisk_eq/gaussian_risk_first_correction` | 通过，单轴F与trace T尺度一致 |
| Appendix A非负seed精确优化eq:seed-opt | `RawSeeds.rawSeedValues/rawSeedFisher`及`rawSeed_isGreatest` | 通过，原始逐列γ²/mass目标与全T一致 |
| 最大值取得、至多d seed、共同仿射上界 | `UniformSupport.exists_uniform_support`实际连续目标实例，`exists_optimalScheme` | 通过，零填充Fin d表示≤d，未预设取得 |
| Proposition lower：cap根、L界与渐近、V≥L | `LowerBound/SpinInterface`及`roof_lower` | 通过，L≥0、L≤j/2+1/4及L/j→1/2 |
| 高斯I/G/R能量及W≤U | 通用`Algebra`，实际`ContinuousEnergy`可积/夹心，`VarianceIdentification` | 通过，实际连续积分链 |
| Theorem energy：任意固定正C² b率泛函 | `FixedC2Limit.fixed_positive_C2_energy_limit`，`FixedDefinitions/FixedGradient`，`FixedIdentification` | 通过，仅论文区间正C²假设，实际U/j |
| Theorem energy：显式eps序列U/j→1/2、W=j/2+o(j) | `GaussianLimit.actual_U_limit/actual_W_limit` | 通过，无外置误差假设 |
| Appendix C统一误差式与log^50余项 | `PaperBounds.actual_paper_uniform_error`，C=40000；全轴根式余量和实际有限差分梯度 | 通过，修改涉及中英九展示式一致 |
| Schur averaging lemma：二阶矩、一阶首项、固定余项加权little-o | `Schur`精确二项式权重、Wallis极限、`schurAverage_littleO` | 通过，索引尺度正确 |
| 随机游走eq:walk的精确一阶矩 | `Schur`等价偶/奇二项式有限和公式 | 公式内容通过；没有单独构造概率随机变量S_N |
| NH全算子SDP值与cap闭式 | `OriginalNH.actualNHRisk/originalNH_minimum/formula/deficit` | 通过，原Bits N全矩阵可行集、真实取得 |
| Corollary gap：N≥10严格NH差及o(N^-1/2) | `FullNH.actualNH_strict_gap/actualNH_gap_littleO` | 通过，统一正margin已传真实C |
| N≤9等号、coherent首阶理论系数 | 当前稿件没有这些理论命题 | 不添加额外验收项目 |
| 数值图表/有限精度计算 | 属于数值证据与绘图复核 | 不称为Lean理论形式化 |

## 等价证明路线

全部命名理论命题已有完整终端或已证等价公式。实现采用若干等价路线：任意PSD对角平方根与共同对偶证书控制全POVM，绕过可测rank-one谱细化；d点参数空间紧性与改进消点构造最优者，替代稿件的弱紧性/接触集Carathéodory叙述；Wallis极限替代Stirling；全复矩阵NH下界加raising达到替代预先协变归约；统一严格margin使严格gap不依赖先调用取得性。这些路线不减弱论文命题，不要求每个叙述步骤都以同名Lean定理出现。

## 独立证据

019五批终端类型/公理审计共74次调用全部exit=0，只有`propext`、`Classical.choice`、`Quot.sound`。最后`AxiomAuditExact.lean`额外给`checked_C_trueLU_minimum`，结论为真实普通POVM及原rhoTensor期望偏导LU风险集合上的`IsLeast C`。五批检查源码和日志位于同目录的`independent/`。在lean目录运行`lake env lean verification/independent/AxiomAuditExact.lean`可复核最后一批；其他四批同理。

本表是理论覆盖验收，不是对PDF视觉版面或浮点图表的重复验收。中英修改公式已源级核对；最终PDF重编/目检由根代理另行记录。