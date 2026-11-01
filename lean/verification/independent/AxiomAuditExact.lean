import FiniteCopy.ExactFiniteN

-- 最后精确优化终端：独立对象、一般POVM、共同roof与原模型取得。
#check FiniteCopy.Optimization.PureEnsemble.probability_integral
#print axioms FiniteCopy.Optimization.PureEnsemble.probability_integral
#check FiniteCopy.Optimization.PureEnsemble.variance_integrable
#print axioms FiniteCopy.Optimization.PureEnsemble.variance_integrable
#check FiniteCopy.Optimization.PureEnsemble.fisher_variance
#print axioms FiniteCopy.Optimization.PureEnsemble.fisher_variance
#check FiniteCopy.Optimization.psd_fisher_le_dual
#print axioms FiniteCopy.Optimization.psd_fisher_le_dual
#check FiniteCopy.Optimization.density_fisher_le_dual
#print axioms FiniteCopy.Optimization.density_fisher_le_dual
#check FiniteCopy.Optimization.exists_optimalScheme
#print axioms FiniteCopy.Optimization.exists_optimalScheme
#check FiniteCopy.Optimization.sectorFisher_isGreatest
#print axioms FiniteCopy.Optimization.sectorFisher_isGreatest
#check FiniteCopy.Optimization.commonVarianceRoof_isLeast
#print axioms FiniteCopy.Optimization.commonVarianceRoof_isLeast
#check FiniteCopy.Optimization.exact_sector_reduction
#print axioms FiniteCopy.Optimization.exact_sector_reduction
#check FiniteCopy.Optimization.rawSeed_isGreatest
#print axioms FiniteCopy.Optimization.rawSeed_isGreatest
#check FiniteCopy.Optimization.roof_sandwich_W
#print axioms FiniteCopy.Optimization.roof_sandwich_W
#check FiniteCopy.Optimization.commonVarianceRoof_spin_littleO
#print axioms FiniteCopy.Optimization.commonVarianceRoof_spin_littleO
#check FiniteCopy.Optimization.tensorFisher_isGreatest
#print axioms FiniteCopy.Optimization.tensorFisher_isGreatest
#check FiniteCopy.Optimization.ordinary_sectorFisher_maximum
#print axioms FiniteCopy.Optimization.ordinary_sectorFisher_maximum
#check FiniteCopy.Optimization.ordinary_tensorFisher_maximum
#print axioms FiniteCopy.Optimization.ordinary_tensorFisher_maximum
#check FiniteCopy.Optimization.C_exact_fisher
#print axioms FiniteCopy.Optimization.C_exact_fisher
#check FiniteCopy.Optimization.C_exact_roof
#print axioms FiniteCopy.Optimization.C_exact_roof
#check FiniteCopy.Optimization.C_minimum_attained
#print axioms FiniteCopy.Optimization.C_minimum_attained

-- 原普通POVM和真实rhoTensor期望导数定义下的最小风险确实取得。
theorem checked_C_trueLU_minimum (N : ℕ) (hN : 0 < N) :
    IsLeast (FiniteCopy.MainTheorem.tensorAttainableRisks N) (FiniteCopy.MainTheorem.C N) := by
  constructor
  · rw [FiniteCopy.MainTheorem.tensorAttainableRisks_eq]
    exact FiniteCopy.Optimization.tensorOptimalRisk_attained N hN
  · intro r hr
    rw [FiniteCopy.MainTheorem.tensorAttainableRisks_eq] at hr
    rw [FiniteCopy.Optimization.C_exact_fisher N hN,
      ← FiniteCopy.Optimization.tensorFisherDenominator_schur]
    exact FiniteCopy.Optimization.tensor_attainableRisks_lower N r hr

#check checked_C_trueLU_minimum
#print axioms checked_C_trueLU_minimum
