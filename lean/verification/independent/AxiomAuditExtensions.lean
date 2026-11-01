import FiniteCopy.OriginalNH
import FiniteCopy.FixedC2Limit
import FiniteCopy.FixedIdentification
import FiniteCopy.FiniteSeed
import FiniteCopy.MainTheorem

-- 新增原模型NH、一般固定轮廓和有限seed终端的独立类型/公理检查。
#check FiniteCopy.NHOperator.originalNH_derivative_x
#print axioms FiniteCopy.NHOperator.originalNH_derivative_x
#check FiniteCopy.NHOperator.originalNH_derivative_y
#print axioms FiniteCopy.NHOperator.originalNH_derivative_y
#check FiniteCopy.NHOperator.originalNH_values
#print axioms FiniteCopy.NHOperator.originalNH_values
#check FiniteCopy.NHOperator.originalNH_minimum
#print axioms FiniteCopy.NHOperator.originalNH_minimum
#check FiniteCopy.NHOperator.originalNH_formula
#print axioms FiniteCopy.NHOperator.originalNH_formula
#check FiniteCopy.NHOperator.originalNH_deficit
#print axioms FiniteCopy.NHOperator.originalNH_deficit
#check CopyQuantumMetrology.FixedWidth.fixed_positive_C2_scale_limit
#print axioms CopyQuantumMetrology.FixedWidth.fixed_positive_C2_scale_limit
#check CopyQuantumMetrology.FixedWidth.fixed_positive_C2_energy_limit
#print axioms CopyQuantumMetrology.FixedWidth.fixed_positive_C2_energy_limit
#check CopyQuantumMetrology.FixedWidth.U_regularized_eq
#print axioms CopyQuantumMetrology.FixedWidth.U_regularized_eq
#check CopyQuantumMetrology.FixedWidth.G_global_exists
#print axioms CopyQuantumMetrology.FixedWidth.G_global_exists
#check CopyQuantumMetrology.FixedWidth.G_bulk_exists
#print axioms CopyQuantumMetrology.FixedWidth.G_bulk_exists
#check FiniteCopy.SeedPOVM.Scheme.outcomeEffect_complete
#print axioms FiniteCopy.SeedPOVM.Scheme.outcomeEffect_complete
#check FiniteCopy.SeedPOVM.Scheme.fisher_matrix
#print axioms FiniteCopy.SeedPOVM.Scheme.fisher_matrix
#check FiniteCopy.SeedPOVM.Scheme.fisher_trace
#print axioms FiniteCopy.SeedPOVM.Scheme.fisher_trace
#check FiniteCopy.SeedPOVM.Scheme.momentUnbiased
#print axioms FiniteCopy.SeedPOVM.Scheme.momentUnbiased
#check FiniteCopy.SeedPOVM.Scheme.estimator_risk
#print axioms FiniteCopy.SeedPOVM.Scheme.estimator_risk
#check FiniteCopy.SeedPOVM.Scheme.risk_attainable
#print axioms FiniteCopy.SeedPOVM.Scheme.risk_attainable
#check FiniteCopy.SeedPOVM.Scheme.ensemble_complete
#print axioms FiniteCopy.SeedPOVM.Scheme.ensemble_complete
#check FiniteCopy.SeedPOVM.Scheme.ensemble_variance_trace_identity
#print axioms FiniteCopy.SeedPOVM.Scheme.ensemble_variance_trace_identity

-- 验证旧的严格cap差可直接接到当前真正全算子NH值。
theorem checked_originalNH_strict_gap (N : ℕ) (hN : 10 ≤ N) :
    FiniteCopy.NHOperator.actualNHRisk N < FiniteCopy.MainTheorem.C N := by
  rw [FiniteCopy.NHOperator.originalNH_formula N (by omega)]
  exact FiniteCopy.MainTheorem.strict_cap_gap N hN

#check checked_originalNH_strict_gap
#print axioms checked_originalNH_strict_gap
