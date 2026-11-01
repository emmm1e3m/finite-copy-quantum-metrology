import FiniteCopy.UniformSupport
import FiniteCopy.SeedBlocks
import FiniteCopy.FullNH
import FiniteCopy.PaperBounds

-- 有限支撑、全局种子统计、真实NH与论文误差式的独立审计。
#check FiniteCopy.ConvexRoof.finite_mixture_reduce
#print axioms FiniteCopy.ConvexRoof.finite_mixture_reduce
#check FiniteCopy.ConvexRoof.primal_attained
#print axioms FiniteCopy.ConvexRoof.primal_attained
#check FiniteCopy.ConvexRoof.exists_uniform_support
#print axioms FiniteCopy.ConvexRoof.exists_uniform_support
#check FiniteCopy.SeedBlocks.effect_sum
#print axioms FiniteCopy.SeedBlocks.effect_sum
#check FiniteCopy.SeedBlocks.fisher_matrix
#print axioms FiniteCopy.SeedBlocks.fisher_matrix
#check FiniteCopy.SeedBlocks.fisher_trace
#print axioms FiniteCopy.SeedBlocks.fisher_trace
#check FiniteCopy.SeedBlocks.momentUnbiased
#print axioms FiniteCopy.SeedBlocks.momentUnbiased
#check FiniteCopy.SeedBlocks.estimator_risk
#print axioms FiniteCopy.SeedBlocks.estimator_risk
#check FiniteCopy.SeedBlocks.risk_attainable
#print axioms FiniteCopy.SeedBlocks.risk_attainable
#check FiniteCopy.MainTheorem.actualNH_below_C
#print axioms FiniteCopy.MainTheorem.actualNH_below_C
#check FiniteCopy.MainTheorem.actualNH_strict_gap
#print axioms FiniteCopy.MainTheorem.actualNH_strict_gap
#check FiniteCopy.MainTheorem.actualNH_first_correction
#print axioms FiniteCopy.MainTheorem.actualNH_first_correction
#check FiniteCopy.MainTheorem.actualNH_gap_littleO
#print axioms FiniteCopy.MainTheorem.actualNH_gap_littleO
#check CopyQuantumMetrology.GaussianLimit.actual_paper_uniform_error
#print axioms CopyQuantumMetrology.GaussianLimit.actual_paper_uniform_error
