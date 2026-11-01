import FiniteCopy.ExactTensorOptimization
import FiniteCopy.OrdinaryFisher
import FiniteCopy.MainTheorem

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk
open SpinPaths TensorModel

theorem roof_sandwich_W (n : ℕ) :
    NHLowerBound.spinL n ≤ commonVarianceRoof n ∧
    commonVarianceRoof n ≤ ContinuousEnergy.W n (epsilon (spinJ n)) := by
  refine ⟨roof_lower n, ?_⟩
  simpa only [actualGaussianVariance_eq_W] using roof_upper n

-- 自旋参数为 j=n/2；直接按 j 的尺度写出论文共同 roof 渐近。
theorem commonVarianceRoof_spin_ratio_limit :
    Filter.Tendsto (fun n : ℕ => commonVarianceRoof n / ((n : ℝ)/2))
      Filter.atTop (𝓝 (1/2 : ℝ)) := by
  have h := commonVarianceRoof_ratio_limit.mul_const 2
  convert h using 1
  · funext n
    ring
  · norm_num

theorem commonVarianceRoof_spin_littleO :
    (fun n => commonVarianceRoof n - ((n : ℝ)/2)/2) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ)/2) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have h := commonVarianceRoof_spin_ratio_limit.sub_const (1/2)
    norm_num only [sub_self] at h
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    intro hz
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact False.elim ((div_ne_zero hn0 (by norm_num : (2 : ℝ) ≠ 0)) hz)

theorem ordinary_sectorFisher_maximum (n : ℕ) :
    IsGreatest (ordinaryFisherValues (state n) (sectorTangent n)) (sectorFisher n) := by
  rw [ordinary_sectorFisherValues_eq]
  exact sectorFisher_isGreatest n

theorem ordinary_tensorFisher_maximum (N : ℕ) :
    IsGreatest (ordinaryFisherValues (rhoTensor N 0 0) (tangentAxes N))
      (Schur.schurAverage sectorFisher N) := by
  rw [ordinaryFisherValues_eq, ← tensorFisherDenominator_schur]
  exact tensorFisher_isGreatest N

-- 论文 C_N：原 N-qubit 模型、任意普通 POVM 与真实局部无偏估计器。
theorem C_exact_fisher (N : ℕ) (hN : 0 < N) :
    MainTheorem.C N = 4*N / Schur.schurAverage sectorFisher N :=
  tensorOptimalRisk_eq N hN

theorem C_exact_roof (N : ℕ) (hN : 0 < N) :
    MainTheorem.C N = 4*N / (2*N - 4*Schur.schurAverage commonVarianceRoof N) :=
  tensorOptimalRisk_roof N hN

theorem C_minimum_attained (N : ℕ) (hN : 0 < N) :
    MainTheorem.C N ∈ MainTheorem.ordinaryAttainableRisks N
      (rhoTensor N 0 0) (tangentAxes N) := by
  rw [MainTheorem.ordinaryAttainableRisks_eq]
  exact tensorOptimalRisk_attained N hN

end FiniteCopy.Optimization
