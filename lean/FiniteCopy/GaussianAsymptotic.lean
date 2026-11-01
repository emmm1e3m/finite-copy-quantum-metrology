import FiniteCopy.GaussianLimit
import FiniteCopy.VarianceIdentification
import FiniteCopy.GaussianVariance
import FiniteCopy.RiskTerminal

open scoped BigOperators Topology
open Filter Asymptotics
noncomputable section
namespace FiniteCopy.MainTheorem
open CopyQuantumMetrology

-- 物理量子方差由实际高斯列的积分定义，并已与连续能量 W 精确识别。
theorem actualVariance_ratio_limit :
    Tendsto (fun n : ℕ => actualGaussianVariance n / n) atTop (𝓝 (1/4 : ℝ)) := by
  simpa only [actualGaussianVariance_eq_W] using GaussianLimit.actual_W_limit

theorem actualVariance_littleO :
    (fun n => actualGaussianVariance n - (n : ℝ)/4) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have h := actualVariance_ratio_limit.sub_const (1/4)
    norm_num only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    intro hz
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact False.elim (hn0 hz)

-- 这里的分母是已证明来自真实 Gaussian 测量的 Fisher，而非任意方差参数。
theorem gaussianFisher_risk_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (2*N/globalGaussianFisher N - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  have h := Schur.schurRisk_scaled_limit actualVariance_littleO
  apply h.congr
  intro N
  rw [← globalGaussian_fisher_variance]
  congr 2
  ring

theorem gaussianCovariance_risk_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N *
      ((N : ℝ) * (globalGaussianCovariance (L := N+3) N false false +
        globalGaussianCovariance (L := N+3) N true true) - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply gaussianFisher_risk_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [globalGaussian_risk N (by omega) (by omega)]

end FiniteCopy.MainTheorem
