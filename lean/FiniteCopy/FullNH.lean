import FiniteCopy.MainTheorem
import FiniteCopy.OriginalNH

open scoped Topology
open Filter
noncomputable section
namespace FiniteCopy.MainTheorem
open FiniteCopy.NHOperator

-- NH从原矩阵SDP定义；闭式由实际CG酉变换和全矩阵最优化定理推出。
theorem actualNH_below_C (N : ℕ) (hN : 0 < N) : actualNHRisk N ≤ C N := by
  rw [originalNH_formula N hN]
  exact (C_finite_sandwich N hN).1

theorem actualNH_strict_gap (N : ℕ) (hN : 10 ≤ N) : actualNHRisk N < C N := by
  rw [originalNH_formula N (by omega)]
  exact strict_cap_gap N hN

theorem actualNH_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (actualNHRisk N - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply Risk.cap_risk_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [originalNH_formula N (by omega)]

theorem actualNH_gap_scaled_zero :
    Tendsto (fun N : ℕ => Real.sqrt N * (C N - actualNHRisk N))
      atTop (𝓝 (0 : ℝ)) := by
  apply cap_gap_smaller_than_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [originalNH_formula N (by omega)]

theorem actualNH_gap_littleO :
    (fun N => C N - actualNHRisk N) =o[atTop] (fun N : ℕ => 1 / Real.sqrt N) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · convert actualNH_gap_scaled_zero using 1
    ext N
    simp only [one_div, div_inv_eq_mul, mul_comm]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro hz
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    exact False.elim ((ne_of_gt (one_div_pos.mpr hs)) hz)

end FiniteCopy.MainTheorem
