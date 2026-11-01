import FiniteCopy.MainTheorem
import FiniteCopy.SchurNH

open scoped Topology
open Filter
noncomputable section
namespace FiniteCopy.MainTheorem
open FiniteCopy.Risk FiniteCopy.NHOptimization

-- 033的实际凸优化值；原算子NH值与它的等价由042单独提供。
theorem reducedNH_eq_capRisk (N : ℕ) (hN : 0 < N) :
    reducedNH N = 4*N/Schur.schurAverage capFisherBound N := by
  rw [schur_capFisherBound]
  exact reducedNH_formula N hN

theorem reducedNH_strict_gap (N : ℕ) (hN : 10 ≤ N) : reducedNH N < C N := by
  rw [reducedNH_eq_capRisk N (by omega)]
  exact strict_cap_gap N hN

theorem reducedNH_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (reducedNH N - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply cap_risk_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [reducedNH_eq_capRisk N (by omega)]

theorem reducedNH_gap_scaled_zero :
    Tendsto (fun N : ℕ => Real.sqrt N * (C N - reducedNH N)) atTop (𝓝 (0 : ℝ)) := by
  apply cap_gap_smaller_than_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [reducedNH_eq_capRisk N (by omega)]

theorem reducedNH_gap_littleO :
    (fun N => C N - reducedNH N) =o[atTop] (fun N : ℕ => 1/Real.sqrt N) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · convert reducedNH_gap_scaled_zero using 1
    ext N
    simp only [one_div, div_inv_eq_mul, mul_comm]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro hz
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    have hh : (1 : ℝ)/Real.sqrt N ≠ 0 := ne_of_gt (one_div_pos.mpr hs)
    exact False.elim (hh hz)

end FiniteCopy.MainTheorem
