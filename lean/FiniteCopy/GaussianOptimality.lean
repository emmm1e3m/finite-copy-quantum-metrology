import FiniteCopy.MainTheorem

open scoped Topology
open Filter
noncomputable section
namespace FiniteCopy.MainTheorem

-- 实际Gaussian风险本身属于普通POVM与真实原模型导数定义的集合。
theorem gaussianRisk_mem_true_unbiased (N : ℕ) (hN : 0 < N) :
    gaussianRisk N ∈ tensorAttainableRisks N := by
  rw [tensorAttainableRisks_eq, gaussianRisk_eq N hN]
  exact gaussian_risk_member N hN

theorem C_le_gaussianRisk (N : ℕ) (hN : 0 < N) : C N ≤ gaussianRisk N := by
  rw [gaussianRisk_eq N hN]
  exact (C_finite_sandwich N hN).2

-- 构造相对于真实最优值的超额风险小于首阶修正。
theorem gaussian_excess_scaled_zero :
    Tendsto (fun N : ℕ => Real.sqrt N * (gaussianRisk N - C N))
      atTop (𝓝 (0 : ℝ)) := by
  have h := gaussian_risk_first_correction.sub optimal_risk_first_correction
  have heq : (fun N : ℕ => Real.sqrt N * (gaussianRisk N - C N)) =
      (fun N : ℕ => Real.sqrt N * (gaussianRisk N - 2) - Real.sqrt N * (C N - 2)) := by
    funext N
    ring
  rw [heq]
  simpa only [sub_self] using h

theorem gaussian_excess_littleO :
    (fun N => gaussianRisk N - C N) =o[atTop] (fun N : ℕ => 1 / Real.sqrt N) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · convert gaussian_excess_scaled_zero using 1
    ext N
    simp only [one_div, div_inv_eq_mul, mul_comm]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro hz
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    exact False.elim ((ne_of_gt (one_div_pos.mpr hs)) hz)

end FiniteCopy.MainTheorem
