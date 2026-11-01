import FiniteCopy.GlobalBounds

open MeasureTheory

namespace CopyQuantumMetrology.GlobalBounds

-- 原稿中的正则化宽度因子；方差仍由 width 给出。
noncomputable def regularizedWidth (ε x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (x ^ 2 + ε ^ 2))

lemma regularizedWidth_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < regularizedWidth ε x := by
  unfold regularizedWidth
  positivity

lemma regularizedWidth_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    regularizedWidth ε x ≤ 1 / (2 * ε) := by
  have hs : ε ≤ Real.sqrt (x ^ 2 + ε ^ 2) := by
    apply (Real.le_sqrt hε.le (by positivity)).2
    nlinarith [sq_nonneg x]
  unfold regularizedWidth
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

-- 常数14为统一有理常数，含全部越过极点的高斯尾部。
theorem gaussian_energy_regularized {J m ε : ℝ} (hJ : 1 ≤ J)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : |m| ≤ J - 1 / 2) :
    (∫ t, (k J m - q J t) ^ 2 *
      column m (width J m (regularizedWidth ε (m / J))) t ^ 2) ≤
      (14 / ε ^ 2) * J := by
  have he := gaussian_energy_uniform_of_width_bound hJ
    (regularizedWidth_pos hε (m / J)) (regularizedWidth_le hε (m / J)) hm
  have hc : 5 / 2 + 16 * (1 / (2 * ε)) + 12 * (1 / (2 * ε)) ^ 2 ≤ 14 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    field_simp
    nlinarith [sq_nonneg (1 - ε)]
  exact he.trans (mul_le_mul_of_nonneg_right hc (by linarith))

end CopyQuantumMetrology.GlobalBounds

