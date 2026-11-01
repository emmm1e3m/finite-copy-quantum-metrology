import FiniteCopy.Gaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory

namespace CopyQuantumMetrology.GlobalBounds

noncomputable def q (J t : ℝ) : ℝ := Real.sqrt (max (J ^ 2 - t ^ 2) 0)

lemma q_nonneg (J t : ℝ) : 0 ≤ q J t := Real.sqrt_nonneg _

lemma q_sq (J t : ℝ) : q J t ^ 2 = max (J ^ 2 - t ^ 2) 0 :=
  Real.sq_sqrt (le_max_right _ _)

lemma q_sq_le (J t : ℝ) : q J t ^ 2 ≤ J ^ 2 := by
  rw [q_sq]
  exact max_le (by nlinarith [sq_nonneg t]) (sq_nonneg J)

lemma continuous_q (J : ℝ) : Continuous (q J) := by
  unfold q
  fun_prop

-- 正部截断在全实轴上收缩距离，包括越过两个极点的尾部。
lemma abs_positive_part_sub {a x : ℝ} (ha : 0 ≤ a) :
    |max x 0 - a| ≤ |x - a| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', zero_sub, abs_neg, abs_of_nonneg ha,
      abs_of_nonpos (by linarith : x - a ≤ 0)]
    linarith

lemma abs_q_sub_sqrt {J m : ℝ} (hB : 0 < J ^ 2 - m ^ 2) (t : ℝ) :
    |q J t - Real.sqrt (J ^ 2 - m ^ 2)| ≤
      |t ^ 2 - m ^ 2| / Real.sqrt (J ^ 2 - m ^ 2) := by
  let B := Real.sqrt (J ^ 2 - m ^ 2)
  have hBp : 0 < B := Real.sqrt_pos.mpr hB
  have hBs : B ^ 2 = J ^ 2 - m ^ 2 := Real.sq_sqrt hB.le
  have habs : |q J t ^ 2 - B ^ 2| ≤ |t ^ 2 - m ^ 2| := by
    rw [q_sq, hBs]
    calc
      _ ≤ |J ^ 2 - t ^ 2 - (J ^ 2 - m ^ 2)| := abs_positive_part_sub hB.le
      _ = _ := by
        rw [show J ^ 2 - t ^ 2 - (J ^ 2 - m ^ 2) = m ^ 2 - t ^ 2 by ring]
        exact abs_sub_comm _ _
  have hfactor : |q J t - B| * (q J t + B) = |q J t ^ 2 - B ^ 2| := by
    rw [← abs_of_nonneg (by linarith [q_nonneg J t] : 0 ≤ q J t + B), ← abs_mul]
    congr 1
    ring
  apply (le_div_iff₀ hBp).mpr
  calc
    |q J t - B| * B ≤ |q J t - B| * (q J t + B) := by
      gcongr
      exact le_add_of_nonneg_left (q_nonneg J t)
    _ = |q J t ^ 2 - B ^ 2| := hfactor
    _ ≤ |t ^ 2 - m ^ 2| := habs

lemma q_sub_sqrt_sq_le {J m : ℝ} (hB : 0 < J ^ 2 - m ^ 2) (t : ℝ) :
    (q J t - Real.sqrt (J ^ 2 - m ^ 2)) ^ 2 ≤
      (t ^ 2 - m ^ 2) ^ 2 / (J ^ 2 - m ^ 2) := by
  have h := abs_q_sub_sqrt hB t
  have hnn : 0 ≤ |t ^ 2 - m ^ 2| / Real.sqrt (J ^ 2 - m ^ 2) := by positivity
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  simpa [← pow_two, div_pow, sq_abs, Real.sq_sqrt hB.le] using hh

-- 同一根式的 Hölder 界控制相邻离散系数，不需要远离极点。
lemma q_sub_sqrt_sq_le_abs {J m : ℝ} (hB : 0 ≤ J ^ 2 - m ^ 2) (t : ℝ) :
    (q J t - Real.sqrt (J ^ 2 - m ^ 2)) ^ 2 ≤ |t ^ 2 - m ^ 2| := by
  let B := Real.sqrt (J ^ 2 - m ^ 2)
  have hBn : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B ^ 2 = J ^ 2 - m ^ 2 := Real.sq_sqrt hB
  have habs : |q J t ^ 2 - B ^ 2| ≤ |t ^ 2 - m ^ 2| := by
    rw [q_sq, hBs]
    calc
      _ ≤ |J ^ 2 - t ^ 2 - (J ^ 2 - m ^ 2)| := abs_positive_part_sub hB
      _ = _ := by
        rw [show J ^ 2 - t ^ 2 - (J ^ 2 - m ^ 2) = m ^ 2 - t ^ 2 by ring]
        exact abs_sub_comm _ _
  have haux : (q J t - B) ^ 2 ≤ |q J t ^ 2 - B ^ 2| := by
    by_cases h : B ≤ q J t
    · rw [abs_of_nonneg (by nlinarith [q_nonneg J t] : 0 ≤ q J t ^ 2 - B ^ 2)]
      nlinarith [mul_nonneg hBn (sub_nonneg.mpr h)]
    · have h' : q J t ≤ B := le_of_not_ge h
      rw [abs_of_nonpos (by nlinarith [q_nonneg J t] : q J t ^ 2 - B ^ 2 ≤ 0)]
      nlinarith [mul_nonneg (q_nonneg J t) (sub_nonneg.mpr h')]
  exact haux.trans habs

lemma squared_difference_bound (m t : ℝ) :
    (t ^ 2 - m ^ 2) ^ 2 ≤ 8 * m ^ 2 * (t - m) ^ 2 + 2 * (t - m) ^ 4 := by
  nlinarith [sq_nonneg (2 * m * (t - m) - (t - m) ^ 2)]

lemma integrable_energy {ρ : ℝ → ℝ} (hρ : Integrable ρ) (hρn : ∀ t, 0 ≤ ρ t)
    (J k : ℝ) : Integrable (fun t => (k - q J t) ^ 2 * ρ t) := by
  refine (hρ.const_mul (2 * k ^ 2 + 2 * J ^ 2)).mono' ?_ ?_
  · exact (((continuous_const.sub (continuous_q J)).pow 2).aestronglyMeasurable.mul
      hρ.aestronglyMeasurable)
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρn t))]
    apply mul_le_mul_of_nonneg_right _ (hρn t)
    nlinarith [sq_nonneg (k + q J t), q_sq_le J t]

lemma integral_root_gap_le {ρ : ℝ → ℝ} {J m S : ℝ}
    (hρ : Integrable ρ) (hρn : ∀ t, 0 ≤ ρ t) (hB : 0 < J ^ 2 - m ^ 2)
    (h2 : Integrable (fun t => (t - m) ^ 2 * ρ t))
    (h4 : Integrable (fun t => (t - m) ^ 4 * ρ t))
    (hm2 : (∫ t, (t - m) ^ 2 * ρ t) = S)
    (hm4 : (∫ t, (t - m) ^ 4 * ρ t) = 3 * S ^ 2) :
    (∫ t, (q J t - Real.sqrt (J ^ 2 - m ^ 2)) ^ 2 * ρ t) ≤
      (8 * m ^ 2 * S + 6 * S ^ 2) / (J ^ 2 - m ^ 2) := by
  have hgap : Integrable (fun t => (q J t - Real.sqrt (J ^ 2 - m ^ 2)) ^ 2 * ρ t) := by
    convert integrable_energy hρ hρn J (Real.sqrt (J ^ 2 - m ^ 2)) using 1
    ext t
    ring
  have hb := (h2.const_mul (8 * m ^ 2 / (J ^ 2 - m ^ 2))).add
    (h4.const_mul (2 / (J ^ 2 - m ^ 2)))
  calc
    _ ≤ ∫ t, (8 * m ^ 2 / (J ^ 2 - m ^ 2)) * ((t - m) ^ 2 * ρ t) +
        (2 / (J ^ 2 - m ^ 2)) * ((t - m) ^ 4 * ρ t) := by
      apply integral_mono hgap hb
      intro t
      have h := (q_sub_sqrt_sq_le hB t).trans
        ((div_le_div_iff_of_pos_right hB).mpr (squared_difference_bound m t))
      have hh := mul_le_mul_of_nonneg_right h (hρn t)
      convert hh using 1 <;> simp only [Pi.add_apply] <;> ring
    _ = _ := by
      rw [integral_add (h2.const_mul _) (h4.const_mul _), integral_const_mul,
        integral_const_mul, hm2, hm4]
      ring

noncomputable def k (J m : ℝ) : ℝ := (q J (m - 1 / 2) + q J (m + 1 / 2)) / 2

lemma k_gap_sq_le {J m : ℝ} (hB : 0 ≤ J ^ 2 - m ^ 2) (hm : |m| ≤ J) :
    (k J m - Real.sqrt (J ^ 2 - m ^ 2)) ^ 2 ≤ J + 1 / 4 := by
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  have hp := q_sub_sqrt_sq_le_abs hB (m + 1 / 2)
  have hn := q_sub_sqrt_sq_le_abs hB (m - 1 / 2)
  have hap : |(m + 1 / 2) ^ 2 - m ^ 2| ≤ J + 1 / 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have han : |(m - 1 / 2) ^ 2 - m ^ 2| ≤ J + 1 / 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  unfold k
  nlinarith [sq_nonneg (q J (m - 1 / 2) - q J (m + 1 / 2))]

lemma integral_energy_le {ρ : ℝ → ℝ} {J m S : ℝ}
    (hρ : Integrable ρ) (hρn : ∀ t, 0 ≤ ρ t) (hnorm : (∫ t, ρ t) = 1)
    (hB : 0 < J ^ 2 - m ^ 2) (hm : |m| ≤ J)
    (h2 : Integrable (fun t => (t - m) ^ 2 * ρ t))
    (h4 : Integrable (fun t => (t - m) ^ 4 * ρ t))
    (hm2 : (∫ t, (t - m) ^ 2 * ρ t) = S)
    (hm4 : (∫ t, (t - m) ^ 4 * ρ t) = 3 * S ^ 2) :
    (∫ t, (k J m - q J t) ^ 2 * ρ t) ≤
      2 * (J + 1 / 4) + 2 * ((8 * m ^ 2 * S + 6 * S ^ 2) / (J ^ 2 - m ^ 2)) := by
  let B := Real.sqrt (J ^ 2 - m ^ 2)
  have hgap : Integrable (fun t => (q J t - B) ^ 2 * ρ t) := by
    convert integrable_energy hρ hρn J B using 1
    ext t
    ring
  calc
    _ ≤ ∫ t, 2 * (k J m - B) ^ 2 * ρ t + 2 * ((q J t - B) ^ 2 * ρ t) := by
      apply integral_mono (integrable_energy hρ hρn J (k J m))
        ((hρ.const_mul _).add (hgap.const_mul 2))
      intro t
      have h : (k J m - q J t) ^ 2 ≤ 2 * (k J m - B) ^ 2 + 2 * (q J t - B) ^ 2 := by
        nlinarith [sq_nonneg (k J m + q J t - 2 * B)]
      convert mul_le_mul_of_nonneg_right h (hρn t) using 1 <;> simp only [Pi.add_apply] <;> ring
    _ = 2 * (k J m - B) ^ 2 + 2 * (∫ t, (q J t - B) ^ 2 * ρ t) := by
      rw [integral_add (hρ.const_mul _) (hgap.const_mul _), integral_const_mul,
        integral_const_mul, hnorm, mul_one]
    _ ≤ _ := by
      have hk := k_gap_sq_le hB.le hm
      have hg := integral_root_gap_le hρ hρn hB h2 h4 hm2 hm4
      dsimp [B] at *
      linarith

lemma moment_bound_linear {J m S b : ℝ} (hJ : 1 ≤ J) (hb : 0 ≤ b)
    (hB : 0 < J ^ 2 - m ^ 2) (hS : S = (J ^ 2 - m ^ 2) * b / J) :
    (8 * m ^ 2 * S + 6 * S ^ 2) / (J ^ 2 - m ^ 2) ≤ (8 * b + 6 * b ^ 2) * J := by
  have hJp : 0 < J := by linarith
  have hJ2p : 0 < J ^ 2 := by positivity
  have hm : m ^ 2 / J ≤ J := by
    apply (div_le_iff₀ hJp).mpr
    nlinarith
  have hd : (J ^ 2 - m ^ 2) / J ^ 2 ≤ 1 := by
    apply (div_le_iff₀ hJ2p).mpr
    nlinarith [sq_nonneg m]
  calc
    _ = 8 * b * (m ^ 2 / J) + 6 * b ^ 2 * ((J ^ 2 - m ^ 2) / J ^ 2) := by
      rw [hS]
      field_simp [ne_of_gt hJp, ne_of_gt hB]
    _ ≤ 8 * b * J + 6 * b ^ 2 * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (mul_le_mul_of_nonneg_left hd (by positivity))
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hJ)]

-- 这里的常数仅依赖宽度 b；边界距可以任意小而无需另加假设。
lemma integral_energy_uniform {ρ : ℝ → ℝ} {J m S b : ℝ}
    (hρ : Integrable ρ) (hρn : ∀ t, 0 ≤ ρ t) (hnorm : (∫ t, ρ t) = 1)
    (hJ : 1 ≤ J) (hb : 0 ≤ b) (hB : 0 < J ^ 2 - m ^ 2) (hm : |m| ≤ J)
    (hS : S = (J ^ 2 - m ^ 2) * b / J)
    (h2 : Integrable (fun t => (t - m) ^ 2 * ρ t))
    (h4 : Integrable (fun t => (t - m) ^ 4 * ρ t))
    (hm2 : (∫ t, (t - m) ^ 2 * ρ t) = S)
    (hm4 : (∫ t, (t - m) ^ 4 * ρ t) = 3 * S ^ 2) :
    (∫ t, (k J m - q J t) ^ 2 * ρ t) ≤ (5 / 2 + 16 * b + 12 * b ^ 2) * J := by
  have he := integral_energy_le hρ hρn hnorm hB hm h2 h4 hm2 hm4
  have hmom := moment_bound_linear hJ hb hB hS
  nlinarith

noncomputable def width (J m b : ℝ) : ℝ := J * (1 - (m / J) ^ 2) * b

lemma width_eq {J : ℝ} (hJ : J ≠ 0) (m b : ℝ) :
    width J m b = (J ^ 2 - m ^ 2) * b / J := by
  unfold width
  field_simp
  <;> ring

lemma width_pos {J m b : ℝ} (hJ : 0 < J) (hb : 0 < b) (hB : 0 < J ^ 2 - m ^ 2) :
    0 < width J m b := by
  rw [width_eq (ne_of_gt hJ)]
  positivity

-- 将通用矩定理直接应用于原稿的归一高斯幅值。
theorem gaussian_energy_uniform {J m b : ℝ} (hJ : 1 ≤ J) (hb : 0 < b)
    (hB : 0 < J ^ 2 - m ^ 2) (hm : |m| ≤ J) :
    (∫ t, (k J m - q J t) ^ 2 * column m (width J m b) t ^ 2) ≤
      (5 / 2 + 16 * b + 12 * b ^ 2) * J := by
  have hJp : 0 < J := by linarith
  have hS := width_pos hJp hb hB
  exact integral_energy_uniform (integrable_column_sq m hS) (fun t => sq_nonneg _)
    (integral_column_sq m hS) hJ hb.le hB hm (width_eq (ne_of_gt hJp) m b)
    (integrable_centered_pow_column_sq m hS 2)
    (integrable_centered_pow_column_sq m hS 4)
    (integral_centered_sq_column_sq m hS)
    (integral_centered_fourth_column_sq m hS)

theorem gaussian_energy_uniform_of_width_bound {J m b M : ℝ} (hJ : 1 ≤ J) (hb : 0 < b)
    (hbM : b ≤ M) (hm : |m| ≤ J - 1 / 2) :
    (∫ t, (k J m - q J t) ^ 2 * column m (width J m b) t ^ 2) ≤
      (5 / 2 + 16 * M + 12 * M ^ 2) * J := by
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  have hB : 0 < J ^ 2 - m ^ 2 := by
    nlinarith [mul_pos (show 0 < J - m by linarith) (show 0 < J + m by linarith)]
  have he := gaussian_energy_uniform hJ hb hB (show |m| ≤ J by linarith)
  have hsq : b ^ 2 ≤ M ^ 2 := by nlinarith
  have hc : 5 / 2 + 16 * b + 12 * b ^ 2 ≤ 5 / 2 + 16 * M + 12 * M ^ 2 := by
    linarith
  exact he.trans (mul_le_mul_of_nonneg_right hc (by linarith))

end CopyQuantumMetrology.GlobalBounds

