import FiniteCopy.Gaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology

namespace CopyQuantumMetrology.Bulk

noncomputable def clippedRoot (u : ℝ) : ℝ := Real.sqrt (max u 0)

lemma clippedRoot_nonneg (u : ℝ) : 0 ≤ clippedRoot u := Real.sqrt_nonneg _

lemma clippedRoot_sq (u : ℝ) : clippedRoot u ^ 2 = max u 0 := by
  exact Real.sq_sqrt (le_max_right _ _)

-- 全实轴的二阶根式余量，允许 u 越过零点。
lemma clippedRoot_quadratic_remainder (u B : ℝ) (hB : 0 < B) :
    |clippedRoot u - B - (u - B^2) / (2*B)| ≤
      (u - B^2)^2 / (2*B^3) := by
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hB2 : 0 < B^2 := sq_pos_of_pos hB
  have hB3 : 0 < B^3 := pow_pos hB 3
  rcases le_total 0 u with hu | hu
  · have hq := clippedRoot_nonneg u
    have hq2 : clippedRoot u ^ 2 = u := by rw [clippedRoot_sq, max_eq_left hu]
    have he : clippedRoot u - B - (u-B^2)/(2*B) =
        -(clippedRoot u-B)^2/(2*B) := by
      field_simp
      nlinarith
    rw [he, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity : 0 < 2*B)]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*B) (by positivity : 0 < 2*B^3)).2
    have hmul : 0 ≤ (clippedRoot u-B)^2 * (clippedRoot u^2+2*B*clippedRoot u) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have hbase : (clippedRoot u-B)^2 * B^2 ≤ (u-B^2)^2 := by
      conv_rhs => rw [← hq2]
      nlinarith only [hmul]
    convert mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2*B) using 1 <;> ring
  · have hq : clippedRoot u = 0 := by simp [clippedRoot, max_eq_right hu]
    have he : 0 - B - (u-B^2)/(2*B) = -(u+B^2)/(2*B) := by field_simp; ring
    rw [hq, he, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2*B)]
    have hmul : 0 ≤ (-u)*B^2 := mul_nonneg (neg_nonneg.mpr hu) hB2.le
    have hbase : |u+B^2| * B^2 ≤ (u-B^2)^2 := by
      rcases le_total 0 (u+B^2) with hh | hh
      · rw [abs_of_nonneg hh]
        nlinarith [sq_nonneg u]
      · rw [abs_of_nonpos hh]
        nlinarith [sq_nonneg (u+B^2)]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*B) (by positivity : 0 < 2*B^3)).2
    convert mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2*B) using 1 <;> ring




lemma position_remainder (J m B z : ℝ) (hB : 0 < B) (hBsq : B^2 = J^2-m^2) :
    |clippedRoot (J^2-(m+z)^2) - B + m*z/B| ≤
      (1/(2*B)+4*m^2/B^3)*z^2 + z^4/B^3 := by
  let u := J^2-(m+z)^2
  have hB0 := ne_of_gt hB
  have hu : u-B^2 = -(2*m*z+z^2) := by dsimp [u]; nlinarith only [hBsq]
  have he : clippedRoot u-B+m*z/B =
      (clippedRoot u-B-(u-B^2)/(2*B))-z^2/(2*B) := by rw [hu]; field_simp; ring
  change |clippedRoot u-B+m*z/B| ≤ _
  rw [he]
  calc
    _ ≤ |clippedRoot u-B-(u-B^2)/(2*B)| + |z^2/(2*B)| := abs_sub _ _
    _ ≤ (u-B^2)^2/(2*B^3) + z^2/(2*B) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ z^2/(2*B))]
      exact add_le_add (clippedRoot_quadratic_remainder u B hB) le_rfl
    _ ≤ (1/(2*B)+4*m^2/B^3)*z^2 + z^4/B^3 := by
      rw [hu]
      have hs : (2*m*z+z^2)^2 ≤ 8*m^2*z^2+2*z^4 := by nlinarith [sq_nonneg (2*m*z-z^2)]
      have hh := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*B^3)
      simp only [neg_sq] at *
      calc
        _ ≤ (8*m^2*z^2+2*z^4)/(2*B^3)+z^2/(2*B) := add_le_add hh le_rfl
        _ = _ := by field_simp; ring

lemma square_error_of_remainder {v l R : ℝ} (h : |v-l| ≤ R) :
    |v^2-l^2| ≤ 2 * |l| * R+R^2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans h
  have he : v^2-l^2 = 2*l*(v-l)+(v-l)^2 := by ring
  rw [he]
  calc
    _ ≤ |2*l*(v-l)| + |(v-l)^2| := abs_add_le _ _
    _ = 2 * |l| * |v-l| + |v-l|^2 := by simp [abs_mul, abs_pow]
    _ ≤ 2 * |l| * R+R^2 := by gcongr

noncomputable def positionConstant (x B : ℝ) : ℝ := 1/(2*B)+4*x^2/B^3+1/B^3

lemma positionConstant_nonneg (x : ℝ) {B : ℝ} (hB : 0 < B) :
    0 ≤ positionConstant x B := by unfold positionConstant; positivity

-- h 为标准差与宏观尺度的比；此估计在全部高斯变量 y 上成立。
lemma scaled_position_remainder (x B h y : ℝ) (hB : 0 < B)
    (hBsq : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) :
    |(B-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y| ≤
      h*positionConstant x B*(y^2+y^4) := by
  have hr := position_remainder 1 x B (h*y) hB (by simpa using hBsq)
  have hB0 := ne_of_gt hB
  have hh0 := ne_of_gt hh
  have hA : 0 ≤ 1/(2*B)+4*x^2/B^3 := by positivity
  have hC : 0 ≤ 1/B^3 := by positivity
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hh4 : h^4 ≤ h^2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh2)]
  have hr' : |clippedRoot (1-(x+h*y)^2)-B+x*(h*y)/B| ≤
      h^2*positionConstant x B*(y^2+y^4) := by
    calc
      _ ≤ (1/(2*B)+4*x^2/B^3)*(h*y)^2 + (h*y)^4/B^3 := by simpa using hr
      _ ≤ (1/(2*B)+4*x^2/B^3)*h^2*y^2 + (1/B^3)*h^2*y^4 := by
        have hm := mul_le_mul_of_nonneg_right hh4 (mul_nonneg hC (by positivity : 0 ≤ y^4))
        convert add_le_add (le_refl ((1/(2*B)+4*x^2/B^3)*h^2*y^2)) hm using 1 <;> ring
      _ ≤ _ := by
        unfold positionConstant
        have hp := mul_nonneg (mul_nonneg hA (sq_nonneg h)) (by positivity : 0 ≤ y^4)
        have hq := mul_nonneg (mul_nonneg hC (sq_nonneg h)) (sq_nonneg y)
        nlinarith only [hp,hq]
  have he : (B-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y =
      -(clippedRoot (1-(x+h*y)^2)-B+x*(h*y)/B)/h := by field_simp; ring
  rw [he, abs_div, abs_neg, abs_of_pos hh]
  apply (div_le_iff₀ hh).2
  convert hr' using 1 <;> ring

noncomputable def positionErrorPolynomial (x B y : ℝ) : ℝ :=
  2 * |x / B| * positionConstant x B * (y^2 + 2*y^4 + y^6) +
    positionConstant x B ^ 2 * (y^4 + 2*y^6 + y^8)

lemma scaled_position_square_error (x B h y : ℝ) (hB : 0 < B)
    (hBsq : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) :
    |((B-clippedRoot (1-(x+h*y)^2))/h)^2 - ((x/B)*y)^2| ≤
      h * positionErrorPolynomial x B y := by
  have hC := positionConstant_nonneg x hB
  have hr := square_error_of_remainder (scaled_position_remainder x B h y hB hBsq hh hh1)
  have hy : |y| ≤ 1+y^2 := by nlinarith [sq_nonneg (|y|-1), sq_abs y]
  have hp : 0 ≤ y^2+y^4 := by positivity
  have hy' := mul_le_mul_of_nonneg_right hy hp
  have hh2 : h^2 ≤ h := by nlinarith
  calc
    _ ≤ 2 * |(x/B)*y| * (h*positionConstant x B*(y^2+y^4)) +
        (h*positionConstant x B*(y^2+y^4))^2 := hr
    _ ≤ h * (2 * |x/B| * positionConstant x B * ((1+y^2)*(y^2+y^4))) +
        h * (positionConstant x B ^ 2 * (y^2+y^4)^2) := by
      rw [abs_mul]
      have ht := mul_le_mul_of_nonneg_left hy' (by positivity :
        0 ≤ 2 * |x/B| * h * positionConstant x B)
      have hs := mul_le_mul_of_nonneg_right hh2 (by positivity :
        0 ≤ positionConstant x B ^ 2 * (y^2+y^4)^2)
      convert add_le_add ht hs using 1 <;> ring
    _ = _ := by unfold positionErrorPolynomial; ring

lemma integrable_standard_moment (n : ℕ) :
    Integrable (fun y : ℝ => y^n * column 0 1 y^2) := by
  simpa using integrable_centered_pow_column_sq 0 (by norm_num : (0:ℝ)<1) n

lemma integral_standard_second : (∫ y : ℝ, y^2 * column 0 1 y^2) = 1 := by
  simpa using integral_centered_sq_column_sq 0 (by norm_num : (0:ℝ)<1)

lemma integral_standard_fourth : (∫ y : ℝ, y^4 * column 0 1 y^2) = 3 := by
  simpa using integral_centered_fourth_column_sq 0 (by norm_num : (0:ℝ)<1)

lemma integral_standard_sixth : (∫ y : ℝ, y^6 * column 0 1 y^2) = 15 := by
  simpa using integral_centered_sixth_column_sq 0 (by norm_num : (0:ℝ)<1)

lemma integral_standard_eighth : (∫ y : ℝ, y^8 * column 0 1 y^2) = 105 := by
  simpa using integral_centered_eighth_column_sq 0 (by norm_num : (0:ℝ)<1)

lemma integrable_position_error (x B : ℝ) :
    Integrable (fun y => positionErrorPolynomial x B y * column 0 1 y^2) := by
  have h := (((integrable_standard_moment 2).add
    ((integrable_standard_moment 4).const_mul 2)).add
    (integrable_standard_moment 6)).const_mul (2 * |x/B| * positionConstant x B)
  have k := (((integrable_standard_moment 4).add
    ((integrable_standard_moment 6).const_mul 2)).add
    (integrable_standard_moment 8)).const_mul (positionConstant x B ^ 2)
  convert h.add k using 1
  ext y
  simp only [positionErrorPolynomial, Pi.add_apply]
  ring

lemma integral_position_error (x B : ℝ) :
    (∫ y, positionErrorPolynomial x B y * column 0 1 y^2) =
      44 * |x/B| * positionConstant x B + 138 * positionConstant x B ^ 2 := by
  let p := fun y : ℝ => (y^2 * column 0 1 y^2 + 2 * (y^4 * column 0 1 y^2)) +
    y^6 * column 0 1 y^2
  let q := fun y : ℝ => (y^4 * column 0 1 y^2 + 2 * (y^6 * column 0 1 y^2)) +
    y^8 * column 0 1 y^2
  have hp : Integrable p := ((integrable_standard_moment 2).add
    ((integrable_standard_moment 4).const_mul 2)).add (integrable_standard_moment 6)
  have hq : Integrable q := ((integrable_standard_moment 4).add
    ((integrable_standard_moment 6).const_mul 2)).add (integrable_standard_moment 8)
  have ep : (∫ y, p y) = 22 := by
    dsimp [p]
    have he := integral_add ((integrable_standard_moment 2).add
      ((integrable_standard_moment 4).const_mul 2)) (integrable_standard_moment 6)
    simp only [Pi.add_apply] at he
    rw [he,
      integral_add (integrable_standard_moment 2) ((integrable_standard_moment 4).const_mul 2),
      integral_const_mul, integral_standard_second, integral_standard_fourth, integral_standard_sixth]
    norm_num
  have eq : (∫ y, q y) = 138 := by
    dsimp [q]
    have he := integral_add ((integrable_standard_moment 4).add
      ((integrable_standard_moment 6).const_mul 2)) (integrable_standard_moment 8)
    simp only [Pi.add_apply] at he
    rw [he,
      integral_add (integrable_standard_moment 4) ((integrable_standard_moment 6).const_mul 2),
      integral_const_mul, integral_standard_fourth, integral_standard_sixth, integral_standard_eighth]
    norm_num
  calc
    _ = ∫ y, (2 * |x/B| * positionConstant x B) * p y +
        positionConstant x B ^ 2 * q y := by
      congr 1
      ext y
      dsimp [p,q,positionErrorPolynomial]
      ring
    _ = _ := by
      rw [integral_add (hp.const_mul _) (hq.const_mul _), integral_const_mul,
        integral_const_mul, ep, eq]
      ring

lemma integrable_scaled_position (x B h : ℝ) (hB : 0 < B)
    (hBsq : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) :
    Integrable (fun y => ((B-clippedRoot (1-(x+h*y)^2))/h)^2 * column 0 1 y^2) := by
  have hlin : Integrable (fun y => ((x/B)*y)^2 * column 0 1 y^2) := by
    convert (integrable_standard_moment 2).const_mul ((x/B)^2) using 1
    ext y
    ring
  have hd : Integrable (fun y =>
      (((B-clippedRoot (1-(x+h*y)^2))/h)^2 - ((x/B)*y)^2) * column 0 1 y^2) := by
    apply ((integrable_position_error x B).const_mul h).mono'
    · have hc : Continuous (fun y =>
          (((B-clippedRoot (1-(x+h*y)^2))/h)^2 - ((x/B)*y)^2) * column 0 1 y^2) := by
        unfold clippedRoot column
        fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (column 0 1 y))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (scaled_position_square_error x B h y hB hBsq hh hh1) (sq_nonneg (column 0 1 y))
  convert hd.add hlin using 1
  ext y
  simp only [Pi.add_apply]
  ring

-- 真正的 Lebesgue 积分误差；主项由标准高斯二阶矩算出。
lemma scaled_position_integral_error (x B h : ℝ) (hB : 0 < B)
    (hBsq : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) :
    |(∫ y, ((B-clippedRoot (1-(x+h*y)^2))/h)^2 * column 0 1 y^2) - (x/B)^2| ≤
      h * (44 * |x/B| * positionConstant x B + 138 * positionConstant x B ^ 2) := by
  have hlin : Integrable (fun y => ((x/B)*y)^2 * column 0 1 y^2) := by
    convert (integrable_standard_moment 2).const_mul ((x/B)^2) using 1
    ext y
    ring
  have elin : (∫ y, ((x/B)*y)^2 * column 0 1 y^2) = (x/B)^2 := by
    simp_rw [mul_pow, mul_assoc]
    rw [integral_const_mul, integral_standard_second, mul_one]
  have he := norm_integral_le_of_norm_le ((integrable_position_error x B).const_mul h)
    (f := fun y => (((B-clippedRoot (1-(x+h*y)^2))/h)^2 - ((x/B)*y)^2) * column 0 1 y^2)
    (by
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (column 0 1 y))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (scaled_position_square_error x B h y hB hBsq hh hh1) (sq_nonneg (column 0 1 y)))
  have ee : (∫ y, (((B-clippedRoot (1-(x+h*y)^2))/h)^2 - ((x/B)*y)^2) * column 0 1 y^2) =
      (∫ y, ((B-clippedRoot (1-(x+h*y)^2))/h)^2 * column 0 1 y^2) - (x/B)^2 := by
    simp_rw [sub_mul]
    rw [integral_sub (integrable_scaled_position x B h hB hBsq hh hh1) hlin, elin]
  rw [ee, Real.norm_eq_abs, integral_const_mul, integral_position_error] at he
  exact he

end CopyQuantumMetrology.Bulk





