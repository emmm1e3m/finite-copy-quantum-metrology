import FiniteCopy.Gaussian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open MeasureTheory
namespace CopyQuantumMetrology.Bulk

lemma column_sq_standardize (m y : ℝ) {S : ℝ} (hS : 0 < S) :
    column m S (m + Real.sqrt S * y)^2 * Real.sqrt S = column 0 1 y^2 := by
  rw [column_sq_eq_gaussianPDF _ _ hS, column_sq_eq_gaussianPDF _ _ (by norm_num : (0:ℝ)<1)]
  change (Real.sqrt (2*Real.pi*S))⁻¹ *
    Real.exp (-(m + Real.sqrt S*y - m)^2/(2*S)) * Real.sqrt S =
    (Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(y-0)^2/(2*1))
  have hs : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have he : -(m + Real.sqrt S*y - m)^2/(2*S) = -(y-0)^2/(2*1) := by
    rw [show m + Real.sqrt S*y - m = Real.sqrt S*y by ring, mul_pow,
      Real.sq_sqrt hS.le]
    field_simp
    <;> ring
  rw [he, Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi), mul_inv_rev]
  simp only [mul_one]
  field_simp

lemma gaussian_integral_standardize (f : ℝ → ℝ) (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, f t * column m S t^2) =
      ∫ y, f (m + Real.sqrt S*y) * column 0 1 y^2 := by
  have hs : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have ht := Measure.integral_comp_mul_left
    (fun u => f (m+u) * column m S (m+u)^2) (Real.sqrt S)
  rw [integral_add_left_eq_self (fun t => f t * column m S t^2) m] at ht
  simp only [smul_eq_mul, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hS)] at ht
  calc
    _ = Real.sqrt S * (∫ y, f (m+Real.sqrt S*y) * column m S (m+Real.sqrt S*y)^2) := by
      rw [ht]
      field_simp
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← column_sq_standardize m y hS]
      ring

end CopyQuantumMetrology.Bulk

