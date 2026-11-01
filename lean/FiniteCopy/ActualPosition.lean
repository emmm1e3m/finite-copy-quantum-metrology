import FiniteCopy.SymmetricPosition
open MeasureTheory
namespace CopyQuantumMetrology.Bulk
open GlobalBounds

lemma q_scale {J : ℝ} (hJ : 0 < J) (x : ℝ) :
    q J (J*x)=J*clippedRoot (1-x^2) := by
  have hq := q_nonneg J (J*x)
  have hc := clippedRoot_nonneg (1-x^2)
  have hs : q J (J*x)^2=(J*clippedRoot (1-x^2))^2 := by
    simp only [q_sq,mul_pow,clippedRoot_sq]
    rw [mul_max_of_nonneg _ _ (sq_nonneg J)]
    congr 1 <;> ring
  nlinarith [mul_nonneg hJ.le hc]

lemma k_scale {J : ℝ} (hJ : 0 < J) (x : ℝ) :
    k J (J*x)=J*symmetricRoot x (1/(2*J)) := by
  have hJ0 := ne_of_gt hJ
  unfold k symmetricRoot
  have ep : J*x+1/2=J*(x+1/(2*J)) := by field_simp
  have en : J*x-1/2=J*(x-1/(2*J)) := by field_simp
  rw [ep,en,q_scale hJ,q_scale hJ]
  ring

-- 原始高斯列与真实离散 k 系数的积分误差，不含渐近假设。
theorem actual_position_error {J x B h : ℝ} (hJ : 0 < J) (hB : 0 < B)
    (hBs : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) (hstep : 1/(2*J) ≤ h) :
    |(∫ t, (k J (J*x)-q J t)^2*column (J*x) ((J*h)^2) t^2)/J-
      J*h^2*(x/B)^2| ≤
      J*h^3*(48*|x/B| * positionConstant x B+147*positionConstant x B^2) := by
  have hJ0 := ne_of_gt hJ
  have hh0 := ne_of_gt hh
  have hS : 0 < (J*h)^2 := sq_pos_of_pos (mul_pos hJ hh)
  let K := symmetricRoot x (1/(2*J))
  have hr : 0 ≤ 1/(2*J) := by positivity
  have hC := positionConstant_nonneg x hB
  have hK : |K-B| ≤ h^2*positionConstant x B := by
    have hk := symmetricRoot_error x B (1/(2*J)) hB hBs (by rw [abs_of_nonneg hr]; exact hstep.trans hh1)
    have hs : (1/(2*J))^2 ≤ h^2 := by nlinarith
    exact hk.trans (mul_le_mul_of_nonneg_right hs hC)
  have he : (∫ t, (k J (J*x)-q J t)^2*column (J*x) ((J*h)^2) t^2)/J =
      J*h^2*(∫ y, ((K-clippedRoot (1-(x+h*y)^2))/h)^2*column 0 1 y^2) := by
    rw [gaussian_integral_standardize _ _ hS,Real.sqrt_sq (mul_pos hJ hh).le]
    have ei : (∫ y, (k J (J*x)-q J (J*x+J*h*y))^2*column 0 1 y^2)=
        (J*h)^2*(∫ y, ((K-clippedRoot (1-(x+h*y)^2))/h)^2*column 0 1 y^2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show J*x+J*h*y=J*(x+h*y) by ring,q_scale hJ,k_scale hJ]
      dsimp [K]
      field_simp
      <;> ring
    rw [ei]
    field_simp
    <;> ring
  rw [he,← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ J*h^2)]
  have hi := shifted_position_integral_error x B K h hB hBs hh hh1 hK
  convert mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ J*h^2) using 1 <;> ring

theorem actual_position_error_width {J x B b h : ℝ} (hJ : 0 < J) (hB : 0 < B)
    (hBs : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1) (hstep : 1/(2*J) ≤ h)
    (hwidth : J*h^2=B^2*b) :
    |(∫ t, (k J (J*x)-q J t)^2*column (J*x) (J*B^2*b) t^2)/J-x^2*b| ≤
      J*h^3*(48*|x/B| * positionConstant x B+147*positionConstant x B^2) := by
  have hs : J*B^2*b=(J*h)^2 := by nlinarith [congrArg (fun a : ℝ => J*a) hwidth]
  have hm : J*h^2*(x/B)^2=x^2*b := by
    rw [hwidth]
    field_simp [ne_of_gt hB]
    <;> ring
  rw [hs,← hm]
  exact actual_position_error hJ hB hBs hh hh1 hstep

end CopyQuantumMetrology.Bulk

