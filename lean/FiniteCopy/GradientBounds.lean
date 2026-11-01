import FiniteCopy.GlobalBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Interval

namespace CopyQuantumMetrology.GradientBounds

open GlobalBounds

-- 移动高斯列的一阶参数导数，保持原始幅值定义。
noncomputable def movingDeriv (s S S₁ t : ℝ) : ℝ :=
  column s S t * ((t-s)/(2*S) + S₁/(4*S)*((t-s)^2/S-1))

lemma score_sq_le (z S S₁ : ℝ) (hS : 0 < S) :
    (z/(2*S) + S₁/(4*S)*(z^2/S-1))^2 ≤
      z^2/(2*S^2) + S₁^2/(4*S^2)*(z^4/S^2+1) := by
  have h₁ : (z/(2*S) + S₁/(4*S)*(z^2/S-1))^2 ≤
      2*(z/(2*S))^2 + 2*(S₁/(4*S)*(z^2/S-1))^2 := by
    nlinarith [sq_nonneg (z/(2*S) - S₁/(4*S)*(z^2/S-1))]
  have h₂ : (z^2/S-1)^2 ≤ 2*((z^2/S)^2+1) := by
    nlinarith [sq_nonneg (z^2/S+1)]
  have h₃ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2*(S₁/(4*S))^2 by positivity)
  calc
    _ ≤ _ := h₁
    _ ≤ 2*(z/(2*S))^2 + 4*(S₁/(4*S))^2*((z^2/S)^2+1) := by
      nlinarith
    _ = _ := by field_simp

-- 正部根式的全轴二次上界，不排除越过两个极点的样本。
lemma q_le_quadratic {J s r : ℝ} (hJ : 0 < J) (hr : 0 < r)
    (hs : |s| ≤ J) (hrJ : r ≤ J) (hB : J*r ≤ J^2-s^2) (t : ℝ) :
    q J t ≤ 2 * Real.sqrt (J^2-s^2) * (1 + (t-s)^2/r^2) := by
  let B := Real.sqrt (J^2-s^2)
  have hBs : B^2 = J^2-s^2 := Real.sq_sqrt (by nlinarith)
  have hBp : 0 < B := Real.sqrt_pos.mpr (by nlinarith)
  have hz : |t^2-s^2| ≤ 2*J*|t-s|+(t-s)^2 := by
    calc
      _ = |2*s*(t-s)+(t-s)^2| := by congr 1; ring
      _ ≤ |2*s*(t-s)|+|(t-s)^2| := abs_add_le _ _
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_sq]
        gcongr
  have hgap := abs_q_sub_sqrt (show 0 < J^2-s^2 by nlinarith) t
  have hq : q J t ≤ B + (2*J*|t-s|+(t-s)^2)/B := by
    have hh := (le_abs_self (q J t-B)).trans hgap
    have hdiv := (div_le_div_iff_of_pos_right hBp).mpr hz
    dsimp [B] at *
    linarith
  have hyoung : 2*r*|t-s| ≤ r^2+(t-s)^2 := by
    nlinarith [sq_nonneg (r-|t-s|), sq_abs (t-s)]
  have hpoly : B + (2*J*|t-s|+(t-s)^2)/B ≤ 2*B*(1+(t-s)^2/r^2) := by
    apply (mul_le_mul_iff_right₀ (show 0 < B*r^2 by positivity)).mp
    have hB' : J*r ≤ B^2 := by rwa [hBs]
    have hb₁ : J*r^3 ≤ B^2*r^2 := by nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hB')]
    have hb₂ : (J*r+r^2)*(t-s)^2 ≤ 2*B^2*(t-s)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [hB', mul_nonneg hr.le (sub_nonneg.mpr hrJ)]
    have hy := mul_le_mul_of_nonneg_left hyoung (show 0 ≤ J*r by positivity)
    field_simp [ne_of_gt hBp, ne_of_gt hr]
    nlinarith only [hb₁, hb₂, hy]
  exact hq.trans hpoly

-- 三个偶数矩已经足以积分整个导数能量上界。
lemma gaussian_derivative_energy_le {s S S₁ A B : ℝ} (hS : 0 < S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {w : ℝ → ℝ}
    (hwc : Continuous w) (hwn : ∀ t, 0 ≤ w t)
    (hwp : ∀ t, w t ≤ A+B*(t-s)^2) :
    (∫ t, w t * movingDeriv s S S₁ t ^ 2) ≤
      A/(2*S) + A*S₁^2/S^2 + 3*B/2 + 4*B*S₁^2/S := by
  let P := fun t : ℝ =>
    (A/(2*S^2)) * ((t-s)^2*column s S t^2) +
    (A*S₁^2/(4*S^4)) * ((t-s)^4*column s S t^2) +
    (A*S₁^2/(4*S^2)) * column s S t^2 +
    (B/(2*S^2)) * ((t-s)^4*column s S t^2) +
    (B*S₁^2/(4*S^4)) * ((t-s)^6*column s S t^2) +
    (B*S₁^2/(4*S^2)) * ((t-s)^2*column s S t^2)
  have hi0 := integrable_column_sq s hS
  have hi2 := integrable_centered_pow_column_sq s hS 2
  have hi4 := integrable_centered_pow_column_sq s hS 4
  have hi6 := integrable_centered_pow_column_sq s hS 6
  have hiP : Integrable P :=
    (((((hi2.const_mul _).add (hi4.const_mul _)).add (hi0.const_mul _)).add
      (hi4.const_mul _)).add (hi6.const_mul _)).add (hi2.const_mul _)
  have hbound : ∀ t, w t * movingDeriv s S S₁ t ^ 2 ≤ P t := by
    intro t
    have h₁ := mul_le_mul_of_nonneg_left (score_sq_le (t-s) S S₁ hS)
      (show 0 ≤ column s S t^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left h₁ (hwn t)
    have h₃ := mul_le_mul_of_nonneg_right (hwp t)
      (show 0 ≤ column s S t^2 *
        ((t-s)^2/(2*S^2)+S₁^2/(4*S^2)*((t-s)^4/S^2+1)) by positivity)
    calc
      _ ≤ (A+B*(t-s)^2) * (column s S t^2 *
          ((t-s)^2/(2*S^2)+S₁^2/(4*S^2)*((t-s)^4/S^2+1))) := by
        apply le_trans _ h₃
        simpa only [movingDeriv, mul_pow] using h₂
      _ = P t := by dsimp [P]; ring
  have hi : Integrable (fun t => w t * movingDeriv s S S₁ t^2) := by
    apply hiP.mono'
    · apply Continuous.aestronglyMeasurable
      unfold movingDeriv column
      fun_prop
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwn t) (sq_nonneg _))]
      exact hbound t
  calc
    _ ≤ ∫ t, P t := integral_mono hi hiP hbound
    _ = _ := by
      dsimp only [P]
      rw [integral_add (by fun_prop) (hi2.const_mul _)]
      rw [integral_add (by fun_prop) (hi6.const_mul _)]
      rw [integral_add (by fun_prop) (hi4.const_mul _)]
      rw [integral_add (by fun_prop) (hi0.const_mul _)]
      rw [integral_add (hi2.const_mul _) (hi4.const_mul _)]
      simp only [integral_const_mul, integral_centered_sq_column_sq s hS,
        integral_centered_fourth_column_sq s hS, integral_centered_sixth_column_sq s hS,
        integral_column_sq s hS]
      field_simp
      <;> ring

-- 长度为一的区间上，积分平方界由方差的非负性直接得到。
theorem gaussian_edge_derivative_uniform {J s r S S₁ c : ℝ} (hJ : 0 < J)
    (hr : 1/2 ≤ r) (hs : |s| ≤ J) (hrJ : r ≤ J)
    (hB : J*r ≤ J^2-s^2) (hS : r/4 ≤ S) (hc : 0 ≤ c)
    (hcB : c * Real.sqrt (J^2-s^2) ≤ 4*J*r) :
    c * (∫ t, q J t * movingDeriv s S S₁ t^2) ≤ (40+768*S₁^2)*J := by
  have hrp : 0 < r := by linarith
  have hSp : 0 < S := by linarith
  let B := Real.sqrt (J^2-s^2)
  have hBn : 0 ≤ B := Real.sqrt_nonneg _
  have he := gaussian_derivative_energy_le (s := s) (S₁ := S₁) hSp
    (show 0 ≤ 2*B by positivity) (show 0 ≤ 2*B/r^2 by positivity)
    (continuous_q J) (q_nonneg J) (fun t => by
      have h := q_le_quadratic hJ hrp hs hrJ hB t
      convert h using 1 <;> dsimp [B] <;> ring)
  have hrS : r/S ≤ 4 := (div_le_iff₀ hSp).2 (by linarith)
  have hinvS : 1/S ≤ 8 := (div_le_iff₀ hSp).2 (by linarith)
  have hinvr : 1/r ≤ 2 := (div_le_iff₀ hrp).2 (by linarith)
  have hrS2 : r/S^2 ≤ 32 := by
    calc
      _ = (r/S)*(1/S) := by ring
      _ ≤ 4*8 := mul_le_mul hrS hinvS (by positivity) (by norm_num)
      _ = _ := by norm_num
  have hrSinv : 1/(r*S) ≤ 16 := by
    calc
      _ = (1/r)*(1/S) := by ring
      _ ≤ 2*8 := mul_le_mul hinvr hinvS (by positivity) (by norm_num)
      _ = _ := by norm_num
  calc
    _ ≤ c * (2*B/(2*S)+(2*B)*S₁^2/S^2+3*(2*B/r^2)/2+
        4*(2*B/r^2)*S₁^2/S) := mul_le_mul_of_nonneg_left he hc
    _ = (c*B) * (1/S+2*S₁^2/S^2+3/r^2+8*S₁^2/(r^2*S)) := by ring
    _ ≤ (4*J*r) * (1/S+2*S₁^2/S^2+3/r^2+8*S₁^2/(r^2*S)) :=
      mul_le_mul_of_nonneg_right hcB (by positivity)
    _ = J * (4*(r/S)+8*S₁^2*(r/S^2)+12*(1/r)+32*S₁^2*(1/(r*S))) := by
      field_simp
      <;> ring
    _ ≤ J*(4*4+8*S₁^2*32+12*2+32*S₁^2*16) := by
      gcongr
    _ = _ := by ring

-- 长度为一的区间上，积分平方界由方差的非负性直接得到。
lemma integral_unit_sq_le {f : ℝ → ℝ} (a : ℝ)
    (hf : IntegrableOn f (Ioc a (a + 1)))
    (hf2 : IntegrableOn (fun s => f s ^ 2) (Ioc a (a + 1))) :
    (∫ s in Ioc a (a + 1), f s) ^ 2 ≤ ∫ s in Ioc a (a + 1), f s ^ 2 := by
  let A := ∫ s in Ioc a (a + 1), f s
  have hconst : IntegrableOn (fun _ : ℝ => A ^ 2) (Ioc a (a + 1)) := integrableOn_const (hs := by simp)
  have heq : (∫ s in Ioc a (a + 1), (f s - A) ^ 2) =
      (∫ s in Ioc a (a + 1), f s ^ 2) - A ^ 2 := by
    calc
      _ = ∫ s in Ioc a (a + 1), f s ^ 2 - (2*A) * f s + A ^ 2 := by
        congr 1
        ext s
        ring
      _ = _ := by
        have hh := integral_add (hf2.sub (hf.const_mul (2*A))) hconst
        simp only [Pi.add_apply, Pi.sub_apply] at hh
        rw [hh]
        have hh' := integral_sub hf2 (hf.const_mul (2*A))
        rw [hh', integral_const_mul]
        simp only [setIntegral_const, Real.volume_real_Ioc_of_le (show a ≤ a + 1 by linarith)]
        dsimp [A]
        ring
  have hn : 0 ≤ ∫ s in Ioc a (a+1), (f s-A)^2 := integral_nonneg (fun s => sq_nonneg (f s-A))
  rw [heq] at hn
  dsimp [A] at hn
  linarith

-- FTC 与上一引理给出逐点参数有限差分的平方界。
lemma finite_difference_sq_le {v D : ℝ → ℝ} (a : ℝ)
    (hderiv : ∀ s ∈ Icc a (a + 1), HasDerivAt v (D s) s)
    (hD : ContinuousOn D (Icc a (a + 1))) :
    (v (a + 1) - v a)^2 ≤ ∫ s in Ioc a (a + 1), D s ^ 2 := by
  have hab : a ≤ a + 1 := by linarith
  have hi := hD.intervalIntegrable_of_Icc (μ := volume) hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa [uIcc_of_le hab] using hderiv) hi
  rw [intervalIntegral.integral_of_le hab] at hftc
  rw [← hftc]
  exact integral_unit_sq_le a hi.1 ((hD.pow 2).intervalIntegrable_of_Icc (μ := volume) hab).1

-- 真实 Fubini 交换参数与样本积分；唯一积分前提是非负导数能量的联合可积性。
theorem weighted_finite_difference_le {v D : ℝ → ℝ → ℝ} {q : ℝ → ℝ} (a : ℝ)
    (hq : ∀ t, 0 ≤ q t)
    (hderiv : ∀ t s, s ∈ Icc a (a + 1) → HasDerivAt (fun s => v s t) (D s t) s)
    (hD : ∀ t, ContinuousOn (fun s => D s t) (Icc a (a + 1)))
    (hfinite : Integrable (fun t => q t * (v (a+1) t - v a t)^2))
    (hprod : Integrable (fun p : ℝ × ℝ => q p.2 * D p.1 p.2 ^ 2)
      ((volume.restrict (Ioc a (a + 1))).prod volume)) :
    (∫ t, q t * (v (a+1) t - v a t)^2) ≤
      ∫ s in Ioc a (a+1), ∫ t, q t * D s t ^ 2 := by
  rw [integral_integral_swap hprod]
  apply integral_mono hfinite hprod.integral_prod_right
  intro t
  dsimp only
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (finite_difference_sq_le a (fun s hs => hderiv t s hs) (hD t)) (hq t)

-- 对 v+(a+1-s)v' 使用一次 FTC，直接得到二阶积分余量。
lemma finite_difference_remainder_sq_le {v D₁ D₂ : ℝ → ℝ} (a : ℝ)
    (hv : ∀ s ∈ Icc a (a+1), HasDerivAt v (D₁ s) s)
    (hD₁ : ∀ s ∈ Icc a (a+1), HasDerivAt D₁ (D₂ s) s)
    (hD₂ : ContinuousOn D₂ (Icc a (a+1))) :
    (v (a+1)-v a-D₁ a)^2 ≤ ∫ s in Ioc a (a+1), D₂ s^2 := by
  have hd : ∀ s ∈ Icc a (a+1),
      HasDerivAt (fun s => v s+(a+1-s)*D₁ s) ((a+1-s)*D₂ s) s := by
    intro s hs
    convert (hv s hs).add (((hasDerivAt_id s).const_sub (a+1)).mul (hD₁ s hs)) using 1
    · rfl
    · simp only [id_eq]; ring
  have hc : ContinuousOn (fun s => (a+1-s)*D₂ s) (Icc a (a+1)) := by fun_prop
  have h := finite_difference_sq_le a hd hc
  simp only [show a+1-(a+1)=0 by ring, zero_mul, add_zero,
    show a+1-a=1 by ring, one_mul] at h
  have hi : IntegrableOn (fun s => D₂ s^2) (Ioc a (a+1)) :=
    ((hD₂.pow 2).intervalIntegrable_of_Icc (by linarith : a ≤ a+1)).1
  have hik : IntegrableOn (fun s => ((a+1-s)*D₂ s)^2) (Ioc a (a+1)) :=
    ((hc.pow 2).intervalIntegrable_of_Icc (by linarith : a ≤ a+1)).1
  calc
    _ = (v (a+1)-(v a+D₁ a))^2 := by ring
    _ ≤ _ := h
    _ ≤ _ := by
      apply setIntegral_mono_on hik hi measurableSet_Ioc
      intro s hs
      have hsq : (a+1-s)^2 ≤ 1 := by
        have := hs.1
        have := hs.2
        nlinarith
      simpa only [mul_pow, one_mul] using
        mul_le_mul_of_nonneg_right hsq (sq_nonneg (D₂ s))

theorem weighted_remainder_le {v D₁ D₂ : ℝ → ℝ → ℝ} {q : ℝ → ℝ} (a : ℝ)
    (hq : ∀ t, 0 ≤ q t)
    (hv : ∀ t s, s ∈ Icc a (a+1) → HasDerivAt (fun s => v s t) (D₁ s t) s)
    (hD₁ : ∀ t s, s ∈ Icc a (a+1) → HasDerivAt (fun s => D₁ s t) (D₂ s t) s)
    (hD₂ : ∀ t, ContinuousOn (fun s => D₂ s t) (Icc a (a+1)))
    (hfinite : Integrable (fun t => q t*(v (a+1) t-v a t-D₁ a t)^2))
    (hprod : Integrable (fun p : ℝ × ℝ => q p.2*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc a (a+1))).prod volume)) :
    (∫ t, q t*(v (a+1) t-v a t-D₁ a t)^2) ≤
      ∫ s in Ioc a (a+1), ∫ t, q t*D₂ s t^2 := by
  rw [integral_integral_swap hprod]
  apply integral_mono hfinite hprod.integral_prod_right
  intro t
  dsimp only
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (finite_difference_remainder_sq_le a (fun s hs => hv t s hs)
      (fun s hs => hD₁ t s hs) (hD₂ t)) (hq t)

-- 可自由选择 η；若余量能量为 O(J⁻¹)，取 η=J⁻¹ᐟ² 即得双边能量误差。
theorem abs_energy_difference_le {f g q : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hq : ∀ t, 0 ≤ q t)
    (hf : Integrable (fun t => q t*f t^2))
    (hg : Integrable (fun t => q t*g t^2))
    (hr : Integrable (fun t => q t*(f t-g t)^2)) :
    |(∫ t, q t*f t^2)-(∫ t, q t*g t^2)| ≤
      η*(∫ t, q t*g t^2)+(1+1/η)*(∫ t, q t*(f t-g t)^2) := by
  have hp (x y : ℝ) : |x^2-y^2| ≤ η*y^2+(1+1/η)*(x-y)^2 := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hη).mp
      field_simp
      nlinarith [sq_nonneg (η*y+x-y), mul_nonneg hη.le (sq_nonneg (x-y))]
    · apply (mul_le_mul_iff_right₀ hη).mp
      field_simp
      nlinarith [sq_nonneg (η*y-x+y)]
  have hi := (hg.const_mul η).add (hr.const_mul (1+1/η))
  have ha : ∀ t, |q t*f t^2-q t*g t^2| ≤
      η*(q t*g t^2)+(1+1/η)*(q t*(f t-g t)^2) := by
    intro t
    have hh := mul_le_mul_of_nonneg_left (hp (f t) (g t)) (hq t)
    calc
      _ = q t*|f t^2-g t^2| := by rw [← mul_sub, abs_mul, abs_of_nonneg (hq t)]
      _ ≤ q t*(η*g t^2+(1+1/η)*(f t-g t)^2) := hh
      _ = _ := by ring
  calc
    _ = |∫ t, q t*f t^2-q t*g t^2| := by rw [integral_sub hf hg]
    _ ≤ ∫ t, |q t*f t^2-q t*g t^2| := abs_integral_le_integral_abs
    _ ≤ ∫ t, η*(q t*g t^2)+(1+1/η)*(q t*(f t-g t)^2) :=
      integral_mono (hf.sub hg).abs hi ha
    _ = _ := by rw [integral_add (hg.const_mul _) (hr.const_mul _),
        integral_const_mul, integral_const_mul]

end CopyQuantumMetrology.GradientBounds


