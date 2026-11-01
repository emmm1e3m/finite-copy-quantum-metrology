import Mathlib

open Filter Topology

namespace CopyQuantumMetrology

/-- 显式宽度规则中的对数。 -/
noncomputable def widthLog (J : ℝ) : ℝ := Real.log (Real.exp 1 + J)

/-- 测量参数；端点截断仅出现在证明中。 -/
noncomputable def epsilon (J : ℝ) : ℝ := (widthLog J)⁻¹
noncomputable def delta (J : ℝ) : ℝ := epsilon J ^ 8

lemma widthLog_pos {J : ℝ} (hJ : 0 ≤ J) : 0 < widthLog J := by
  apply Real.log_pos
  have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
  linarith

lemma widthLog_atTop : Tendsto widthLog atTop atTop := by
  exact Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_id)

lemma epsilon_pos {J : ℝ} (hJ : 0 ≤ J) : 0 < epsilon J :=
  inv_pos.mpr (widthLog_pos hJ)

lemma epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) :=
  widthLog_atTop.inv_tendsto_atTop

lemma delta_tendsto_zero : Tendsto delta atTop (𝓝 0) := by
  change Tendsto (fun J : ℝ => epsilon J ^ 8) atTop (𝓝 0)
  simpa using epsilon_tendsto_zero.pow 8

/-- 任意固定对数幂均被线性尺度支配，包含平移常数 exp(1)。 -/
lemma log_pow_div_tendsto_zero (n : ℕ) :
    Tendsto (fun J : ℝ => widthLog J ^ n / J) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.exp 1) n one_ne_zero).comp
    (tendsto_const_nhds.add_atTop tendsto_id :
      Tendsto (fun J : ℝ => Real.exp 1 + J) atTop atTop)
  simpa [widthLog, Function.comp_def, add_comm, add_left_comm, add_assoc] using h

/-- 对平方后的极限取平方根，避免引入非整数指数记号。 -/
lemma log_pow_div_sqrt_tendsto_zero (n : ℕ) :
    Tendsto (fun J : ℝ => widthLog J ^ n / Real.sqrt J) atTop (𝓝 0) := by
  have h := (log_pow_div_tendsto_zero (n * 2)).sqrt
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with J hJ
  rw [pow_mul, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg (le_of_lt (widthLog_pos hJ)) n)]

/-- 多项式因子乘以 exp(-c sqrt J) 的极限。 -/
lemma square_exp_sqrt_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun J : ℝ => J ^ 2 * Real.exp (-c * Real.sqrt J)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) c hc).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with J hJ
  dsimp only [Function.comp_def]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 1
  calc
    Real.sqrt J ^ 4 = (Real.sqrt J ^ 2) ^ 2 := by ring
    _ = J ^ 2 := by rw [Real.sq_sqrt hJ]




/-- 高斯尾误差的实际指数项趋零。 -/
lemma logarithmic_tail_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun J : ℝ => widthLog J ^ 26 * J *
      Real.exp (-(c * J / widthLog J ^ 17))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with J hJ
    exact mul_nonneg (mul_nonneg (pow_nonneg (widthLog_pos hJ).le _) hJ)
      (Real.exp_nonneg _)
  · have h26 := (tendsto_order.1 (log_pow_div_tendsto_zero 26)).2 1 zero_lt_one
    have h17 := (tendsto_order.1 (log_pow_div_sqrt_tendsto_zero 17)).2 1 zero_lt_one
    filter_upwards [h26, h17, eventually_gt_atTop (0 : ℝ)] with J h26 h17 hJ
    have hL : 0 < widthLog J := widthLog_pos hJ.le
    have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
    have hp26 : widthLog J ^ 26 ≤ J := (div_lt_one hJ).mp h26 |>.le
    have hp17 : widthLog J ^ 17 ≤ Real.sqrt J := (div_lt_one hs).mp h17 |>.le
    have hsq := Real.sq_sqrt hJ.le
    have hx : Real.sqrt J ≤ J / widthLog J ^ 17 := by
      apply (le_div_iff₀ (pow_pos hL _)).2
      nlinarith [mul_le_mul_of_nonneg_left hp17 hs.le]
    have he : Real.exp (-(c * J / widthLog J ^ 17)) ≤
        Real.exp (-c * Real.sqrt J) := by
      apply Real.exp_le_exp.mpr
      rw [mul_div_assoc]
      nlinarith
    have hm : widthLog J ^ 26 * J ≤ J ^ 2 := by nlinarith
    exact mul_le_mul hm he (Real.exp_nonneg _) (sq_nonneg J)
  · exact square_exp_sqrt_tendsto_zero c hc

/-- 显式截止参数所需的增长条件。 -/
lemma div_log_pow_atTop (n : ℕ) :
    Tendsto (fun J : ℝ => J / widthLog J ^ n) atTop atTop := by
  have h : Tendsto (fun J : ℝ => widthLog J ^ n / J) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact log_pow_div_tendsto_zero n
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with J hJ
      exact div_pos (pow_pos (widthLog_pos hJ.le) _) hJ
  have hi := h.inv_tendsto_nhdsGT_zero
  change Tendsto (fun J : ℝ => (widthLog J ^ n / J)⁻¹) atTop atTop at hi
  simpa only [inv_div] using hi

lemma delta_growth_atTop : Tendsto (fun J : ℝ => J * delta J) atTop atTop := by
  simpa only [delta, epsilon, inv_pow, div_eq_mul_inv] using div_log_pow_atTop 8

lemma tail_scale_atTop :
    Tendsto (fun J : ℝ => J * epsilon J * delta J ^ 2) atTop atTop := by
  have heq : (fun J : ℝ => J * epsilon J * delta J ^ 2) =
      (fun J : ℝ => J / widthLog J ^ 17) := by
    funext J
    simp only [delta, epsilon, ← pow_mul, inv_pow, div_eq_mul_inv]
    ring
  rw [heq]
  exact div_log_pow_atTop 17

lemma eventually_admissible : ∀ᶠ J : ℝ in atTop,
    0 < epsilon J ∧ epsilon J ≤ 1 ∧ 0 < delta J ∧ delta J < 1/2 ∧
      2 ≤ J * delta J ∧ 1 ≤ J * epsilon J * delta J ^ 2 := by
  have he := (tendsto_order.1 epsilon_tendsto_zero).2 1 zero_lt_one
  have hd := (tendsto_order.1 delta_tendsto_zero).2 (1/2) (by norm_num)
  filter_upwards [eventually_ge_atTop (0 : ℝ), he, hd,
    delta_growth_atTop.eventually_ge_atTop 2, tail_scale_atTop.eventually_ge_atTop 1]
    with J hJ he hd hg ht
  exact ⟨epsilon_pos hJ, he.le, pow_pos (epsilon_pos hJ) 8, hd, hg, ht⟩

/-- 代入显式参数后的统一误差。 -/
noncomputable def explicitError (C c J : ℝ) : ℝ :=
  C * ((widthLog J)⁻¹ + widthLog J ^ 7 / J +
    widthLog J ^ 44 / Real.sqrt J +
    widthLog J ^ 26 * J * Real.exp (-(c * J / widthLog J ^ 17)) +
    Real.log (2 + J) / J)

lemma shifted_log_div_tendsto_zero :
    Tendsto (fun J : ℝ => Real.log (2 + J) / J) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
    (tendsto_const_nhds.add_atTop tendsto_id :
      Tendsto (fun J : ℝ => 2 + J) atTop atTop)
  simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using h

lemma explicitError_tendsto_zero (C c : ℝ) (hc : 0 < c) :
    Tendsto (explicitError C c) atTop (𝓝 0) := by
  have h := ((((epsilon_tendsto_zero.add (log_pow_div_tendsto_zero 7)).add
    (log_pow_div_sqrt_tendsto_zero 44)).add (logarithmic_tail_tendsto_zero c hc)).add
    shifted_log_div_tendsto_zero).const_mul C
  unfold explicitError
  simpa only [epsilon, add_zero, mul_zero] using h



/-- 论文统一界的原始形式，eps 与 cutoff 可独立变化。 -/
noncomputable def uniformError (C c J eps cutoff : ℝ) : ℝ :=
  C * ((eps⁻¹)^7 * (cutoff + J⁻¹) +
    (eps⁻¹)^12 * (cutoff⁻¹)^4 / Real.sqrt J +
    (eps⁻¹)^2 * (cutoff⁻¹)^3 * J * Real.exp (-(c * J * eps * cutoff^2)) +
    Real.log (2+J) / J)

lemma uniformError_substitution {J : ℝ} (hJ : 0 < J) (C c : ℝ) :
    uniformError C c J (epsilon J) (delta J) = explicitError C c J := by
  have hL : widthLog J ≠ 0 := ne_of_gt (widthLog_pos hJ.le)
  have hS : Real.sqrt J ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hJ)
  have he : c * J * epsilon J * delta J ^ 2 = c * J / widthLog J ^ 17 := by
    dsimp [epsilon, delta]
    field_simp
  unfold uniformError explicitError
  rw [he]
  simp only [epsilon, delta, inv_pow, inv_inv, ← pow_mul]
  congr 1
  field_simp
  ring

lemma regularized_target_tendsto :
    Tendsto (fun J : ℝ => Real.sqrt (1 + epsilon J ^ 2) / 2) atTop (𝓝 (1/2)) := by
  have h := (((epsilon_tendsto_zero.pow 2).const_add 1).sqrt).div_const 2
  simpa using h

/-- 收尾接口：实际能量必须先独立满足统一误差界。 -/
theorem energy_limit_of_uniform_bound (U : ℝ → ℝ) (C c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ J : ℝ in atTop,
      |U J / J - Real.sqrt (1 + epsilon J ^ 2) / 2| ≤
        uniformError C c J (epsilon J) (delta J)) :
    Tendsto (fun J : ℝ => U J / J) atTop (𝓝 (1/2)) := by
  have hb : ∀ᶠ J : ℝ in atTop,
      |U J / J - Real.sqrt (1 + epsilon J ^ 2) / 2| ≤ explicitError C c J := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with J hb hJ
    simpa only [uniformError_substitution hJ] using hb
  have ha := squeeze_zero' (Eventually.of_forall (fun J : ℝ =>
    abs_nonneg (U J / J - Real.sqrt (1 + epsilon J ^ 2) / 2))) hb
    (explicitError_tendsto_zero C c hc)
  have hd : Tendsto (fun J : ℝ => U J / J - Real.sqrt (1 + epsilon J ^ 2) / 2)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using ha
  have hh := hd.add regularized_target_tendsto
  simpa only [sub_add_cancel, zero_add] using hh




/-- 任意索引序列的版本，适用于整数与半整数自旋。 -/
theorem energy_limit_along_of_uniform_bound {α : Type*} {l : Filter α}
    (U J : α → ℝ) (hJ : Tendsto J l atTop) (C c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ a in l,
      |U a / J a - Real.sqrt (1 + epsilon (J a) ^ 2) / 2| ≤
        uniformError C c (J a) (epsilon (J a)) (delta (J a))) :
    Tendsto (fun a => U a / J a) l (𝓝 (1/2)) := by
  have hb : ∀ᶠ a in l,
      |U a / J a - Real.sqrt (1 + epsilon (J a) ^ 2) / 2| ≤ explicitError C c (J a) := by
    filter_upwards [hbound, hJ.eventually (eventually_gt_atTop (0 : ℝ))] with a hb ha
    simpa only [uniformError_substitution ha] using hb
  have he := (explicitError_tendsto_zero C c hc).comp hJ
  have ha := squeeze_zero' (Eventually.of_forall (fun a =>
    abs_nonneg (U a / J a - Real.sqrt (1 + epsilon (J a) ^ 2) / 2))) hb he
  have hd : Tendsto (fun a => U a / J a - Real.sqrt (1 + epsilon (J a) ^ 2) / 2)
      l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using ha
  have hh := hd.add (regularized_target_tendsto.comp hJ)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hh

lemma scale_ratio_tendsto_one :
    Tendsto (fun J : ℝ => J / (J - 1/2)) atTop (𝓝 1) := by
  have hden : Tendsto (fun J : ℝ => J - 1/2) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-(1/2 : ℝ))
      (tendsto_id : Tendsto (fun J : ℝ => J) atTop atTop)
  have hz : Tendsto (fun J : ℝ => (1/2 : ℝ) / (J - 1/2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hh := hz.const_add 1
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1/2 : ℝ)] with J hJ
  have hn : J - 1/2 ≠ 0 := ne_of_gt (sub_pos.mpr hJ)
  calc
    1 + (1/2)/(J-1/2) = ((J-1/2)+(1/2))/(J-1/2) := by rw [add_div, div_self hn]
    _ = J/(J-1/2) := by rw [sub_add_cancel]

/-- 将归一化尺度 J 改回论文中的 j=J-1/2。 -/
theorem energy_limit_spin_of_uniform_bound {α : Type*} {l : Filter α}
    (U J : α → ℝ) (hJ : Tendsto J l atTop) (C c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ a in l,
      |U a / J a - Real.sqrt (1 + epsilon (J a) ^ 2) / 2| ≤
        uniformError C c (J a) (epsilon (J a)) (delta (J a))) :
    Tendsto (fun a => U a / (J a - 1/2)) l (𝓝 (1/2)) := by
  have hu := energy_limit_along_of_uniform_bound U J hJ C c hc hbound
  have hh := hu.mul (scale_ratio_tendsto_one.comp hJ)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [hJ.eventually (eventually_gt_atTop (0 : ℝ))] with a ha
  dsimp only [Function.comp_apply]
  exact div_mul_div_cancel₀ (ne_of_gt ha)

/-- n=2j，n+1 为自旋空间维数。 -/
noncomputable def spinScale (n : ℕ) : ℝ := ((n : ℝ) + 1) / 2

lemma spinScale_atTop : Tendsto spinScale atTop atTop := by
  unfold spinScale
  exact (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
    (by norm_num : (0 : ℝ) < 2)

theorem half_integer_energy_limit_of_uniform_bound (U : ℕ → ℝ) (C c : ℝ) (hc : 0 < c)
    (hbound : ∀ᶠ n : ℕ in atTop,
      |U n / spinScale n - Real.sqrt (1 + epsilon (spinScale n) ^ 2) / 2| ≤
        uniformError C c (spinScale n) (epsilon (spinScale n)) (delta (spinScale n))) :
    Tendsto (fun n : ℕ => U n / ((n : ℝ) / 2)) atTop (𝓝 (1/2)) := by
  have h := energy_limit_spin_of_uniform_bound U spinScale spinScale_atTop C c hc hbound
  convert h using 1
  funext n
  unfold spinScale
  congr 1
  ring

end CopyQuantumMetrology


