import Mathlib
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CopyQuantumMetrology.RateFunctional

/-- 正则化宽度。 -/
def width (ε x : ℝ) : ℝ := 1 / (2 * Real.sqrt (x ^ 2 + ε ^ 2))
/-- 正规化率密度。 -/
def density (ε x : ℝ) : ℝ := x ^ 2 * width ε x + 1 / (4 * width ε x)

theorem radicand_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 < x ^ 2 + ε ^ 2 := by
  positivity

theorem density_eq {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    density ε x = x ^ 2 / (2 * Real.sqrt (x ^ 2 + ε ^ 2)) +
      Real.sqrt (x ^ 2 + ε ^ 2) / 2 := by
  have hs : Real.sqrt (x ^ 2 + ε ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (radicand_pos hε x))
  unfold density width
  field_simp
  <;> ring

theorem continuous_density {ε : ℝ} (hε : 0 < ε) : Continuous (density ε) := by
  have hs : Continuous (fun x : ℝ => Real.sqrt (x ^ 2 + ε ^ 2)) :=
    (continuous_id.pow 2 |>.add continuous_const).sqrt
  have hn (x : ℝ) : 2 * Real.sqrt (x ^ 2 + ε ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 (radicand_pos hε x)))
  have he : density ε = fun x => x ^ 2 / (2 * Real.sqrt (x ^ 2 + ε ^ 2)) +
      Real.sqrt (x ^ 2 + ε ^ 2) / 2 := funext (density_eq hε)
  rw [he]
  exact ((continuous_id.pow 2).div (continuous_const.mul hs) hn).add (hs.div_const 2)

theorem hasDerivAt_primitive {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.sqrt (y ^ 2 + ε ^ 2) / 2) (density ε x) x := by
  have hs := (((hasDerivAt_id x).pow 2).add_const (ε ^ 2)).sqrt
    (ne_of_gt (radicand_pos hε x))
  have hd := ((hasDerivAt_id x).mul hs).div_const 2
  convert hd using 1 <;> simp [density_eq hε] <;> ring

/-- 直接用微积分基本定理计算实际区间积分。 -/
theorem regularized_rate_integral {ε : ℝ} (hε : 0 < ε) :
    (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, density ε x) =
      Real.sqrt (1 + ε ^ 2) / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_primitive hε x)
    ((continuous_density hε).intervalIntegrable (-1) 1)
  rw [h]
  norm_num
  ring

/-- d=2j+1 时的相邻网格分界点。 -/
def edge (d k : ℕ) : ℝ := -1 + 2 * k / d
/-- 自旋 m=-j+k 对应的 x=m/J，是等距网格的中点。 -/
def spinPoint (d k : ℕ) : ℝ := -1 + (2 * k + 1) / d
/-- 所有 d 个自旋列上的正规化和。 -/
def spinAverage (f : ℝ → ℝ) (d : ℕ) : ℝ :=
  (∑ k ∈ Finset.range d, f (spinPoint d k)) / d

theorem edge_length {d k : ℕ} : edge d (k + 1) - edge d k = 2 / d := by
  unfold edge
  push_cast
  ring

theorem edge_mono {d k : ℕ} : edge d k ≤ edge d (k + 1) := by
  have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  linarith [edge_length (d := d) (k := k)]

theorem edge_zero (d : ℕ) : edge d 0 = -1 := by simp [edge]
theorem edge_last {d : ℕ} (hd : 0 < d) : edge d d = 1 := by
  have h : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  norm_num [edge, h]

theorem cell_subset {d k : ℕ} (hd : 0 < d) (hk : k < d) :
    Set.uIcc (edge d k) (edge d (k + 1)) ⊆ Set.Icc (-1 : ℝ) 1 := by
  rw [uIcc_of_le edge_mono]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hk' : (k + 1 : ℝ) ≤ d := by exact_mod_cast hk
  intro x hx
  constructor
  · have : 0 ≤ 2 * (k : ℝ) / d := by positivity
    exact le_trans (by dsimp [edge]; linarith) hx.1
  · apply le_trans hx.2
    dsimp [edge]
    push_cast
    have : 2 * ((k : ℝ) + 1) / d ≤ 2 := (div_le_iff₀ hd').2 (by nlinarith)
    linarith

theorem spinPoint_in_cell {d k : ℕ} :
    spinPoint d k ∈ Set.Icc (edge d k) (edge d (k + 1)) := by
  have hd : (0 : ℝ) ≤ 1 / d := by positivity
  constructor <;> dsimp [spinPoint, edge] <;> push_cast <;> ring_nf at * <;> linarith





/-- 每个网格单元上的振荡控制给出平均误差；不假设黎曼和极限。 -/
theorem spinAverage_error_of_oscillation {f : ℝ → ℝ} {d : ℕ} {η : ℝ}
    (hd : 0 < d) (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hosc : ∀ k < d, ∀ x ∈ Set.uIcc (edge d k) (edge d (k + 1)),
      |f (spinPoint d k) - f x| ≤ η) :
    |spinAverage f d - (∫ x in (-1 : ℝ)..1, f x) / 2| ≤ η := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfi (k : ℕ) (hk : k < d) :
      IntervalIntegrable f volume (edge d k) (edge d (k + 1)) :=
    (hf.mono (cell_subset hd hk)).intervalIntegrable
  have hp := intervalIntegral.sum_integral_adjacent_intervals hfi
  rw [edge_zero, edge_last hd] at hp
  have he (k : ℕ) (hk : k < d) :
      |(2 / (d : ℝ)) * f (spinPoint d k) -
        ∫ x in edge d k..edge d (k + 1), f x| ≤ η * (2 / d) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := edge d k) (b := edge d (k + 1)) (C := η)
      (f := fun x => f (spinPoint d k) - f x)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hosc k hk x (uIoc_subset_uIcc hx))
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hfi k hk),
      intervalIntegral.integral_const, edge_length] at h
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (d : ℝ))] at h
    simpa only [Real.norm_eq_abs, smul_eq_mul] using h
  have ha : spinAverage f d - (∫ x in (-1 : ℝ)..1, f x) / 2 =
      (∑ k ∈ Finset.range d, ((2 / (d : ℝ)) * f (spinPoint d k) -
        ∫ x in edge d k..edge d (k + 1), f x)) / 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
    unfold spinAverage
    ring
  rw [ha, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    |∑ k ∈ Finset.range d, ((2 / (d : ℝ)) * f (spinPoint d k) -
      ∫ x in edge d k..edge d (k + 1), f x)|
      ≤ ∑ k ∈ Finset.range d, |(2 / (d : ℝ)) * f (spinPoint d k) -
        ∫ x in edge d k..edge d (k + 1), f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range d, η * (2 / (d : ℝ)) :=
      Finset.sum_le_sum (fun k hk => he k (Finset.mem_range.1 hk))
    _ = η * 2 := by simp; field_simp

/-- 连续函数在实际自旋网格上的黎曼和收敛，覆盖全部正整数维数。 -/
theorem spinAverage_tendsto {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    Tendsto (spinAverage f) atTop (𝓝 ((∫ x in (-1 : ℝ)..1, f x) / 2)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine ⟨max N 1, ?_⟩
  intro d hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hd)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hNd : (N : ℝ) ≤ d := by exact_mod_cast le_trans (le_max_left N 1) hd
  have hmesh : 2 / (d : ℝ) < δ := by
    apply (div_lt_iff₀ hd').2
    have := (div_lt_iff₀ hδ).1 hN
    nlinarith
  have he := spinAverage_error_of_oscillation hdpos hf (η := ε / 2) (by
    intro k hk x hx
    have hm := spinPoint_in_cell (d := d) (k := k)
    have hm' : spinPoint d k ∈ Set.uIcc (edge d k) (edge d (k + 1)) := by
      rwa [uIcc_of_le edge_mono]
    have hx' := hx
    rw [uIcc_of_le edge_mono] at hx'
    have hdistance : dist (spinPoint d k) x < δ := by
      rw [Real.dist_eq]
      have : |spinPoint d k - x| ≤ 2 / (d : ℝ) := by
        apply abs_le.2
        have hl := edge_length (d := d) (k := k)
        constructor <;> linarith [hm.1, hm.2, hx'.1, hx'.2]
      exact lt_of_le_of_lt this hmesh
    simpa only [Real.dist_eq] using
      (hu _ (cell_subset hdpos hk hm') _ (cell_subset hdpos hk hx) hdistance).le)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt he (by linarith)

/-- 固定正则化宽度的实际有限和收敛到精确率。 -/
theorem regularized_spinAverage_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (spinAverage (density ε)) atTop (𝓝 (Real.sqrt (1 + ε ^ 2) / 2)) := by
  have hi := regularized_rate_integral hε
  have ht := spinAverage_tendsto (continuous_density hε).continuousOn
  have hi' : (∫ x in (-1 : ℝ)..1, density ε x) / 2 = Real.sqrt (1 + ε ^ 2) / 2 := by linarith
  rwa [hi'] at ht




/-- 中点公式与物理自旋坐标 m/J 的直接一致性。 -/
theorem spinPoint_physical {d k : ℕ} (hd : 0 < d) :
    spinPoint d k = ((k : ℝ) - ((d : ℝ) - 1) / 2) / ((d : ℝ) / 2) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold spinPoint
  field_simp
  <;> ring

/-- n=2j、d=n+1 的整数和半整数自旋共用同一个极限。 -/
theorem half_integer_spinAverage_tendsto {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    Tendsto (fun n : ℕ => spinAverage f (n + 1)) atTop
      (𝓝 ((∫ x in (-1 : ℝ)..1, f x) / 2)) :=
  (spinAverage_tendsto hf).comp (tendsto_add_atTop_nat 1)

/-- 有限网格的定量黎曼和误差，Lipschitz 常数作为显式输入。 -/
theorem spinAverage_error_of_lipschitz {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hd : 0 < d) (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|) :
    |spinAverage f d - (∫ x in (-1 : ℝ)..1, f x) / 2| ≤ L / d := by
  apply spinAverage_error_of_oscillation hd hf
  intro k hk x hx
  have hm := spinPoint_in_cell (d := d) (k := k)
  have hm' : spinPoint d k ∈ Set.uIcc (edge d k) (edge d (k + 1)) := by
    rwa [uIcc_of_le edge_mono]
  have hx' := hx
  rw [uIcc_of_le edge_mono] at hx'
  have hdist : |spinPoint d k - x| ≤ 1 / (d : ℝ) := by
    apply abs_le.2
    have hleft : spinPoint d k - edge d k = 1 / (d : ℝ) := by
      unfold spinPoint edge
      ring
    have hright : edge d (k + 1) - spinPoint d k = 1 / (d : ℝ) := by
      unfold spinPoint edge
      push_cast
      ring
    constructor <;> linarith [hx'.1, hx'.2]
  calc
    |f (spinPoint d k) - f x| ≤ L * |spinPoint d k - x| :=
      hlip _ (cell_subset hd hk hm') _ (cell_subset hd hk hx)
    _ ≤ L * (1 / (d : ℝ)) := mul_le_mul_of_nonneg_left hdist hL
    _ = L / d := by ring

/-- 内区误差与坏列数量的有限求和接口。bad 的定义和局部能量界均为外部输入。 -/
theorem average_error_bulk_boundary {d : ℕ} {a : ℕ → ℝ} {f : ℝ → ℝ}
    (bad : Finset ℕ) {η B : ℝ} (hd : 0 < d) (hη : 0 ≤ η)
    (hgood : ∀ k < d, k ∉ bad → |a k - f (spinPoint d k)| ≤ η)
    (hbad : ∀ k < d, k ∈ bad → |a k - f (spinPoint d k)| ≤ B) :
    |(∑ k ∈ Finset.range d, a k) / d - spinAverage f d| ≤
      η + B * ((Finset.range d).filter (fun k => k ∈ bad)).card / d := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold spinAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hd']
  apply (div_le_iff₀ hd').2
  calc
    |∑ k ∈ Finset.range d, (a k - f (spinPoint d k))|
      ≤ ∑ k ∈ Finset.range d, |a k - f (spinPoint d k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range d, (η + if k ∈ bad then B else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hb : k ∈ bad
      · simp only [hb, ite_true]
        exact le_trans (hbad k (Finset.mem_range.1 hk) hb) (le_add_of_nonneg_left hη)
      · simpa only [hb, ite_false, add_zero] using hgood k (Finset.mem_range.1 hk) hb
    _ = (η + B * ((Finset.range d).filter (fun k => k ∈ bad)).card / (d : ℝ)) * d := by
      simp [Finset.sum_add_distrib, Finset.filter_mem_eq_inter]
      field_simp
      <;> ring

/-- 将局部能量误差、边界列数量和实际积分连成一个有限维估计。 -/
theorem rate_error_bulk_boundary {d : ℕ} {a : ℕ → ℝ} {f : ℝ → ℝ}
    (bad : Finset ℕ) {η B L : ℝ} (hd : 0 < d) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |f x - f y| ≤ L * |x - y|)
    (hgood : ∀ k < d, k ∉ bad → |a k - f (spinPoint d k)| ≤ η)
    (hbad : ∀ k < d, k ∈ bad → |a k - f (spinPoint d k)| ≤ B) :
    |(∑ k ∈ Finset.range d, a k) / d - (∫ x in (-1 : ℝ)..1, f x) / 2| ≤
      η + B * ((Finset.range d).filter (fun k => k ∈ bad)).card / d + L / d := by
  calc
    _ ≤ |(∑ k ∈ Finset.range d, a k) / d - spinAverage f d| +
        |spinAverage f d - (∫ x in (-1 : ℝ)..1, f x) / 2| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (average_error_bulk_boundary bad hd hη hgood hbad)
      (spinAverage_error_of_lipschitz hd hf hL hlip)

/-- 密度的导数使用显式有理式，便于同时控制全部正则化参数。 -/
def densityDerivative (ε x : ℝ) : ℝ :=
  (x / Real.sqrt (x ^ 2 + ε ^ 2)) * (1 + ε ^ 2 / (2 * (x ^ 2 + ε ^ 2)))

theorem hasDerivAt_density {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (density ε) (densityDerivative ε x) x := by
  have hr := radicand_pos hε x
  have hspos := Real.sqrt_pos.2 hr
  have hsq := Real.sq_sqrt hr.le
  have hs := (((hasDerivAt_id x).pow 2).add_const (ε ^ 2)).sqrt (ne_of_gt hr)
  have hd := (((hasDerivAt_id x).pow 2).div (hs.const_mul 2)
    (mul_ne_zero (by norm_num) (ne_of_gt hspos))).add (hs.div_const 2)
  have he : density ε = fun y => y ^ 2 / (2 * Real.sqrt (y ^ 2 + ε ^ 2)) +
      Real.sqrt (y ^ 2 + ε ^ 2) / 2 := funext (density_eq hε)
  rw [he]
  convert hd using 1
  · rfl
  · dsimp [densityDerivative]
    field_simp [ne_of_gt hspos, ne_of_gt hr]
    rw [hsq]
    ring

/-- 比一般 ε⁻³ 界更强：实际率密度的 Lipschitz 常数统一为 3/2。 -/
theorem abs_densityDerivative_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |densityDerivative ε x| ≤ 3 / 2 := by
  have hr := radicand_pos hε x
  have hspos := Real.sqrt_pos.2 hr
  have hsq := Real.sq_sqrt hr.le
  have hx : |x| ≤ Real.sqrt (x ^ 2 + ε ^ 2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg ε]
  have hxdiv : |x / Real.sqrt (x ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_one hspos).2 hx
  have he0 : 0 ≤ ε ^ 2 / (2 * (x ^ 2 + ε ^ 2)) := by positivity
  have he1 : ε ^ 2 / (2 * (x ^ 2 + ε ^ 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (x ^ 2 + ε ^ 2))).2
    nlinarith [sq_nonneg x]
  unfold densityDerivative
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + ε ^ 2 / (2 * (x ^ 2 + ε ^ 2)))]
  nlinarith [abs_nonneg (x / Real.sqrt (x ^ 2 + ε ^ 2))]

theorem density_lipschitz {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |density ε x - density ε y| ≤ (3 / 2 : ℝ) * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := density ε) (f' := densityDerivative ε)
    (fun z _ => (hasDerivAt_density hε z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using abs_densityDerivative_le hε z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- 显式密度的有限维误差，不把积分值或黎曼和极限当作前提。 -/
theorem regularized_spinAverage_error {ε : ℝ} {d : ℕ} (hε : 0 < ε) (hd : 0 < d) :
    |spinAverage (density ε) d - Real.sqrt (1 + ε ^ 2) / 2| ≤ 3 / (2 * d) := by
  have h := spinAverage_error_of_lipschitz hd (continuous_density hε).continuousOn
    (L := 3 / 2) (by norm_num) (fun x _ y _ => density_lipschitz hε x y)
  have hi := regularized_rate_integral hε
  have hi' : (∫ x in (-1 : ℝ)..1, density ε x) / 2 = Real.sqrt (1 + ε ^ 2) / 2 := by
    linarith
  rw [hi'] at h
  convert h using 1 <;> ring

theorem density_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ density ε x := by
  rw [density_eq hε]
  positivity

/-- 正则化参数至多 1 时，目标密度在整个积分区间上被绝对常数 2 控制。 -/
theorem density_le_two {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : density ε x ≤ 2 := by
  have hr := radicand_pos hε x
  have hspos := Real.sqrt_pos.2 hr
  have hsq := Real.sq_sqrt hr.le
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hesq : ε ^ 2 ≤ 1 := by nlinarith
  have hsle : Real.sqrt (x ^ 2 + ε ^ 2) ≤ 2 := by nlinarith
  have hfrac : x ^ 2 / (2 * Real.sqrt (x ^ 2 + ε ^ 2)) ≤
      Real.sqrt (x ^ 2 + ε ^ 2) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (x ^ 2 + ε ^ 2))).2
    nlinarith [sq_nonneg ε]
  rw [density_eq hε]
  linarith

/-- 从任意中点和删去若干列时的确切计数误差接口。 -/
theorem spinAverage_delete_error {f : ℝ → ℝ} {d : ℕ} (bad : Finset ℕ)
    {M : ℝ} (hd : 0 < d)
    (hM : ∀ k < d, k ∈ bad → |f (spinPoint d k)| ≤ M) :
    |(∑ k ∈ (Finset.range d).filter (fun k => k ∉ bad), f (spinPoint d k)) / d -
      spinAverage f d| ≤ M * ((Finset.range d).filter (fun k => k ∈ bad)).card / d := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have he := Finset.sum_filter_add_sum_filter_not (Finset.range d)
    (fun k => k ∈ bad) (fun k => f (spinPoint d k))
  unfold spinAverage
  rw [← sub_div, abs_div, abs_of_pos hd']
  apply (div_le_div_iff_of_pos_right hd').2
  have hdif : (∑ k ∈ (Finset.range d).filter (fun k => k ∉ bad), f (spinPoint d k)) -
      ∑ k ∈ Finset.range d, f (spinPoint d k) =
      -(∑ k ∈ (Finset.range d).filter (fun k => k ∈ bad), f (spinPoint d k)) := by
    linarith [he]
  rw [hdif, abs_neg]
  calc
    _ ≤ ∑ k ∈ (Finset.range d).filter (fun k => k ∈ bad), |f (spinPoint d k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ (Finset.range d).filter (fun k => k ∈ bad), M :=
      Finset.sum_le_sum (fun k hk => hM k (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
        (Finset.mem_filter.1 hk).2)
    _ = _ := by simp; ring

/-- 真实正则化密度的删点和与完整积分之间的统一参数估计。 -/
theorem regularized_deleted_spinAverage_error {ε : ℝ} {d : ℕ}
    (bad : Finset ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d) :
    |(∑ k ∈ (Finset.range d).filter (fun k => k ∉ bad), density ε (spinPoint d k)) / d -
      Real.sqrt (1 + ε ^ 2) / 2| ≤
      2 * ((Finset.range d).filter (fun k => k ∈ bad)).card / d + 3 / (2 * d) := by
  have hm (k : ℕ) (hk : k < d) : spinPoint d k ∈ Set.Icc (-1 : ℝ) 1 := by
    apply cell_subset hd hk
    simpa only [uIcc_of_le edge_mono] using spinPoint_in_cell (d := d) (k := k)
  calc
    _ ≤ |(∑ k ∈ (Finset.range d).filter (fun k => k ∉ bad), density ε (spinPoint d k)) / d -
        spinAverage (density ε) d| +
        |spinAverage (density ε) d - Real.sqrt (1 + ε ^ 2) / 2| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (spinAverage_delete_error bad hd (fun k hk _ => by
      rw [abs_of_nonneg (density_nonneg hε _)]
      exact density_le_two hε hε1 (hm k hk))) (regularized_spinAverage_error hε hd)

end CopyQuantumMetrology.RateFunctional
