import FiniteCopy.RateFunctional

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CopyQuantumMetrology.RateFunctional

/-- 位置项和梯度项分别对应的目标密度。 -/
def positionProfile (ε x : ℝ) : ℝ := x ^ 2 * width ε x
def gradientProfile (ε x : ℝ) : ℝ := 1 / (4 * width ε x)

theorem profile_sum (ε x : ℝ) :
    positionProfile ε x + gradientProfile ε x = density ε x := rfl

theorem positionProfile_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ positionProfile ε x := by unfold positionProfile width; positivity

theorem gradientProfile_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ gradientProfile ε x := by unfold gradientProfile width; positivity

theorem positionProfile_le_two {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) : positionProfile ε x ≤ 2 := by
  have := density_le_two hε hε1 hx
  rw [← profile_sum] at this
  linarith [gradientProfile_nonneg hε x]

theorem gradientProfile_le_two {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) : gradientProfile ε x ≤ 2 := by
  have := density_le_two hε hε1 hx
  rw [← profile_sum] at this
  linarith [positionProfile_nonneg hε x]

theorem position_error_of_global_bound {ε x A B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) (hA : |A| ≤ B) :
    |A - positionProfile ε x| ≤ B + 2 := by
  calc
    _ ≤ |A| + |positionProfile ε x| := abs_sub _ _
    _ ≤ B + 2 := by
      rw [abs_of_nonneg (positionProfile_nonneg hε x)]
      exact add_le_add hA (positionProfile_le_two hε hε1 hx)

theorem gradient_error_of_global_bound {ε x A B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) (hA : |A| ≤ B) :
    |A - gradientProfile ε x| ≤ B + 2 := by
  calc
    _ ≤ |A| + |gradientProfile ε x| := abs_sub _ _
    _ ≤ B + 2 := by
      rw [abs_of_nonneg (gradientProfile_nonneg hε x)]
      exact add_le_add hA (gradientProfile_le_two hε hε1 hx)

/-- 与 U=(ΣI+ΣG+ΣR)/d 的归一化一致；边和只含 d-1 项。 -/
theorem raw_energy_normalize (d : ℕ) (J : ℝ) (I G R : ℕ → ℝ) :
    (((∑ k ∈ Finset.range d, I k) + (∑ k ∈ Finset.range (d - 1), G k) +
      (∑ k ∈ Finset.range d, R k)) / d) / J =
    ((∑ k ∈ Finset.range d, I k / J) + (∑ k ∈ Finset.range (d - 1), G k / J)) / d +
      (∑ k ∈ Finset.range d, R k) / (d * J) := by
  rw [← Finset.sum_div, ← Finset.sum_div]
  ring

/-- 允许 n=0 的有限和误差；坏列与坏边可分别选取和计数。 -/
theorem sum_error_bulk_boundary {n : ℕ} {a b : ℕ → ℝ}
    (bad : Finset ℕ) {η B : ℝ} (hη : 0 ≤ η)
    (hgood : ∀ k < n, k ∉ bad → |a k - b k| ≤ η)
    (hbad : ∀ k < n, k ∈ bad → |a k - b k| ≤ B) :
    |(∑ k ∈ Finset.range n, a k) - ∑ k ∈ Finset.range n, b k| ≤
      η * n + B * ((Finset.range n).filter (fun k => k ∈ bad)).card := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |a k - b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (η + if k ∈ bad then B else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hb : k ∈ bad
      · simp only [hb, ite_true]
        exact (hbad k (Finset.mem_range.1 hk) hb).trans (le_add_of_nonneg_left hη)
      · simpa only [hb, ite_false, add_zero] using hgood k (Finset.mem_range.1 hk) hb
    _ = _ := by simp [Finset.sum_add_distrib, Finset.filter_mem_eq_inter]; ring

theorem partial_average_error {n d : ℕ} {a b : ℕ → ℝ}
    (bad : Finset ℕ) {η B : ℝ} (hd : 0 < d) (hn : n ≤ d) (hη : 0 ≤ η)
    (hgood : ∀ k < n, k ∉ bad → |a k - b k| ≤ η)
    (hbad : ∀ k < n, k ∈ bad → |a k - b k| ≤ B) :
    |(∑ k ∈ Finset.range n, a k) / d - (∑ k ∈ Finset.range n, b k) / d| ≤
      η + B * ((Finset.range n).filter (fun k => k ∈ bad)).card / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (n : ℝ) ≤ d := by exact_mod_cast hn
  rw [← sub_div, abs_div, abs_of_pos hd']
  apply (div_le_iff₀ hd').2
  calc
    _ ≤ η * n + B * ((Finset.range n).filter (fun k => k ∈ bad)).card :=
      sum_error_bulk_boundary bad hη hgood hbad
    _ ≤ η * d + B * ((Finset.range n).filter (fun k => k ∈ bad)).card := by gcongr
    _ = _ := by field_simp

/-- d 个位置目标加 d-1 个梯度目标，只差最右侧的一个梯度目标。 -/
theorem profile_sum_missing_last {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    (∑ k ∈ Finset.range d, density ε (spinPoint d k)) =
      (∑ k ∈ Finset.range d, positionProfile ε (spinPoint d k)) +
      (∑ k ∈ Finset.range (d - 1), gradientProfile ε (spinPoint d k)) +
      gradientProfile ε (spinPoint d (d - 1)) := by
  simp_rw [← profile_sum]
  rw [Finset.sum_add_distrib]
  rcases d with _ | n
  · omega
  · simp only [Nat.add_sub_cancel, Finset.sum_range_succ]
    ring

/-- 真实列数 d 与真实边数 d-1 的汇总接口。I、G 已除以 J，r 是归一化离散修正。
    局部能量界仍须由调用方对实际高斯积分证明；这里不把它们当作已证明的物理结论。 -/
theorem regularized_energy_error {d : ℕ} {ε : ℝ} {I G : ℕ → ℝ} {r : ℝ}
    (badI badG : Finset ℕ) {ηI ηG BI BG R : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hηI : 0 ≤ ηI) (hηG : 0 ≤ ηG)
    (hIgood : ∀ k < d, k ∉ badI →
      |I k - positionProfile ε (spinPoint d k)| ≤ ηI)
    (hIbad : ∀ k < d, k ∈ badI →
      |I k - positionProfile ε (spinPoint d k)| ≤ BI)
    (hGgood : ∀ k < d - 1, k ∉ badG →
      |G k - gradientProfile ε (spinPoint d k)| ≤ ηG)
    (hGbad : ∀ k < d - 1, k ∈ badG →
      |G k - gradientProfile ε (spinPoint d k)| ≤ BG)
    (hr : |r| ≤ R) :
    |((∑ k ∈ Finset.range d, I k) + (∑ k ∈ Finset.range (d - 1), G k)) / d + r -
      Real.sqrt (1 + ε ^ 2) / 2| ≤
      ηI + ηG + BI * ((Finset.range d).filter (fun k => k ∈ badI)).card / d +
      BG * ((Finset.range (d - 1)).filter (fun k => k ∈ badG)).card / d +
      2 / d + 3 / (2 * d) + R := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hi := partial_average_error badI hd (le_refl d) hηI hIgood hIbad
  have hg := partial_average_error badG hd (Nat.sub_le d 1) hηG hGgood hGbad
  have hp := profile_sum_missing_last hd ε
  have hk : d - 1 < d := Nat.sub_lt hd (by omega)
  have hx : spinPoint d (d - 1) ∈ Icc (-1 : ℝ) 1 := by
    apply cell_subset hd hk
    simpa only [uIcc_of_le edge_mono] using spinPoint_in_cell (d := d) (k := d - 1)
  have hlast : |gradientProfile ε (spinPoint d (d - 1)) / d| ≤ 2 / d := by
    rw [abs_of_nonneg (div_nonneg (gradientProfile_nonneg hε _) hd'.le)]
    exact div_le_div_of_nonneg_right (gradientProfile_le_two hε hε1 hx) hd'.le
  have heq :
      ((∑ k ∈ Finset.range d, I k) + (∑ k ∈ Finset.range (d - 1), G k)) / d + r -
        Real.sqrt (1 + ε ^ 2) / 2 =
      ((∑ k ∈ Finset.range d, I k) / d -
        (∑ k ∈ Finset.range d, positionProfile ε (spinPoint d k)) / d) +
      ((∑ k ∈ Finset.range (d - 1), G k) / d -
        (∑ k ∈ Finset.range (d - 1), gradientProfile ε (spinPoint d k)) / d) -
      gradientProfile ε (spinPoint d (d - 1)) / d +
      (spinAverage (density ε) d - Real.sqrt (1 + ε ^ 2) / 2) + r := by
    unfold spinAverage
    rw [hp]
    ring
  rw [heq]
  calc
    _ ≤ (|((∑ k ∈ Finset.range d, I k) / d -
          (∑ k ∈ Finset.range d, positionProfile ε (spinPoint d k)) / d)| +
        |((∑ k ∈ Finset.range (d - 1), G k) / d -
          (∑ k ∈ Finset.range (d - 1), gradientProfile ε (spinPoint d k)) / d)|) +
        |gradientProfile ε (spinPoint d (d - 1)) / d| +
        |spinAverage (density ε) d - Real.sqrt (1 + ε ^ 2) / 2| + |r| := by
      grw [abs_add_le, abs_add_le, abs_sub, abs_add_le]
    _ ≤ _ := by linarith [regularized_spinAverage_error hε hd]

/-- 任意趋零的正参数序列都适用；无需先固定 ε 再作对角选择。 -/
theorem variable_regularization_tendsto {E : ℕ → ℝ}
    (hE : ∀ n, 0 < E n) (hE0 : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun n => spinAverage (density (E n)) (n + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmesh : Tendsto (fun n : ℕ => 3 / (2 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 / 2) using 1
    · ext n
      push_cast
      field_simp
      <;> ring
    · norm_num
  have herr : Tendsto (fun n => spinAverage (density (E n)) (n + 1) -
      Real.sqrt (1 + E n ^ 2) / 2) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun n => regularized_spinAverage_error (hE n) (Nat.succ_pos n)) hmesh
  have hrate : Tendsto (fun n => Real.sqrt (1 + E n ^ 2) / 2) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add (hE0.pow 2)).sqrt).div_const 2
  simpa only [sub_add_cancel, zero_add] using herr.add hrate

end CopyQuantumMetrology.RateFunctional

