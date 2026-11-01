import FiniteCopy.GlobalBounds
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace CopyQuantumMetrology.GlobalBounds

noncomputable def correction (J m : ℝ) : ℝ :=
  (q J (m + 1 / 2) - q J (m - 1 / 2)) ^ 2 / 4

lemma correction_nonneg (J m : ℝ) : 0 ≤ correction J m := by
  unfold correction
  positivity

lemma correction_le_root_gap {J m : ℝ} (hB : 0 < J ^ 2 - m ^ 2) :
    correction J m ≤ (m ^ 2 + 1 / 16) / (J ^ 2 - m ^ 2) := by
  have hp := q_sub_sqrt_sq_le hB (m + 1 / 2)
  have hn := q_sub_sqrt_sq_le hB (m - 1 / 2)
  have hsum : ((m + 1 / 2) ^ 2 - m ^ 2) ^ 2 / (J ^ 2 - m ^ 2) +
      ((m - 1 / 2) ^ 2 - m ^ 2) ^ 2 / (J ^ 2 - m ^ 2) =
      2 * ((m ^ 2 + 1 / 16) / (J ^ 2 - m ^ 2)) := by ring
  unfold correction
  nlinarith [sq_nonneg (q J (m + 1 / 2) + q J (m - 1 / 2) -
    2 * Real.sqrt (J ^ 2 - m ^ 2))]

lemma correction_le_reciprocals {J m : ℝ} (hJ : 1 ≤ J)
    (hm : |m| ≤ J - 1 / 2) :
    correction J m ≤ J * (1 / (J + m) + 1 / (J - m)) := by
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  have hplus : 0 < J + m := by linarith
  have hminus : 0 < J - m := by linarith
  have hB : 0 < J ^ 2 - m ^ 2 := by nlinarith [mul_pos hplus hminus]
  calc
    _ ≤ (m ^ 2 + 1 / 16) / (J ^ 2 - m ^ 2) := correction_le_root_gap hB
    _ ≤ (2 * J ^ 2) / (J ^ 2 - m ^ 2) := by
      apply (div_le_div_iff_of_pos_right hB).2
      nlinarith [sq_nonneg (J - 1)]
    _ = _ := by
      field_simp
      <;> ring

-- n=2j 统一整数与半整数自旋；共有 n+1 个实际列。
noncomputable def spinJ (n : ℕ) : ℝ := ((n : ℝ) + 1) / 2
noncomputable def spinM (n i : ℕ) : ℝ := (i : ℝ) - n / 2

lemma spinM_abs_le {n i : ℕ} (hi : i ≤ n) :
    |spinM n i| ≤ spinJ n - 1 / 2 := by
  have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  apply abs_le.mpr
  dsimp [spinJ, spinM]
  constructor <;> linarith

lemma correction_spin_le {n i : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) :
    correction (spinJ n) (spinM n i) ≤
      2 * spinJ n * (1 / ((i : ℝ) + 1) + 1 / ((n - i : ℕ) + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hbase := correction_le_reciprocals
    (show 1 ≤ spinJ n by dsimp [spinJ]; linarith) (spinM_abs_le hi)
  have hleft : 1 / (spinJ n + spinM n i) ≤ 2 / ((i : ℝ) + 1) := by
    dsimp [spinJ, spinM]
    apply (div_le_div_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) i] : 0 < ((n : ℝ) + 1) / 2 + ((i : ℝ) - n / 2))
      (by positivity : 0 < (i : ℝ) + 1)).2
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hright : 1 / (spinJ n - spinM n i) ≤ 2 / ((n - i : ℕ) + 1) := by
    rw [Nat.cast_sub hi]
    dsimp [spinJ, spinM]
    apply (div_le_div_iff₀ (by linarith : 0 < ((n : ℝ) + 1) / 2 - ((i : ℝ) - n / 2))
      (by linarith : 0 < (n : ℝ) - i + 1)).2
    linarith
  calc
    _ ≤ spinJ n * (1 / (spinJ n + spinM n i) + 1 / (spinJ n - spinM n i)) := hbase
    _ ≤ spinJ n * (2 / ((i : ℝ) + 1) + 2 / ((n - i : ℕ) + 1)) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hleft hright)
      dsimp [spinJ]
      positivity
    _ = _ := by ring

theorem sum_correction_le_harmonic {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), correction (spinJ n) (spinM n i)) ≤
      4 * spinJ n * (harmonic (n + 1) : ℝ) := by
  have hreflect : (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / ((n - i : ℕ) + 1)) =
      ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / ((i : ℝ) + 1) := by
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
      Finset.sum_range_reflect (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) (n + 1)
  have hharm : (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / ((i : ℝ) + 1)) =
      (harmonic (n + 1) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one, one_div]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        2 * spinJ n * (1 / ((i : ℝ) + 1) + 1 / ((n - i : ℕ) + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact correction_spin_le hn (by simpa using Finset.mem_range.mp hi)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hreflect, hharm]
      ring

-- 除以实际维数 d=2J 后，离散修正至多 2(1+log d)。
theorem average_correction_le_log {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), correction (spinJ n) (spinM n i)) / (n + 1 : ℕ) ≤
      2 * (1 + Real.log (n + 1 : ℕ)) := by
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hnpos).2
  have hh := harmonic_le_one_add_log (n + 1)
  have hs := sum_correction_le_harmonic hn
  have hfac : 4 * spinJ n = 2 * ((n + 1 : ℕ) : ℝ) := by simp [spinJ]; ring
  rw [hfac] at hs
  have hmul := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 * (n + 1 : ℕ) by positivity)
  push_cast at *
  nlinarith

theorem sum_correction_le_log {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), correction (spinJ n) (spinM n i)) ≤
      4 * spinJ n * (1 + Real.log (n + 1 : ℕ)) := by
  have hs := sum_correction_le_harmonic hn
  have hh := harmonic_le_one_add_log (n + 1)
  have hJ : 0 ≤ 4 * spinJ n := by dsimp [spinJ]; positivity
  exact hs.trans (mul_le_mul_of_nonneg_left hh hJ)

-- 此量即 U/J 分解中离散修正的贡献。
theorem normalized_correction_le_log {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), correction (spinJ n) (spinM n i)) /
      ((n + 1 : ℕ) * spinJ n) ≤
        2 * (1 + Real.log (n + 1 : ℕ)) / spinJ n := by
  rw [← div_div]
  exact div_le_div_of_nonneg_right (average_correction_le_log hn)
    (by dsimp [spinJ]; positivity)

end CopyQuantumMetrology.GlobalBounds

