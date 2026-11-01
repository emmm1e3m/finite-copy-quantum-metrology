import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

open scoped BigOperators
open Complex

noncomputable section
namespace CopyQuantumMetrology.PhaseMoments

variable {L : ℕ} [NeZero L]

-- 标准有限指标嵌入；维度不超过相位数时没有频率混叠。
omit [NeZero L] in
theorem fin_zmod_injective {d : ℕ} (hd : d ≤ L) :
    Function.Injective (fun i : Fin d => (i.val : ZMod L)) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hd),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hd)] using hv

omit [NeZero L] in
theorem fin_neg_zmod_injective {d : ℕ} (hd : d ≤ L) :
    Function.Injective (fun i : Fin d => -(i.val : ZMod L)) := by
  intro i j hij
  exact fin_zmod_injective hd (neg_injective hij)

def cx (k : ZMod L) : ℝ := (ZMod.stdAddChar k).re
def cy (k : ZMod L) : ℝ := (ZMod.stdAddChar k).im
def angle (k : ZMod L) : ℝ := 2 * Real.pi * (k.val / L)

-- 这里的实、虚部确实是论文中均匀网格上的 cos 与 sin。
theorem character_exp (k : ZMod L) :
    ZMod.stdAddChar k = Complex.exp ((angle k : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  rfl

theorem character_frequency_exp (k : ZMod L) (m : ℤ) :
    ZMod.stdAddChar ((m : ZMod L) * k) =
      Complex.exp ((m : ℂ) * (angle k : ℂ) * Complex.I) := by
  have hm : ((m * (k.val : ℤ) : ℤ) : ZMod L) = (m : ZMod L) * k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hm, ZMod.stdAddChar_coe]
  congr 1
  simp only [angle]
  push_cast
  ring

theorem cx_eq_cos (k : ZMod L) : cx k = Real.cos (angle k) := by
  rw [cx, character_exp, Complex.exp_ofReal_mul_I_re]

theorem cy_eq_sin (k : ZMod L) : cy k = Real.sin (angle k) := by
  rw [cy, character_exp, Complex.exp_ofReal_mul_I_im]

omit [NeZero L] in
private theorem natCast_ne_zero {n : ℕ} (hn : 0 < n) (hLn : n < L) :
    (n : ZMod L) ≠ 0 := by
  intro hz
  have hdiv := (ZMod.natCast_eq_zero_iff n L).mp hz
  have := Nat.le_of_dvd hn hdiv
  omega

-- 一阶与二阶谐波都是非平凡加性特征，有限和严格为零。
theorem character_sum (hL : 3 ≤ L) :
    ∑ k : ZMod L, ZMod.stdAddChar k = 0 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    simpa only [Nat.cast_one] using natCast_ne_zero (L := L) (n := 1) (by omega) (by omega)
  simpa [h1] using AddChar.sum_mulShift (1 : ZMod L) (ZMod.isPrimitive_stdAddChar L)

theorem character_square_sum (hL : 3 ≤ L) :
    ∑ k : ZMod L, (ZMod.stdAddChar k) ^ 2 = 0 := by
  have h2 : (2 : ZMod L) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using natCast_ne_zero (L := L) (n := 2) (by omega) (by omega)
  have hs := AddChar.sum_mulShift (2 : ZMod L) (ZMod.isPrimitive_stdAddChar L)
  simpa only [h2, ite_false, Nat.cast_zero, mul_two,
    AddChar.map_add_eq_mul, ← pow_two] using hs

theorem cx_sum (hL : 3 ≤ L) : ∑ k : ZMod L, cx k = 0 := by
  have h := congrArg Complex.re (character_sum hL)
  simpa only [Complex.re_sum, Complex.zero_re, cx] using h

theorem cy_sum (hL : 3 ≤ L) : ∑ k : ZMod L, cy k = 0 := by
  have h := congrArg Complex.im (character_sum hL)
  simpa only [Complex.im_sum, Complex.zero_im, cy] using h

theorem cx_sq_add_cy_sq (k : ZMod L) : cx k ^ 2 + cy k ^ 2 = 1 := by
  have hn : ‖ZMod.stdAddChar k‖ = 1 := Circle.norm_coe (ZMod.toCircle k)
  have hs := Complex.normSq_eq_norm_sq (ZMod.stdAddChar k)
  rw [hn, one_pow, Complex.normSq_apply] at hs
  simpa only [cx, cy, pow_two] using hs

private theorem squares_sum :
    (∑ k : ZMod L, cx k ^ 2) + (∑ k : ZMod L, cy k ^ 2) = (L : ℝ) := by
  rw [← Finset.sum_add_distrib]
  simp only [cx_sq_add_cy_sq, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one]

private theorem squares_diff (hL : 3 ≤ L) :
    (∑ k : ZMod L, cx k ^ 2) - (∑ k : ZMod L, cy k ^ 2) = 0 := by
  have h := congrArg Complex.re (character_square_sum hL)
  simpa only [Complex.re_sum, Complex.zero_re, pow_two, Complex.mul_re,
    Finset.sum_sub_distrib, cx, cy] using h

theorem cx_square_sum (hL : 3 ≤ L) : ∑ k : ZMod L, cx k ^ 2 = (L : ℝ) / 2 := by
  linarith [squares_sum (L := L), squares_diff hL]

theorem cy_square_sum (hL : 3 ≤ L) : ∑ k : ZMod L, cy k ^ 2 = (L : ℝ) / 2 := by
  linarith [squares_sum (L := L), squares_diff hL]

theorem cx_cy_sum (hL : 3 ≤ L) : ∑ k : ZMod L, cx k * cy k = 0 := by
  have h := congrArg Complex.im (character_square_sum hL)
  simp only [Complex.im_sum, Complex.zero_im, pow_two, Complex.mul_im,
    Finset.sum_add_distrib] at h
  have hc : (∑ k : ZMod L, (ZMod.stdAddChar k).im * (ZMod.stdAddChar k).re) =
      ∑ k : ZMod L, (ZMod.stdAddChar k).re * (ZMod.stdAddChar k).im := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hc] at h
  change (∑ k : ZMod L, (ZMod.stdAddChar k).re * (ZMod.stdAddChar k).im) = 0
  linarith

-- 分母 L 对应每个相位的均匀概率 1/L。
theorem phase_moments (hL : 3 ≤ L) :
    (∑ k : ZMod L, cx k) / L = 0 ∧
    (∑ k : ZMod L, cy k) / L = 0 ∧
    (∑ k : ZMod L, cx k ^ 2) / L = 1 / 2 ∧
    (∑ k : ZMod L, cy k ^ 2) / L = 1 / 2 ∧
    (∑ k : ZMod L, cx k * cy k) / L = 0 := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cx_sum hL, zero_div]
  · rw [cy_sum hL, zero_div]
  · rw [cx_square_sum hL]
    field_simp
  · rw [cy_square_sum hL]
    field_simp
  · rw [cx_cy_sum hL, zero_div]

theorem cos_sin_moments (hL : 3 ≤ L) :
    (∑ k : ZMod L, Real.cos (angle k)) / L = 0 ∧
    (∑ k : ZMod L, Real.sin (angle k)) / L = 0 ∧
    (∑ k : ZMod L, Real.cos (angle k) ^ 2) / L = 1 / 2 ∧
    (∑ k : ZMod L, Real.sin (angle k) ^ 2) / L = 1 / 2 ∧
    (∑ k : ZMod L, Real.cos (angle k) * Real.sin (angle k)) / L = 0 := by
  simpa only [cx_eq_cos, cy_eq_sin] using phase_moments hL

end CopyQuantumMetrology.PhaseMoments
