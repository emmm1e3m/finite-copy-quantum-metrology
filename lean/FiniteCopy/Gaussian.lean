import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open scoped Real NNReal ENNReal

namespace CopyQuantumMetrology

noncomputable def column (m S t : ℝ) : ℝ :=
  (2 * Real.pi * S) ^ (-1 / 4 : ℝ) * Real.exp (-(t - m)^2 / (4 * S))

lemma column_pos (m t : ℝ) {S : ℝ} (hS : 0 < S) : 0 < column m S t := by
  unfold column
  positivity

lemma column_nonneg (m t : ℝ) {S : ℝ} (hS : 0 < S) : 0 ≤ column m S t :=
  le_of_lt (column_pos m t hS)

lemma column_sq_eq_gaussianPDF (m t : ℝ) {S : ℝ} (hS : 0 < S) :
    column m S t ^ 2 = gaussianPDFReal m ⟨S, hS.le⟩ t := by
  have hp : 0 ≤ 2 * Real.pi * S := by positivity
  change column m S t ^ 2 = (Real.sqrt (2*Real.pi*S))⁻¹ *
    Real.exp (-(t-m)^2/(2*S))
  unfold column
  rw [mul_pow, ← Real.rpow_mul_natCast hp]
  norm_num
  rw [Real.rpow_neg hp,
    ← Real.sqrt_eq_rpow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma integrable_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    Integrable (fun t => column m S t ^ 2) := by
  simp_rw [column_sq_eq_gaussianPDF _ _ hS]
  exact integrable_gaussianPDFReal _ _

lemma integral_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, column m S t ^ 2) = 1 := by
  simp_rw [column_sq_eq_gaussianPDF _ _ hS]
  exact integral_gaussianPDFReal_eq_one m (by
    intro h
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    exact (ne_of_gt hS) hh)

lemma integrable_centered_pow_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) (n : ℕ) :
    Integrable (fun t => (t - m)^n * column m S t ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (2 * S)⁻¹) (by positivity) (s := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  simp only [Real.rpow_natCast] at h
  have hh := (h.const_mul (Real.sqrt (2 * Real.pi * S))⁻¹).comp_sub_right m
  convert hh using 1
  ext t
  rw [column_sq_eq_gaussianPDF _ _ hS]
  change (t-m)^n * ((Real.sqrt (2*Real.pi*S))⁻¹ * Real.exp (-(t-m)^2/(2*S))) =
    (Real.sqrt (2*Real.pi*S))⁻¹ * ((t-m)^n * Real.exp (-((2*S)⁻¹)*(t-m)^2))
  rw [show -(t-m)^2/(2*S) = -((2*S)⁻¹)*(t-m)^2 by ring]
  ring

lemma hasDerivAt_column_sq (m t : ℝ) {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun t => column m S t ^ 2)
      (-(t - m) / S * column m S t ^ 2) t := by
  simp_rw [column_sq_eq_gaussianPDF _ _ hS]
  change HasDerivAt (fun t => (Real.sqrt (2*Real.pi*S))⁻¹ * Real.exp (-(t-m)^2/(2*S)))
    (-(t-m)/S * ((Real.sqrt (2*Real.pi*S))⁻¹ * Real.exp (-(t-m)^2/(2*S)))) t
  convert (((((hasDerivAt_id t).sub_const m).pow 2).neg.div_const (2 * S)).exp.const_mul
    (Real.sqrt (2 * Real.pi * S))⁻¹) using 1
  · rfl
  · dsimp
    ring

lemma integral_centered_moment_recurrence (m : ℝ) {S : ℝ} (hS : 0 < S) (n : ℕ) :
    (∫ t, (t - m)^(n + 2) * column m S t ^ 2) =
      (n + 1 : ℝ) * S * (∫ t, (t - m)^n * column m S t ^ 2) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => (t-m)^(n+1))
    (u' := fun t : ℝ => (n+1 : ℝ) * (t-m)^n)
    (v := fun t : ℝ => column m S t ^ 2)
    (v' := fun t : ℝ => -(t-m)/S * column m S t ^ 2)
    (by
      intro t _
      convert ((hasDerivAt_id t).sub_const m).pow (n+1) using 1
      · rfl
      · simp)
    (by intro t _; exact hasDerivAt_column_sq m t hS)
    (by
      convert (integrable_centered_pow_column_sq m hS (n+2)).const_mul (-1/S) using 1
      ext t
      simp only [Pi.mul_apply, pow_add, pow_one, pow_two]
      ring)
    (by
      convert (integrable_centered_pow_column_sq m hS n).const_mul (n+1 : ℝ) using 1
      ext t
      simp only [Pi.mul_apply]
      ring)
    (integrable_centered_pow_column_sq m hS (n+1))
  have h' : (-1/S) * (∫ t, (t-m)^(n+2) * column m S t ^ 2) =
      -((n+1 : ℝ) * (∫ t, (t-m)^n * column m S t ^ 2)) := by
    calc
      _ = ∫ t, (t-m)^(n+1) * (-(t-m)/S * column m S t ^ 2) := by
        rw [← integral_const_mul]
        congr 1
        ext t
        simp only [pow_add, pow_one, pow_two]
        ring
      _ = -(∫ t, ((n+1 : ℝ)*(t-m)^n) * column m S t ^ 2) := h
      _ = _ := by rw [← integral_const_mul]; congr 1; congr 1; ext t; ring
  field_simp [ne_of_gt hS] at h'
  nlinarith

lemma integral_centered_sq_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m)^2 * column m S t ^ 2) = S := by
  simpa [integral_column_sq m hS] using integral_centered_moment_recurrence m hS 0

lemma integral_centered_first_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m) * column m S t ^ 2) = 0 := by
  have hne : (⟨S, hS.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact (ne_of_gt hS) (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
  calc
    _ = ∫ t, (t-m) * column 0 S (t-m) ^ 2 := by simp [column]
    _ = ∫ t, t * column 0 S t ^ 2 :=
      integral_sub_right_eq_self (μ := volume) (fun t : ℝ => t * column 0 S t ^ 2) m
    _ = ∫ t, t ∂gaussianReal 0 ⟨S, hS.le⟩ := by
      rw [integral_gaussianReal_eq_integral_smul hne]
      simp_rw [column_sq_eq_gaussianPDF _ _ hS]
      simp only [smul_eq_mul, mul_comm]
    _ = 0 := integral_id_gaussianReal

lemma integral_centered_third_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m)^3 * column m S t ^ 2) = 0 := by
  have h := integral_centered_moment_recurrence m hS 1
  simpa [integral_centered_first_column_sq m hS] using h

lemma integral_centered_fourth_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m)^4 * column m S t ^ 2) = 3*S^2 := by
  have h := integral_centered_moment_recurrence m hS 2
  rw [integral_centered_sq_column_sq m hS] at h
  norm_num at h
  nlinarith

lemma integral_centered_sixth_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m)^6 * column m S t ^ 2) = 15*S^3 := by
  have h := integral_centered_moment_recurrence m hS 4
  rw [integral_centered_fourth_column_sq m hS] at h
  norm_num at h
  nlinarith

lemma integral_centered_eighth_column_sq (m : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, (t-m)^8 * column m S t ^ 2) = 105*S^4 := by
  have h := integral_centered_moment_recurrence m hS 6
  rw [integral_centered_sixth_column_sq m hS] at h
  norm_num at h
  nlinarith

-- 一阶对数导数允许均值与方差同时依赖参数。
noncomputable def columnScore (m S m₁ S₁ t : ℝ) : ℝ :=
  -S₁/(4*S) + (t-m)*m₁/(2*S) + (t-m)^2*S₁/(4*S^2)

noncomputable def columnScoreDeriv (m S m₁ S₁ m₂ S₂ t : ℝ) : ℝ :=
  -S₂/(4*S) + S₁^2/(4*S^2) + (-m₁^2+(t-m)*m₂)/(2*S) -
    (t-m)*m₁*S₁/S^2 + (t-m)^2*S₂/(4*S^2) - (t-m)^2*S₁^2/(2*S^3)

lemma column_eq_exp_log (m t : ℝ) {S : ℝ} (hS : 0 < S) :
    column m S t = Real.exp ((-1/4 : ℝ)*Real.log (2*Real.pi*S) - (t-m)^2/(4*S)) := by
  unfold column
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1
  ring

lemma hasDerivAt_column {m S : ℝ → ℝ} {s m₁ S₁ : ℝ} (t : ℝ)
    (hm : HasDerivAt m m₁ s) (hS : HasDerivAt S S₁ s) (hpos : 0 < S s) :
    HasDerivAt (fun x => column (m x) (S x) t)
      (column (m s) (S s) t * columnScore (m s) (S s) m₁ S₁ t) s := by
  have hl : HasDerivAt
      (fun x => (-1/4 : ℝ)*Real.log (2*Real.pi*S x) - (t-m x)^2/(4*S x))
      (columnScore (m s) (S s) m₁ S₁ t) s := by
    convert (((hS.const_mul (2*Real.pi)).log (by positivity)).const_mul (-1/4)).sub
      (((hm.const_sub t).pow 2).div (hS.const_mul 4) (by positivity)) using 1
    dsimp [columnScore]
    field_simp [ne_of_gt hpos, Real.pi_ne_zero]
    ring
  have he := hl.exp
  rw [← column_eq_exp_log _ _ hpos] at he
  apply he.congr_of_eventuallyEq
  filter_upwards [hS.continuousAt.eventually (lt_mem_nhds hpos)] with x hx
  exact column_eq_exp_log _ _ hx

lemma hasDerivAt_columnScore {m S m₁ S₁ : ℝ → ℝ} {s m₂ S₂ : ℝ} (t : ℝ)
    (hm : HasDerivAt m (m₁ s) s) (hS : HasDerivAt S (S₁ s) s)
    (hm₁ : HasDerivAt m₁ m₂ s) (hS₁ : HasDerivAt S₁ S₂ s) (hpos : 0 < S s) :
    HasDerivAt (fun x => columnScore (m x) (S x) (m₁ x) (S₁ x) t)
      (columnScoreDeriv (m s) (S s) (m₁ s) (S₁ s) m₂ S₂ t) s := by
  unfold columnScore
  convert ((hS₁.neg.div (hS.const_mul 4) (by positivity)).add
    (((hm.const_sub t).mul hm₁).div (hS.const_mul 2) (by positivity))).add
    ((((hm.const_sub t).pow 2).mul hS₁).div ((hS.pow 2).const_mul 4)
      (by change 4 * S s ^ 2 ≠ 0; positivity)) using 1
  dsimp [columnScoreDeriv]
  field_simp [ne_of_gt hpos]
  ring

lemma hasDerivAt_column_first {m S m₁ S₁ : ℝ → ℝ} {s m₂ S₂ : ℝ} (t : ℝ)
    (hm : HasDerivAt m (m₁ s) s) (hS : HasDerivAt S (S₁ s) s)
    (hm₁ : HasDerivAt m₁ m₂ s) (hS₁ : HasDerivAt S₁ S₂ s) (hpos : 0 < S s) :
    HasDerivAt (fun x => column (m x) (S x) t * columnScore (m x) (S x) (m₁ x) (S₁ x) t)
      (column (m s) (S s) t * (columnScore (m s) (S s) (m₁ s) (S₁ s) t ^ 2 +
        columnScoreDeriv (m s) (S s) (m₁ s) (S₁ s) m₂ S₂ t)) s := by
  convert (hasDerivAt_column t hm hS hpos).mul
    (hasDerivAt_columnScore t hm hS hm₁ hS₁ hpos) using 1
  ring

-- 邻域中的一阶导数保证这里确为原始幅值的二阶导数。
lemma hasDerivAt_deriv_column {m S m₁ S₁ : ℝ → ℝ} {s m₂ S₂ : ℝ} (t : ℝ)
    (hm : ∀ᶠ x in 𝓝 s, HasDerivAt m (m₁ x) x)
    (hS : ∀ᶠ x in 𝓝 s, HasDerivAt S (S₁ x) x)
    (hm₁ : HasDerivAt m₁ m₂ s) (hS₁ : HasDerivAt S₁ S₂ s) (hpos : 0 < S s) :
    HasDerivAt (deriv (fun x => column (m x) (S x) t))
      (column (m s) (S s) t * (columnScore (m s) (S s) (m₁ s) (S₁ s) t ^ 2 +
        columnScoreDeriv (m s) (S s) (m₁ s) (S₁ s) m₂ S₂ t)) s := by
  apply (hasDerivAt_column_first t hm.self_of_nhds hS.self_of_nhds hm₁ hS₁ hpos).congr_of_eventuallyEq
  filter_upwards [hm, hS, hS.self_of_nhds.continuousAt.eventually (lt_mem_nhds hpos)]
    with x hmx hSx hpx
  exact (hasDerivAt_column t hmx hSx hpx).deriv

lemma hasDerivAt_column_moving {S : ℝ → ℝ} {s S₁ : ℝ} (t : ℝ)
    (hS : HasDerivAt S S₁ s) (hpos : 0 < S s) :
    HasDerivAt (fun x => column x (S x) t)
      (column s (S s) t * ((t-s)/(2*S s) + S₁/(4*S s)*((t-s)^2/S s-1))) s := by
  convert hasDerivAt_column t (hasDerivAt_id s) hS hpos using 1 <;>
    simp only [id_eq, columnScore] <;> field_simp [ne_of_gt hpos] <;> ring

end CopyQuantumMetrology
