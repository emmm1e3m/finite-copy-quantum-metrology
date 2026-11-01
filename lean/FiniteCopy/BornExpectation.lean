import FiniteCopy.TensorModel
import FiniteCopy.QuantumModel

open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
open Matrix MeasureTheory
noncomputable section
namespace CopyQuantumMetrology.TensorModel

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

theorem born_hasDerivAt (ρ : ℝ → Matrix ι ι ℂ) (D E : Matrix ι ι ℂ)
    (t : ℝ) (hρ : HasDerivAt ρ D t) :
    HasDerivAt (fun x => born (ρ x) E) (born D E) t := by
  have htr : HasDerivAt (fun x => Matrix.trace (ρ x * E)) (Matrix.trace (D * E)) t := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hρ i) j).mul_const (E j i)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t htr

theorem born_rhoTensor_hasDerivAt_x (N : ℕ) (E : NMatrix N) :
    HasDerivAt (fun x : ℝ => born (rhoTensor N x 0) E)
      (born ((2 / (2 : ℂ)^N) • collectiveX N) E) 0 :=
  born_hasDerivAt _ _ E 0 (rhoTensor_hasDerivAt_x N)

theorem born_rhoTensor_hasDerivAt_y (N : ℕ) (E : NMatrix N) :
    HasDerivAt (fun y : ℝ => born (rhoTensor N 0 y) E)
      (born ((2 / (2 : ℂ)^N) • collectiveY N) E) 0 :=
  born_hasDerivAt _ _ E 0 (rhoTensor_hasDerivAt_y N)

theorem born_rhoTensor_zero (N : ℕ) (E : NMatrix N) :
    born (rhoTensor N 0 0) E = (Matrix.trace E).re / (2 : ℝ)^N := by
  rw [rhoTensor_zero]
  unfold born
  rw [smul_mul, one_mul, Matrix.trace_smul]
  have hc : ((2 : ℂ)^N)⁻¹ = (((2 : ℝ)^N)⁻¹ : ℝ) := by push_cast; rfl
  rw [hc, smul_eq_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring
section Integral
variable [MeasurableSpace Ω] (μ : Measure Ω)

-- 有限维矩阵线性性将期望改写成一个固定矩阵的 Born 配对。
-- 因而无需把微分与无限积分交换当作未验证步骤。
theorem integral_born (A : Matrix ι ι ℂ) (E : Ω → Matrix ι ι ℂ)
    (hE : ∀ i j, Integrable (fun z => E z i j) μ) :
    (∫ z, born A (E z) ∂μ) = born A (fun i j => ∫ z, E z i j ∂μ) := by
  have hint : Integrable (fun z => Matrix.trace (A * E z)) μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hE j i).const_mul (A i j)))
  unfold born
  change (∫ z, RCLike.re (Matrix.trace (A * E z)) ∂μ) =
    RCLike.re (Matrix.trace (A * Matrix.of (fun i j => ∫ z, E z i j ∂μ)))
  rw [integral_re hint]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp only [integral_const_mul, Matrix.of_apply]
    · intro j hj
      exact (hE j i).const_mul (A i j)
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => (hE j i).const_mul (A i j))

theorem born_real_smul_right (A E : Matrix ι ι ℂ) (u : ℝ) :
    born A (u • E) = u * born A E := by
  simp only [born, Matrix.mul_smul, Matrix.trace_smul]
  change (u • Matrix.trace (A * E)).re = u * (Matrix.trace (A * E)).re
  simp

theorem expectation_eq_born_integral (A : Matrix ι ι ℂ)
    (E : Ω → Matrix ι ι ℂ) (u : Ω → ℝ)
    (hint : ∀ i j, Integrable (fun z => u z • E z i j) μ) :
    (∫ z, u z * born A (E z) ∂μ) =
      born A (fun i j => ∫ z, u z • E z i j ∂μ) := by
  simpa only [born_real_smul_right, Matrix.smul_apply] using
    integral_born μ A (fun z => u z • E z) hint

theorem expectation_hasDerivAt (ρ : ℝ → Matrix ι ι ℂ) (D : Matrix ι ι ℂ)
    (E : Ω → Matrix ι ι ℂ) (u : Ω → ℝ) (t : ℝ)
    (hρ : HasDerivAt ρ D t)
    (hint : ∀ i j, Integrable (fun z => u z • E z i j) μ) :
    HasDerivAt (fun x => ∫ z, u z * born (ρ x) (E z) ∂μ)
      (∫ z, u z * born D (E z) ∂μ) t := by
  simpa only [expectation_eq_born_integral μ _ E u hint] using
    born_hasDerivAt ρ D (fun i j => ∫ z, u z • E z i j ∂μ) t hρ

theorem rhoTensor_expectation_hasDerivAt_x (N : ℕ) (E : Ω → NMatrix N)
    (u : Ω → ℝ) (hint : ∀ i j, Integrable (fun z => u z • E z i j) μ) :
    HasDerivAt (fun x => ∫ z, u z * born (rhoTensor N x 0) (E z) ∂μ)
      (∫ z, u z * born ((2 / (2 : ℂ)^N) • collectiveX N) (E z) ∂μ) 0 :=
  expectation_hasDerivAt μ _ _ E u 0 (rhoTensor_hasDerivAt_x N) hint

theorem rhoTensor_expectation_hasDerivAt_y (N : ℕ) (E : Ω → NMatrix N)
    (u : Ω → ℝ) (hint : ∀ i j, Integrable (fun z => u z • E z i j) μ) :
    HasDerivAt (fun y => ∫ z, u z * born (rhoTensor N 0 y) (E z) ∂μ)
      (∫ z, u z * born ((2 / (2 : ℂ)^N) • collectiveY N) (E z) ∂μ) 0 :=
  expectation_hasDerivAt μ _ _ E u 0 (rhoTensor_hasDerivAt_y N) hint

end Integral
end CopyQuantumMetrology.TensorModel





