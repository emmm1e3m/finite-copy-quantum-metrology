import FiniteCopy.TensorModel

open scoped BigOperators ComplexOrder
open Matrix
noncomputable section
namespace CopyQuantumMetrology.TensorModel

-- Bloch圆盘内的显式Cholesky因子，包含边界上的退化情形。
def rhoFactor (x y : ℝ) : QMatrix :=
  !![1, 0; (x : ℂ) - (y : ℂ) * Complex.I, (Real.sqrt (1-x^2-y^2) : ℂ)]

theorem rho_factor (x y : ℝ) (h : x^2 + y^2 ≤ 1) :
    rho x y = (2 : ℝ)⁻¹ • (rhoFactor x y * (rhoFactor x y)ᴴ) := by
  have hs : (Real.sqrt (1-x^2-y^2))^2 = 1-x^2-y^2 :=
    Real.sq_sqrt (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, rhoFactor, sigmaX, sigmaY, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat, Complex.smul_re,
      Complex.smul_im] <;> (try constructor) <;> nlinarith [hs]

theorem rho_posSemidef (x y : ℝ) (h : x^2 + y^2 ≤ 1) : (rho x y).PosSemidef := by
  rw [rho_factor x y h]
  exact (Matrix.posSemidef_self_mul_conjTranspose (rhoFactor x y)).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)

theorem rhoTensor_posSemidef (N : ℕ) (x y : ℝ) (h : x^2 + y^2 ≤ 1) :
    (rhoTensor N x y).PosSemidef := tensorPower_posSemidef N _ (rho_posSemidef x y h)

end CopyQuantumMetrology.TensorModel




