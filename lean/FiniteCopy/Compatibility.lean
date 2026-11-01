import FiniteCopy.SpinCoupling
import FiniteCopy.SpinPhase

open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

theorem complexR_eq_raising (n : ℕ) :
    complexR n = raisingMatrix (spinCoefficient n) := by
  ext i j
  simp [complexR, R, raisingMatrix, edge, spinCoefficient, Matrix.sum_apply,
    Matrix.single_apply, apply_ite]

theorem complexR_adjoint_eq_lowering (n : ℕ) :
    (complexR n)ᴴ = loweringMatrix (spinCoefficient n) := by
  rw [complexR_eq_raising]
  simp [raisingMatrix, loweringMatrix, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_single]

theorem Jx_eq_spinX (n : ℕ) : Jx n = spinX (spinCoefficient n) := by
  unfold Jx spinX
  rw [complexR_adjoint_eq_lowering, complexR_eq_raising]

theorem Jy_eq_spinY (n : ℕ) : Jy n = spinY (spinCoefficient n) := by
  unfold Jy spinY
  rw [complexR_adjoint_eq_lowering, complexR_eq_raising]

theorem qubit_Jx : Jx 1 = (2 : ℂ)⁻¹ • !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Jx, complexR, R, Fin.sum_univ_one, edge, Matrix.single_apply,
      Matrix.conjTranspose_apply]

theorem qubit_Jy : Jy 1 = (2 : ℂ)⁻¹ • !![0, Complex.I; -Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Jy, complexR, R, Fin.sum_univ_one, edge, Matrix.single_apply,
      Matrix.conjTranspose_apply] <;> ring

theorem tensorJx_actual (n : ℕ) : tensorJx n =
    spinX (spinCoefficient n) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ
      ((2 : ℂ)⁻¹ • !![0, 1; 1, 0]) := by
  rw [tensorJx, Jx_eq_spinX n, qubit_Jx]

theorem tensorJy_actual (n : ℕ) : tensorJy n =
    spinY (spinCoefficient n) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ
      ((2 : ℂ)⁻¹ • !![0, Complex.I; -Complex.I, 0]) := by
  rw [tensorJy, Jy_eq_spinY n, qubit_Jy]

theorem actual_spinX_CG (n : ℕ) :
    (spinX (spinCoefficient n) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ
        ((2 : ℂ)⁻¹ • !![0, 1; 1, 0])) * CG n = CG n * outputJx n := by
  rw [← tensorJx_actual]
  exact CG_Jx n

theorem actual_spinY_CG (n : ℕ) :
    (spinY (spinCoefficient n) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ
        ((2 : ℂ)⁻¹ • !![0, Complex.I; -Complex.I, 0])) * CG n = CG n * outputJy n := by
  rw [← tensorJy_actual]
  exact CG_Jy n

theorem actual_outputX_succ (n : ℕ) : outputJx (n+1) =
    Matrix.fromBlocks (spinX (spinCoefficient (n+2))) 0 0
      (spinX (spinCoefficient n)) := by
  rw [outputJx_succ, Jx_eq_spinX, Jx_eq_spinX]

theorem actual_outputY_succ (n : ℕ) : outputJy (n+1) =
    Matrix.fromBlocks (spinY (spinCoefficient (n+2))) 0 0
      (spinY (spinCoefficient n)) := by
  rw [outputJy_succ, Jy_eq_spinY, Jy_eq_spinY]

end CopyQuantumMetrology.ClebschGordan


