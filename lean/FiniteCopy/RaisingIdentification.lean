import FiniteCopy.ActualRaising
import FiniteCopy.NHUnitary
open scoped BigOperators
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator
open CopyQuantumMetrology CopyQuantumMetrology.ClebschGordan
open CopyQuantumMetrology.SpinPaths CopyQuantumMetrology.TensorModel
open FiniteCopy.Algebra

-- 从逐项升矩阵识别039框架使用的同一个真实自旋算子。
lemma raiseReal_eq_R (n : ℕ) : raiseReal n (spinEdge n) = R n := by
  ext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · have h := R_mul_zero (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) j
    simpa [raiseReal] using h.symm
  · have hr := R_mul_succ (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) r j
    simp only [Matrix.mul_one, Matrix.one_apply] at hr
    rw [hr]
    by_cases h : r.castSucc = j
    · subst j
      simp [raiseReal, edge, spinEdge]
    · have hn : r.val ≠ j.val := fun he => h (Fin.ext he)
      simp [raiseReal, h, hn]

theorem raiseMatrix_eq_complexR (n : ℕ) : raiseMatrix n (spinEdge n) = complexR n := by
  unfold raiseMatrix complexR
  rw [raiseReal_eq_R]

lemma blockRaising_eq_diagonalRaising (N : ℕ) :
    blockRaising (spin N) (fun b => spinEdge (spin N b)) = diagonalRaising N := by
  simp only [blockRaising, diagonalRaising, raiseMatrix_eq_complexR]

theorem physicalRaising_block_transport (N : ℕ) : physicalRaising N =
    transport (frameUnitary N) (blockRaising (spin N) (fun b => spinEdge (spin N b))) := by
  rw [blockRaising_eq_diagonalRaising, physicalRaising_transport]

lemma axisX_complexR (n : ℕ) : axisX (complexR n) = Jx n := by
  ext i j
  simp [axisX, Jx, Matrix.smul_apply, Complex.real_smul]
  ring

lemma axisY_complexR (n : ℕ) : axisY (complexR n) = Jy n := rfl

lemma axisX_diagonalRaising (N : ℕ) : axisX (diagonalRaising N) =
    diagOp (signature N) 0 := by
  unfold axisX diagonalRaising diagOp
  simp only [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_add,
    ← Matrix.blockDiagonal'_smul, spinOp, ite_true]
  congr 1
  funext b
  exact axisX_complexR (spin N b)

lemma axisY_diagonalRaising (N : ℕ) : axisY (diagonalRaising N) =
    diagOp (signature N) 1 := by
  unfold axisY diagonalRaising diagOp
  simp only [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_sub,
    ← Matrix.blockDiagonal'_smul, spinOp, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rfl

-- NH中两个切向确为原始N比特模型的集体Jx、Jy，固定升算子方向。
theorem axisX_physicalRaising (N : ℕ) : axisX (physicalRaising N) = collectiveX N := by
  rw [physicalRaising_transport, axisX_transport, axisX_diagonalRaising,
    ← collective_transport]
  simp [collectiveAxes]

theorem axisY_physicalRaising (N : ℕ) : axisY (physicalRaising N) = collectiveY N := by
  rw [physicalRaising_transport, axisY_transport, axisY_diagonalRaising,
    ← collective_transport]
  simp [collectiveAxes]

end FiniteCopy.NHOperator
