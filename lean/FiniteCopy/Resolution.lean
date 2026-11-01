import FiniteCopy.ActualFrame
import FiniteCopy.POVMCompatibility
open scoped BigOperators
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths
open ClebschGordan TensorModel FiniteCopy.POVM FiniteCopy.Risk

def weight (N : ℕ) (b : B N) : ℝ := (spin N b+1 : ℝ) / (2 : ℝ)^N
def tangentAxes (N : ℕ) (a : Fin 2) : NMatrix N :=
  (2 / (2 : ℂ)^N) • collectiveAxes N a

theorem weight_nonneg (N : ℕ) (b : B N) : 0 ≤ weight N b := by
  unfold weight
  positivity

lemma povm_tangent_op (a : Fin 2) (n : ℕ) :
    (if a = 0 then tangentX n (FiniteCopy.Algebra.spinEdge n)
      else tangentY n (FiniteCopy.Algebra.spinEdge n)) =
      (2 / (n+1 : ℝ)) • spinOp a n := by
  fin_cases a <;> simp [spinOp, Jx_eq_spinX, Jy_eq_spinY,
    tangentX_eq_spinX, tangentY_eq_spinY]

lemma weighted_reference_term (N : ℕ) (b : B N) :
    weight N b • (U N b * state (spin N b) * (U N b)ᴴ) =
      ((2 : ℝ)^N)⁻¹ • (U N b * (U N b)ᴴ) := by
  rw [state, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
  congr 1
  have hd : (spin N b+1 : ℝ) ≠ 0 := by positivity
  simp only [weight, Nat.cast_add, Nat.cast_one]
  field_simp

lemma weighted_tangent_term (N : ℕ) (b : B N) (a : Fin 2) :
    weight N b • (U N b *
      (if a = 0 then tangentX (spin N b) (FiniteCopy.Algebra.spinEdge (spin N b))
        else tangentY (spin N b) (FiniteCopy.Algebra.spinEdge (spin N b))) * (U N b)ᴴ) =
      (2 / (2 : ℝ)^N) • (U N b * spinOp a (spin N b) * (U N b)ᴴ) := by
  rw [povm_tangent_op, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  have hd : (spin N b+1 : ℝ) ≠ 0 := by positivity
  unfold weight
  field_simp

theorem reference_decomposition (N : ℕ) : rhoTensor N 0 0 =
    ∑ b, weight N b • (U N b * state (spin N b) * (U N b)ᴴ) := by
  simp_rw [weighted_reference_term]
  rw [← Finset.smul_sum, U_complete, rhoTensor_zero]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem tangent_decomposition (N : ℕ) (a : Fin 2) : tangentAxes N a =
    ∑ b, weight N b • (U N b *
      (if a = 0 then tangentX (spin N b) (FiniteCopy.Algebra.spinEdge (spin N b))
        else tangentY (spin N b) (FiniteCopy.Algebra.spinEdge (spin N b))) * (U N b)ᴴ) := by
  simp_rw [weighted_tangent_term]
  rw [← Finset.smul_sum, ← collective_decomposition]
  ext i j
  simp [tangentAxes, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def blockResolution (N : ℕ) :
    BlockResolution (rhoTensor N 0 0) (tangentAxes N) (spin N) (weight N) where
  embedding := U N
  isometry := U_isometry N
  weight_nonneg := weight_nonneg N
  reference := reference_decomposition N
  tangent := tangent_decomposition N

theorem tangentAxes_deriv_x (N : ℕ) :
    HasDerivAt (fun x : ℝ => rhoTensor N x 0) (tangentAxes N 0) 0 := by
  simpa [tangentAxes, collectiveAxes] using rhoTensor_hasDerivAt_x N

theorem tangentAxes_deriv_y (N : ℕ) :
    HasDerivAt (fun y : ℝ => rhoTensor N 0 y) (tangentAxes N 1) 0 := by
  simpa [tangentAxes, collectiveAxes] using rhoTensor_hasDerivAt_y N

end CopyQuantumMetrology.SpinPaths
