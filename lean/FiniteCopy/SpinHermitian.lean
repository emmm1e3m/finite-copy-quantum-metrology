import FiniteCopy.SpinStatistics
open scoped BigOperators ComplexOrder
open Matrix Complex
noncomputable section
namespace CopyQuantumMetrology
variable {n : ℕ}

lemma raising_adjoint (c : Fin n → ℝ) : (raisingMatrix c)ᴴ = loweringMatrix c := by
  simp [raisingMatrix, loweringMatrix, Matrix.conjTranspose_sum, Matrix.conjTranspose_single]

lemma lowering_adjoint (c : Fin n → ℝ) : (loweringMatrix c)ᴴ = raisingMatrix c := by
  rw [← raising_adjoint, Matrix.conjTranspose_conjTranspose]

lemma spinX_hermitian (c : Fin n → ℝ) : (spinX c).IsHermitian := by
  simp [Matrix.IsHermitian, spinX, Matrix.conjTranspose_smul, raising_adjoint, lowering_adjoint,
    add_comm]

lemma spinY_hermitian (c : Fin n → ℝ) : (spinY c).IsHermitian := by
  simp only [Matrix.IsHermitian, spinY, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, raising_adjoint, lowering_adjoint]
  ext i j
  simp [Complex.star_def]
  ring

lemma trace_raising_zero (c : Fin n → ℝ) : Matrix.trace (raisingMatrix c) = 0 := by
  unfold raisingMatrix
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro r hr
  apply Matrix.trace_single_eq_of_ne
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_succ, Fin.val_castSucc] at he
  omega

lemma trace_lowering_zero (c : Fin n → ℝ) : Matrix.trace (loweringMatrix c) = 0 := by
  rw [← raising_adjoint, Matrix.trace_conjTranspose, trace_raising_zero]
  simp

lemma trace_spin_zero (c : Fin n → ℝ) (b : Bool) : Matrix.trace (spinObservable c b) = 0 := by
  cases b <;> simp [spinObservable, spinX, spinY, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_sub, trace_raising_zero, trace_lowering_zero]

lemma spinReference_positive (n : ℕ) : (spinReference n).PosSemidef := by
  exact (Matrix.PosSemidef.one).smul (by positivity : 0 ≤ (n+1 : ℝ)⁻¹)

lemma trace_spinReference (n : ℕ) : Matrix.trace (spinReference n) = 1 := by
  simp [spinReference, Matrix.trace_smul, Matrix.trace_one, RCLike.real_smul_eq_coe_mul]
  field_simp

lemma trace_spinTangent (c : Fin n → ℝ) (b : Bool) : Matrix.trace (spinTangent c b) = 0 := by
  simp [spinTangent, Matrix.trace_smul, trace_spin_zero]

end CopyQuantumMetrology

