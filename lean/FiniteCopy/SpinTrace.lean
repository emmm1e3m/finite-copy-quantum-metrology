import FiniteCopy.SpinPhase
import FiniteCopy.Algebra
open scoped BigOperators ComplexOrder
open Matrix Complex
noncomputable section
namespace CopyQuantumMetrology
variable {n : ℕ}

lemma trace_raising_lowering (c : Fin n → ℝ) :
    Matrix.trace (raisingMatrix c * loweringMatrix c) = ∑ r, (c r : ℂ)^2 := by
  simp only [raisingMatrix, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul]
  unfold loweringMatrix
  simp only [Matrix.sum_apply, Matrix.single_apply]
  simp only [Fin.castSucc_inj, Fin.succ_inj, and_self, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, smul_eq_mul, ← sq]

lemma trace_spin_squares (c : Fin n → ℝ) :
    Matrix.trace (spinX c * spinX c) + Matrix.trace (spinY c * spinY c) =
      ∑ r, (c r : ℂ)^2 := by
  have ht : Matrix.trace (raisingMatrix c * loweringMatrix c) =
      Matrix.trace (loweringMatrix c * raisingMatrix c) := Matrix.trace_mul_comm _ _
  simp only [spinX, spinY, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, smul_eq_mul]
  rw [← ht, trace_raising_lowering]
  norm_num
  ring_nf
  simp [Complex.I_sq]
  ring

lemma trace_spin_squares_re (c : Fin n → ℝ) :
    (Matrix.trace (spinX c * spinX c)).re + (Matrix.trace (spinY c * spinY c)).re =
      ∑ r, c r ^ 2 := by
  have h := congrArg Complex.re (trace_spin_squares c)
  simpa only [Complex.add_re, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] using h


lemma spinCoefficient_eq_spinEdge (n : ℕ) (r : Fin n) :
    spinCoefficient n r = FiniteCopy.Algebra.spinEdge n r.val := rfl

theorem spin_trace_value (n : ℕ) :
    (Matrix.trace (spinX (spinCoefficient n) * spinX (spinCoefficient n))).re +
    (Matrix.trace (spinY (spinCoefficient n) * spinY (spinCoefficient n))).re =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) * (n+1) := by
  rw [trace_spin_squares_re]
  simp_rw [spinCoefficient_eq_spinEdge]
  rw [Fin.sum_univ_eq_sum_range (fun i => FiniteCopy.Algebra.spinEdge n i ^ 2), ← FiniteCopy.Algebra.spinA_sum_eq_edge_sq,
    FiniteCopy.Algebra.spinA_sum]

end CopyQuantumMetrology


