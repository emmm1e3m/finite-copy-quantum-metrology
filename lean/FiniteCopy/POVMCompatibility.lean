import FiniteCopy.Paths
import FiniteCopy.RiskTerminal
open scoped BigOperators
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths
open ClebschGordan FiniteCopy.POVM

lemma povm_raising_eq (n : ℕ) :
    raising n (FiniteCopy.Algebra.spinEdge n) = raisingMatrix (spinCoefficient n) := by
  unfold raising raisingMatrix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h₀ : vertex n i.val = i.castSucc := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (by omega : i.val ≤ n)]
  have h₁ : vertex n (i.val+1) = i.succ := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (by omega : i.val+1 ≤ n)]
  simp [h₀, h₁, FiniteCopy.Algebra.spinEdge, spinCoefficient]

lemma povm_lowering_eq (n : ℕ) :
    lowering n (FiniteCopy.Algebra.spinEdge n) = loweringMatrix (spinCoefficient n) := by
  unfold lowering loweringMatrix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h₀ : vertex n i.val = i.castSucc := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (by omega : i.val ≤ n)]
  have h₁ : vertex n (i.val+1) = i.succ := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (by omega : i.val+1 ≤ n)]
  simp [h₀, h₁, FiniteCopy.Algebra.spinEdge, spinCoefficient]

lemma tangentX_eq_spinX (n : ℕ) : tangentX n (FiniteCopy.Algebra.spinEdge n) =
    (2 / (n+1 : ℝ)) • spinX (spinCoefficient n) := by
  rw [tangentX, povm_raising_eq, povm_lowering_eq]
  ext i j
  simp [spinX, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

lemma tangentY_eq_spinY (n : ℕ) : tangentY n (FiniteCopy.Algebra.spinEdge n) =
    (2 / (n+1 : ℝ)) • spinY (spinCoefficient n) := by
  rw [tangentY, povm_raising_eq, povm_lowering_eq]
  ext i j
  simp [spinY, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

end CopyQuantumMetrology.SpinPaths
