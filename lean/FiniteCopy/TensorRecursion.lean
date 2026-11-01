import FiniteCopy.TensorModel

open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.Elementwise
open Matrix
noncomputable section
namespace CopyQuantumMetrology.TensorModel

-- 将最后一个量子比特拆到右边，直接对接自旋 ⊗ 比特的 CG 方向。
def splitLast (N : ℕ) : Bits (N+1) ≃ Bits N × Qubit where
  toFun b := (fun i => b i.castSucc, b (Fin.last N))
  invFun p := Fin.snoc p.1 p.2
  left_inv b := Fin.snoc_init_self b
  right_inv p := by simp

@[simp] theorem splitLast_apply (N : ℕ) (b : Bits (N+1)) :
    splitLast N b = (fun i => b i.castSucc, b (Fin.last N)) := rfl

theorem tensorPower_succ_right (N : ℕ) (A : QMatrix) (b c : Bits (N+1)) :
    tensorPower (N+1) A b c =
      (tensorPower N A ⊗ₖ A) (splitLast N b) (splitLast N c) := by
  simp only [splitLast_apply, tensorPower, Fin.prod_univ_castSucc, Matrix.kroneckerMap_apply]

theorem tensorPower_succ_right_matrix (N : ℕ) (A : QMatrix) :
    tensorPower (N+1) A =
      (tensorPower N A ⊗ₖ A).submatrix (splitLast N) (splitLast N) := by
  ext b c
  exact tensorPower_succ_right N A b c

-- 乘积法则同时给出集体算符的精确张量递推，避免手工重排 erase 乘积。
theorem sum_onSite_succ_right (N : ℕ) (A : QMatrix) (b c : Bits (N+1)) :
    (∑ r, onSite (N+1) r A) b c =
      (∑ r, onSite N r A) (splitLast N b).1 (splitLast N c).1 *
        (1 : QMatrix) (splitLast N b).2 (splitLast N c).2 +
      (1 : NMatrix N) (splitLast N b).1 (splitLast N c).1 *
        A (splitLast N b).2 (splitLast N c).2 := by
  have hA : HasDerivAt (fun t : ℝ =>
      ((1 : QMatrix) + (t : ℂ) • A) (splitLast N b).2 (splitLast N c).2)
      (A (splitLast N b).2 (splitLast N c).2) 0 := by
    convert (hasDerivAt_const (0 : ℝ)
      ((1 : QMatrix) (splitLast N b).2 (splitLast N c).2)).add
      ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
        (A (splitLast N b).2 (splitLast N c).2)) using 1 <;> simp <;> rfl
  have hN := unnormalized_derivative_entry N A (splitLast N b).1 (splitLast N c).1
  have hp := hN.mul hA
  have he : (fun t : ℝ => tensorPower (N+1) ((1 : QMatrix) + (t : ℂ) • A) b c) =
      (fun t : ℝ => tensorPower N ((1 : QMatrix) + (t : ℂ) • A)
        (splitLast N b).1 (splitLast N c).1 *
        ((1 : QMatrix) + (t : ℂ) • A) (splitLast N b).2 (splitLast N c).2) := by
    funext t
    exact tensorPower_succ_right N _ b c
  have ht := unnormalized_derivative_entry (N+1) A b c
  rw [he] at ht
  have hu := ht.unique hp
  simpa only [Complex.ofReal_zero, zero_smul, add_zero, tensorPower_one] using hu

theorem collective_succ_right (N : ℕ) (A : QMatrix) :
    collective (N+1) A =
      (collective N A ⊗ₖ (1 : QMatrix) +
        (1 : NMatrix N) ⊗ₖ ((2 : ℂ)⁻¹ • A)).submatrix
        (splitLast N) (splitLast N) := by
  ext b c
  simp only [collective, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.kroneckerMap_apply]
  rw [sum_onSite_succ_right]
  ring

@[simp] theorem collective_zero (A : QMatrix) : collective 0 A = 0 := by
  simp [collective]

theorem collectiveX_succ_right (N : ℕ) :
    collectiveX (N+1) =
      (collectiveX N ⊗ₖ (1 : QMatrix) +
        (1 : NMatrix N) ⊗ₖ ((2 : ℂ)⁻¹ • sigmaX)).submatrix
        (splitLast N) (splitLast N) := collective_succ_right N sigmaX

theorem collectiveY_succ_right (N : ℕ) :
    collectiveY (N+1) =
      (collectiveY N ⊗ₖ (1 : QMatrix) +
        (1 : NMatrix N) ⊗ₖ ((2 : ℂ)⁻¹ • sigmaY)).submatrix
        (splitLast N) (splitLast N) := collective_succ_right N sigmaY

end CopyQuantumMetrology.TensorModel





