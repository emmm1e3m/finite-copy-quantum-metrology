import FiniteCopy.Paths
open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths
open ClebschGordan

def sourceEquiv (S : Signature) : S.Space × Fin 2 ≃ Σ b : S.Block, Input (S.spin b) where
  toFun p := ⟨p.1.1, (p.1.2,p.2)⟩
  invFun p := (⟨p.1,p.2.1⟩,p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def targetEquiv (S : Signature) : S.next.Space ≃ Σ b : S.Block, Output (S.spin b) where
  toFun p := match p with
    | ⟨Sum.inl b,i⟩ => ⟨b, Sum.inl i⟩
    | ⟨Sum.inr b,i⟩ => ⟨b.val, Sum.inr (Fin.cast (Nat.sub_add_cancel b.property) i)⟩
  invFun p := match p with
    | ⟨b,Sum.inl i⟩ => ⟨Sum.inl b,i⟩
    | ⟨b,Sum.inr i⟩ =>
      have h : 0 < S.spin b := by have hi := i.isLt; omega
      ⟨Sum.inr ⟨b,h⟩, Fin.cast (Nat.sub_add_cancel h).symm i⟩
  left_inv p := by
    rcases p with ⟨b,i⟩
    rcases b with b | ⟨b,h⟩
    · rfl
    · congr 1
  right_inv p := by
    rcases p with ⟨b,i⟩
    rcases i with i | i
    · rfl
    · congr 2

def nextCG (S : Signature) : Matrix (S.Space × Fin 2) S.next.Space ℂ := by
  classical
  exact (Matrix.blockDiagonal' (fun b => CG (S.spin b))).submatrix
    (sourceEquiv S) (targetEquiv S)

@[simp] theorem targetEquiv_up (S : Signature) (b : S.Block) (i : Fin (S.spin b+2)) :
    targetEquiv S ⟨Sum.inl b,i⟩ = ⟨b,Sum.inl i⟩ := rfl

@[simp] theorem targetEquiv_down (S : Signature) (b : S.Block) (h : 0<S.spin b)
    (i : Fin (S.spin b-1+1)) :
    targetEquiv S ⟨Sum.inr ⟨b,h⟩,i⟩ =
      ⟨b,Sum.inr (Fin.cast (Nat.sub_add_cancel h) i)⟩ := rfl

lemma blockCG_left (S : Signature) :
    (Matrix.blockDiagonal' (fun b => CG (S.spin b)))ᴴ *
      Matrix.blockDiagonal' (fun b => CG (S.spin b)) = 1 := by
  classical
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp only [CG_conjTranspose_mul]
  exact Matrix.blockDiagonal'_one

lemma blockCG_right (S : Signature) :
    Matrix.blockDiagonal' (fun b => CG (S.spin b)) *
      (Matrix.blockDiagonal' (fun b => CG (S.spin b)))ᴴ = 1 := by
  classical
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp only [CG_mul_conjTranspose]
  exact Matrix.blockDiagonal'_one

theorem nextCG_left (S : Signature) : (nextCG S)ᴴ * nextCG S = 1 := by
  classical
  rw [nextCG, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, blockCG_left, Matrix.submatrix_one_equiv]

theorem nextCG_right (S : Signature) : nextCG S * (nextCG S)ᴴ = 1 := by
  classical
  rw [nextCG, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, blockCG_right, Matrix.submatrix_one_equiv]

end CopyQuantumMetrology.SpinPaths
