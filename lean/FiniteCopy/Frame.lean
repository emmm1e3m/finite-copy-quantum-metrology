import FiniteCopy.Operators
open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths

structure Frame (ι : Type) [Fintype ι] [DecidableEq ι] (S : Signature)
    (A : Fin 2 → Matrix ι ι ℂ) where
  basis : Matrix ι S.Space ℂ
  left : basisᴴ * basis = 1
  right : basis * basisᴴ = 1
  intertwine : ∀ a, A a * basis = basis * diagOp S a

def tensorOperators {ι : Type} [DecidableEq ι]
    (A : Fin 2 → Matrix ι ι ℂ) (a : Fin 2) : Matrix (ι × Fin 2) (ι × Fin 2) ℂ :=
  A a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ spinOp a 1

namespace Frame
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Signature}
variable {A : Fin 2 → Matrix ι ι ℂ} (F : Frame ι S A)

def tensorBasis : Matrix (ι × Fin 2) (S.Space × Fin 2) ℂ :=
  F.basis ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

lemma tensorBasis_left : F.tensorBasisᴴ * F.tensorBasis = 1 := by
  rw [tensorBasis, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, F.left, Matrix.one_mul, Matrix.one_kronecker_one]

lemma tensorBasis_right : F.tensorBasis * F.tensorBasisᴴ = 1 := by
  rw [tensorBasis, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, F.right, Matrix.one_mul, Matrix.one_kronecker_one]

lemma tensorBasis_intertwine (a : Fin 2) :
    tensorOperators A a * F.tensorBasis = F.tensorBasis *
      (diagOp S a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix S.Space S.Space ℂ) ⊗ₖ spinOp a 1) := by
  simp only [tensorOperators, tensorBasis, Matrix.add_mul, Matrix.mul_add,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, F.intertwine]

def next : Frame (ι × Fin 2) S.next (tensorOperators A) where
  basis := F.tensorBasis * nextCG S
  left := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = (nextCG S)ᴴ * (F.tensorBasisᴴ * F.tensorBasis) * nextCG S := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.tensorBasis_left, Matrix.mul_one, nextCG_left]
  right := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = F.tensorBasis * (nextCG S * (nextCG S)ᴴ) * F.tensorBasisᴴ := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nextCG_right, Matrix.mul_one, F.tensorBasis_right]
  intertwine a := by
    rw [← Matrix.mul_assoc, F.tensorBasis_intertwine, Matrix.mul_assoc,
      nextCG_intertwining, ← Matrix.mul_assoc]

def reindex {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) :
    Frame κ S (fun a => (A a).submatrix e e) where
  basis := F.basis.submatrix e id
  left := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, F.left]
    simp
  right := by
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul F.basis F.basisᴴ e id e Function.bijective_id, F.right,
      Matrix.submatrix_one_equiv]
  intertwine a := by
    rw [Matrix.submatrix_mul_equiv, F.intertwine]
    exact (Matrix.submatrix_mul F.basis (diagOp S a) e id id Function.bijective_id).symm

end Frame
end CopyQuantumMetrology.SpinPaths
