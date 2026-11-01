import FiniteCopy.Embeddings
import FiniteCopy.TensorRecursion
open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths
open ClebschGordan TensorModel

def collectiveAxes (N : ℕ) (a : Fin 2) : NMatrix N :=
  if a = 0 then collectiveX N else collectiveY N

lemma collectiveAxes_succ (N : ℕ) (a : Fin 2) :
    collectiveAxes (N+1) a =
      (tensorOperators (collectiveAxes N) a).submatrix (splitLast N) (splitLast N) := by
  fin_cases a
  · simpa [collectiveAxes, tensorOperators, spinOp, qubit_Jx, sigmaX] using
      collectiveX_succ_right N
  · simpa [collectiveAxes, tensorOperators, spinOp, qubit_Jy, sigmaY] using
      collectiveY_succ_right N

set_option backward.isDefEq.respectTransparency false in
def zeroFrame : Frame (Bits 0) (signature 0) (collectiveAxes 0) where
  basis := Matrix.of (fun _ _ => 1)
  left := by
    ext i j
    letI : Subsingleton (signature 0).Space := by
      change Subsingleton (Σ _ : PUnit, Fin 1)
      refine ⟨?_⟩
      rintro ⟨⟨⟩,u⟩ ⟨⟨⟩,v⟩
      have huv : u = v := Subsingleton.elim _ _
      cases huv
      rfl
    have he : i = j := Subsingleton.elim _ _
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, he, Bits]
  right := by
    ext i j
    have he : i = j := Subsingleton.elim _ _
    change (∑ q : (signature 0).Space, (1 : ℂ) * star (1 : ℂ)) =
      (1 : NMatrix 0) i j
    change (∑ q : (Σ _ : PUnit, Fin 1), (1 : ℂ) * star (1 : ℂ)) = _
    simp [Matrix.one_apply, he, Fintype.sum_sigma]
  intertwine a := by
    have hd : diagOp (signature 0) a = 0 := by
      have hz : spinOp a 0 = 0 := by
        have hr : complexR 0 = 0 := by simp [complexR, R]
        simp [spinOp, Jx, Jy, hr]
      ext p q
      simp [diagOp, hz, Matrix.blockDiagonal'_apply]
    simp [collectiveAxes, collectiveX, collectiveY, hd]

def actualFrame : (N : ℕ) → Frame (Bits N) (signature N) (collectiveAxes N)
  | 0 => zeroFrame
  | N+1 =>
    let G := ((actualFrame N).next).reindex (splitLast N)
    { basis := G.basis
      left := G.left
      right := G.right
      intertwine := fun a => by rw [collectiveAxes_succ]; exact G.intertwine a }

def U (N : ℕ) (b : B N) : Matrix (Bits N) (Fin (spin N b+1)) ℂ :=
  (actualFrame N).embedding b

theorem U_isometry (N : ℕ) (b : B N) : (U N b)ᴴ * U N b = 1 :=
  (actualFrame N).embedding_isometry b

theorem U_orthogonal (N : ℕ) (b c : B N) (h : b ≠ c) : (U N b)ᴴ * U N c = 0 :=
  (actualFrame N).embedding_orthogonal b c h

theorem U_complete (N : ℕ) : ∑ b, U N b * (U N b)ᴴ = 1 :=
  (actualFrame N).embedding_complete

theorem collective_decomposition (N : ℕ) (a : Fin 2) :
    collectiveAxes N a = ∑ b, U N b * spinOp a (spin N b) * (U N b)ᴴ :=
  (actualFrame N).operator_decomposition a

theorem collectiveX_decomposition (N : ℕ) : collectiveX N =
    ∑ b, U N b * spinX (spinCoefficient (spin N b)) * (U N b)ᴴ := by
  simpa [collectiveAxes, spinOp, Jx_eq_spinX] using collective_decomposition N 0

theorem collectiveY_decomposition (N : ℕ) : collectiveY N =
    ∑ b, U N b * spinY (spinCoefficient (spin N b)) * (U N b)ᴴ := by
  simpa [collectiveAxes, spinOp, Jy_eq_spinY] using collective_decomposition N 1

end CopyQuantumMetrology.SpinPaths
