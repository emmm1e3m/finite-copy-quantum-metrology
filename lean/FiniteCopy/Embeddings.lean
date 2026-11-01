import FiniteCopy.Frame
open scoped BigOperators
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths

namespace Frame
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Signature}
variable {A : Fin 2 → Matrix ι ι ℂ} (F : Frame ι S A)

def embedding (b : S.Block) : Matrix ι (Fin (S.spin b+1)) ℂ :=
  F.basis.submatrix id (fun i => (⟨b,i⟩ : S.Space))

theorem embedding_isometry (b : S.Block) : (F.embedding b)ᴴ * F.embedding b = 1 := by
  ext i j
  have h := congrArg (fun M => M ⟨b,i⟩ ⟨b,j⟩) F.left
  simpa [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem embedding_orthogonal (b c : S.Block) (hbc : b ≠ c) :
    (F.embedding b)ᴴ * F.embedding c = 0 := by
  ext i j
  have h := congrArg (fun M => M ⟨b,i⟩ ⟨c,j⟩) F.left
  have hne : (⟨b,i⟩ : S.Space) ≠ ⟨c,j⟩ := fun he => hbc (congrArg Sigma.fst he)
  simpa [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hne] using h

theorem embedding_complete : ∑ b, F.embedding b * (F.embedding b)ᴴ = 1 := by
  rw [← F.right]
  ext i j
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_sigma]

lemma mul_diag_entry (U : Matrix ι S.Space ℂ)
    (D : ∀ b, Matrix (Fin (S.spin b+1)) (Fin (S.spin b+1)) ℂ)
    (i : ι) (b : S.Block) (j : Fin (S.spin b+1)) :
    (U * Matrix.blockDiagonal' D) i ⟨b,j⟩ = ∑ k, U i ⟨b,k⟩ * D b k j := by
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single b]
  · simp
  · intro c hc
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc, mul_zero]

lemma sandwich_diag (D : ∀ b, Matrix (Fin (S.spin b+1)) (Fin (S.spin b+1)) ℂ) :
    F.basis * Matrix.blockDiagonal' D * F.basisᴴ =
      ∑ b, F.embedding b * D b * (F.embedding b)ᴴ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  change (∑ q : S.Space, (F.basis * Matrix.blockDiagonal' D) i q * star (F.basis j q)) = _
  rw [Fintype.sum_sigma]
  simp_rw [mul_diag_entry]
  simp [embedding, Matrix.conjTranspose_apply]

theorem operator_decomposition (a : Fin 2) :
    A a = ∑ b, F.embedding b * spinOp a (S.spin b) * (F.embedding b)ᴴ := by
  calc
    A a = A a * (F.basis * F.basisᴴ) := by rw [F.right, Matrix.mul_one]
    _ = (A a * F.basis) * F.basisᴴ := by rw [Matrix.mul_assoc]
    _ = (F.basis * diagOp S a) * F.basisᴴ := by rw [F.intertwine]
    _ = _ := F.sandwich_diag _

end Frame
end CopyQuantumMetrology.SpinPaths
