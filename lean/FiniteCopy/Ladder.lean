import FiniteCopy.ClebschGordan
import Mathlib.Data.Matrix.Basis

open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

def edge (n i : ℕ) : ℝ := Real.sqrt (((i : ℝ)+1) * ((n : ℝ)-i))

def R (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  ∑ r : Fin n, Matrix.single r.succ r.castSucc (edge n r.val)

lemma R_mul_zero {n : ℕ} {κ : Type*} (M : Matrix (Fin (n+1)) κ ℝ) (q : κ) :
    (R n * M) 0 q = 0 := by
  rw [R, Matrix.sum_mul]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  apply Matrix.single_mul_apply_of_ne
  exact Fin.succ_ne_zero r |>.symm

lemma R_mul_succ {n : ℕ} {κ : Type*} (M : Matrix (Fin (n+1)) κ ℝ)
    (r : Fin n) (q : κ) :
    (R n * M) r.succ q = edge n r.val * M r.castSucc q := by
  rw [R, Matrix.sum_mul]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single r]
  · exact Matrix.single_mul_apply_same _ _ _ _ _
  · intro s _ hs
    apply Matrix.single_mul_apply_of_ne
    exact fun h => hs (Fin.succ_injective _ h.symm)
  · simp

lemma mul_R_last {n : ℕ} {κ : Type*} (M : Matrix κ (Fin (n+1)) ℝ) (p : κ) :
    (M * R n) p (Fin.last n) = 0 := by
  rw [R, Matrix.mul_sum]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro r _
  apply Matrix.mul_single_apply_of_ne
  exact Fin.castSucc_ne_last r |>.symm

lemma mul_R_castSucc {n : ℕ} {κ : Type*} (M : Matrix κ (Fin (n+1)) ℝ)
    (r : Fin n) (p : κ) :
    (M * R n) p r.castSucc = M p r.succ * edge n r.val := by
  rw [R, Matrix.mul_sum]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single r]
  · exact Matrix.mul_single_apply_same _ _ _ _ _
  · intro s _ hs
    apply Matrix.mul_single_apply_of_ne
    exact fun h => hs (Fin.castSucc_injective _ h.symm)
  · simp

def tensorR (n : ℕ) : Matrix (Input n) (Input n) ℝ :=
  R n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
  (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) ⊗ₖ R 1

lemma tensorR_mul_zero {n : ℕ} {κ : Type*} (M : Matrix (Input n) κ ℝ)
    (i : Fin (n+1)) (q : κ) :
    (tensorR n * M) (i, 0) q =
      (R n * M.submatrix (fun j => (j,0)) id) i q := by
  simp [tensorR, Matrix.add_mul, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.sum_univ_two,
    R, Fin.sum_univ_one, Matrix.single_apply, edge, Matrix.submatrix_apply]

lemma tensorR_mul_one {n : ℕ} {κ : Type*} (M : Matrix (Input n) κ ℝ)
    (i : Fin (n+1)) (q : κ) :
    (tensorR n * M) (i, 1) q =
      (R n * M.submatrix (fun j => (j,1)) id) i q + M (i,0) q := by
  simp [tensorR, Matrix.add_mul, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.sum_univ_two,
    R, Fin.sum_univ_one, Matrix.single_apply, edge, Finset.sum_add_distrib, add_comm,
    Matrix.submatrix_apply]

end CopyQuantumMetrology.ClebschGordan

