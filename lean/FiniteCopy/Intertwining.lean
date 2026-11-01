import FiniteCopy.Coefficients

open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

def plus (n : ℕ) : Matrix (Input n) (Fin (n+2)) ℝ :=
  (realCG n).submatrix id Sum.inl

def minus (n : ℕ) : Matrix (Input n) (Fin n) ℝ :=
  (realCG n).submatrix id Sum.inr

lemma plus_zero (n : ℕ) (i : Fin (n+1)) (l : Fin (n+2)) :
    plus n (i,0) l = if i.val = l.val then a n l.val else 0 := by
  simp only [plus, Matrix.submatrix_apply, id_eq, realCG, ↓reduceIte,
    Fin.ext_iff, Fin.val_castSucc]

lemma plus_one (n : ℕ) (i : Fin (n+1)) (l : Fin (n+2)) :
    plus n (i,1) l = if i.val+1 = l.val then b n l.val else 0 := by
  simp only [plus, Matrix.submatrix_apply, id_eq, realCG,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, Fin.ext_iff, Fin.val_succ]

lemma minus_zero (n : ℕ) (i : Fin (n+1)) (k : Fin n) :
    minus n (i,0) k = if k.val+1 = i.val then -b n (k.val+1) else 0 := by
  simp only [minus, Matrix.submatrix_apply, id_eq, realCG, ↓reduceIte,
    Fin.ext_iff, Fin.val_succ]

lemma minus_one (n : ℕ) (i : Fin (n+1)) (k : Fin n) :
    minus n (i,1) k = if k.val = i.val then a n (k.val+1) else 0 := by
  simp only [minus, Matrix.submatrix_apply, id_eq, realCG,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, Fin.ext_iff, Fin.val_castSucc]

theorem plus_intertwining (n : ℕ) : tensorR n * plus n = plus n * R (n+1) := by
  ext ⟨i,q⟩ l
  fin_cases q
  · change (tensorR n * plus n) (i,0) l = (plus n * R (n+1)) (i,0) l
    rw [tensorR_mul_zero]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [R_mul_zero]
      refine Fin.lastCases ?_ (fun k => ?_) l
      · rw [mul_R_last]
      · rw [mul_R_castSucc]
        simp [plus_zero]
    · rw [R_mul_succ]
      refine Fin.lastCases ?_ (fun k => ?_) l
      · rw [mul_R_last]
        simp only [Matrix.submatrix_apply, id_eq, plus_zero, Fin.val_castSucc, Fin.val_last]
        have h : r.val ≠ n+1 := by omega
        simp [h]
      · rw [mul_R_castSucc]
        simp only [Matrix.submatrix_apply, id_eq, plus_zero, Fin.val_castSucc,
          Fin.val_succ, Nat.add_left_inj]
        by_cases h : r.val = k.val
        · rw [← h]
          simpa [mul_comm] using edge_a_plus n r.val
        · simp [h]
  · change (tensorR n * plus n) (i,1) l = (plus n * R (n+1)) (i,1) l
    rw [tensorR_mul_one]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [R_mul_zero, zero_add]
      refine Fin.lastCases ?_ (fun k => ?_) l
      · rw [mul_R_last]
        simp [plus_zero]
      · rw [mul_R_castSucc]
        simp only [plus_zero, plus_one, Fin.val_zero, Fin.val_castSucc,
          Fin.val_succ, Nat.add_left_inj]
        by_cases h : k.val = 0
        · simpa [h, mul_comm] using edge_plus_zero n
        · simp [h, Ne.symm h]
    · rw [R_mul_succ]
      refine Fin.lastCases ?_ (fun k => ?_) l
      · rw [mul_R_last]
        simp only [Matrix.submatrix_apply, id_eq, plus_one, plus_zero,
          Fin.val_castSucc, Fin.val_succ, Fin.val_last]
        have h : r.val+1 ≠ n+1 := by omega
        have hr : r.val ≠ n := by omega
        simp [h, hr]
      · rw [mul_R_castSucc]
        simp only [Matrix.submatrix_apply, id_eq, plus_one, plus_zero,
          Fin.val_castSucc, Fin.val_succ, Nat.add_left_inj]
        by_cases h : r.val+1 = k.val
        · rw [← h]
          simpa [mul_comm, Nat.add_assoc] using edge_b_plus n r.val
        · simp [h]

theorem minus_intertwining (n : ℕ) :
    tensorR (n+1) * minus (n+1) = minus (n+1) * R n := by
  ext ⟨i,q⟩ k
  fin_cases q
  · change (tensorR (n+1) * minus (n+1)) (i,0) k = (minus (n+1) * R n) (i,0) k
    rw [tensorR_mul_zero]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [R_mul_zero]
      refine Fin.lastCases ?_ (fun t => ?_) k
      · rw [mul_R_last]
      · rw [mul_R_castSucc]
        simp [minus_zero]
    · rw [R_mul_succ]
      refine Fin.lastCases ?_ (fun t => ?_) k
      · rw [mul_R_last]
        simp only [Matrix.submatrix_apply, id_eq, minus_zero, Fin.val_castSucc, Fin.val_last]
        have h : n+1 ≠ r.val := by omega
        simp [h]
      · rw [mul_R_castSucc]
        simp only [Matrix.submatrix_apply, id_eq, minus_zero, Fin.val_castSucc,
          Fin.val_succ, Nat.add_left_inj]
        by_cases h : t.val+1 = r.val
        · rw [← h]
          simpa [mul_comm, Nat.add_assoc] using congrArg Neg.neg (edge_b_minus n t.val)
        · simp [h]
  · change (tensorR (n+1) * minus (n+1)) (i,1) k = (minus (n+1) * R n) (i,1) k
    rw [tensorR_mul_one]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [R_mul_zero, zero_add]
      refine Fin.lastCases ?_ (fun t => ?_) k
      · rw [mul_R_last]
        simp [minus_zero]
      · rw [mul_R_castSucc]
        simp [minus_zero, minus_one]
    · rw [R_mul_succ]
      refine Fin.lastCases ?_ (fun t => ?_) k
      · rw [mul_R_last]
        simp only [Matrix.submatrix_apply, id_eq, minus_zero, minus_one,
          Fin.val_castSucc, Fin.val_succ, Fin.val_last, Nat.add_left_inj]
        by_cases h : n = r.val
        · rw [← h]
          have hh := edge_a_minus n n (le_refl n)
          simpa [edge, sub_eq_add_neg] using hh
        · simp [h]
      · rw [mul_R_castSucc]
        simp only [Matrix.submatrix_apply, id_eq, minus_zero, minus_one,
          Fin.val_castSucc, Fin.val_succ, Nat.add_left_inj]
        by_cases h : t.val = r.val
        · rw [← h]
          simpa [mul_comm, Nat.add_assoc, sub_eq_add_neg] using edge_a_minus n t.val (by omega)
        · simp [h]

def blockR (n : ℕ) : Matrix (Output (n+1)) (Output (n+1)) ℝ :=
  Matrix.fromBlocks (R (n+2)) 0 0 (R n)

theorem realCG_raising_succ (n : ℕ) :
    tensorR (n+1) * realCG (n+1) = realCG (n+1) * blockR n := by
  ext p q
  rcases q with l | k
  · have h := congrArg (fun M => M p l) (plus_intertwining (n+1))
    simpa [Matrix.mul_apply, plus, Matrix.submatrix_apply, Fintype.sum_sum_type,
      blockR, Matrix.fromBlocks] using h
  · have h := congrArg (fun M => M p k) (minus_intertwining n)
    simpa [Matrix.mul_apply, minus, Matrix.submatrix_apply, Fintype.sum_sum_type,
      blockR, Matrix.fromBlocks] using h

def blockRzero : Matrix (Output 0) (Output 0) ℝ :=
  Matrix.fromBlocks (R 1) 0 0 (0 : Matrix (Fin 0) (Fin 0) ℝ)

theorem realCG_raising_zero :
    tensorR 0 * realCG 0 = realCG 0 * blockRzero := by
  ext p q
  rcases q with l | k
  · have h := congrArg (fun M => M p l) (plus_intertwining 0)
    simpa [Matrix.mul_apply, plus, Matrix.submatrix_apply, Fintype.sum_sum_type,
      blockRzero, Matrix.fromBlocks] using h
  · exact Fin.elim0 k

end CopyQuantumMetrology.ClebschGordan

