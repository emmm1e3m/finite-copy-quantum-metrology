import FiniteCopy.NextCG
open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.SpinPaths
open ClebschGordan

def spinOp (a : Fin 2) (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  if a = 0 then Jx n else Jy n

def outOp (a : Fin 2) (n : ℕ) : Matrix (Output n) (Output n) ℂ :=
  if a = 0 then outputJx n else outputJy n

def tensorOp (a : Fin 2) (n : ℕ) : Matrix (Input n) (Input n) ℂ :=
  spinOp a n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ spinOp a 1

def diagOp (S : Signature) (a : Fin 2) : Matrix S.Space S.Space ℂ :=
  Matrix.blockDiagonal' (fun b => spinOp a (S.spin b))

lemma local_intertwining (a : Fin 2) (n : ℕ) : tensorOp a n * CG n = CG n * outOp a n := by
  fin_cases a
  · exact CG_Jx n
  · exact CG_Jy n

lemma outOp_up (a : Fin 2) (n : ℕ) (i j : Fin (n+2)) :
    outOp a n (Sum.inl i) (Sum.inl j) = spinOp a (n+1) i j := by
  cases n <;> fin_cases a <;>
    simp [outOp, spinOp, outputJx_zero, outputJy_zero, outputJx_succ, outputJy_succ]

lemma outOp_up_down (a : Fin 2) (n : ℕ) (i : Fin (n+2)) (j : Fin n) :
    outOp a n (Sum.inl i) (Sum.inr j) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => fin_cases a <;> simp [outOp, outputJx_succ, outputJy_succ]

lemma outOp_down_up (a : Fin 2) (n : ℕ) (i : Fin n) (j : Fin (n+2)) :
    outOp a n (Sum.inr i) (Sum.inl j) = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => fin_cases a <;> simp [outOp, outputJx_succ, outputJy_succ]

lemma outOp_down (a : Fin 2) (n : ℕ) (h : 0<n) (i j : Fin (n-1+1)) :
    outOp a n (Sum.inr (Fin.cast (Nat.sub_add_cancel h) i))
      (Sum.inr (Fin.cast (Nat.sub_add_cancel h) j)) = spinOp a (n-1) i j := by
  cases n with
  | zero => omega
  | succ n => fin_cases a <;> simp [outOp, spinOp, outputJx_succ, outputJy_succ]

lemma source_operator (S : Signature) (a : Fin 2) :
    (Matrix.blockDiagonal' (fun b => tensorOp a (S.spin b))).submatrix
      (sourceEquiv S) (sourceEquiv S) =
    diagOp S a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix S.Space S.Space ℂ) ⊗ₖ spinOp a 1 := by
  classical
  ext ⟨⟨b,i⟩,u⟩ ⟨⟨c,j⟩,v⟩
  by_cases h : b = c
  · subst c
    simp [sourceEquiv, diagOp, tensorOp, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Sigma.mk.inj_iff]
  · simp [sourceEquiv, diagOp, Matrix.blockDiagonal'_apply, h,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Sigma.mk.inj_iff]

set_option backward.isDefEq.respectTransparency false in
lemma target_operator (S : Signature) (a : Fin 2) :
    (Matrix.blockDiagonal' (fun b => outOp a (S.spin b))).submatrix
      (targetEquiv S) (targetEquiv S) = diagOp S.next a := by
  classical
  ext ⟨b,i⟩ ⟨c,j⟩
  rcases b with b | ⟨b,hb⟩ <;> rcases c with c | ⟨c,hc⟩
  · change (Matrix.blockDiagonal' (fun d => outOp a (S.spin d)))
      ⟨b,Sum.inl i⟩ ⟨c,Sum.inl j⟩ = _
    by_cases h : b = c
    · subst c
      simpa [diagOp, Signature.next, Matrix.submatrix_apply] using outOp_up a (S.spin b) i j
    · simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h]
  · change (Matrix.blockDiagonal' (fun d => outOp a (S.spin d)))
      ⟨b,Sum.inl i⟩ ⟨c,Sum.inr (Fin.cast (Nat.sub_add_cancel hc) j)⟩ = _
    by_cases h : b = c
    · subst c
      simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, outOp_up_down]
    · simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h]
  · change (Matrix.blockDiagonal' (fun d => outOp a (S.spin d)))
      ⟨b,Sum.inr (Fin.cast (Nat.sub_add_cancel hb) i)⟩ ⟨c,Sum.inl j⟩ = _
    by_cases h : b = c
    · subst c
      simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, outOp_down_up]
    · simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h]
  · change (Matrix.blockDiagonal' (fun d => outOp a (S.spin d)))
      ⟨b,Sum.inr (Fin.cast (Nat.sub_add_cancel hb) i)⟩
      ⟨c,Sum.inr (Fin.cast (Nat.sub_add_cancel hc) j)⟩ = _
    by_cases h : b = c
    · subst c
      simpa [diagOp, Signature.next, Matrix.submatrix_apply] using outOp_down a (S.spin b) hb i j
    · simp [diagOp, Signature.next, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, h,
        Subtype.mk.injEq]

theorem nextCG_intertwining (S : Signature) (a : Fin 2) :
    (diagOp S a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix S.Space S.Space ℂ) ⊗ₖ spinOp a 1) * nextCG S =
      nextCG S * diagOp S.next a := by
  classical
  rw [← source_operator, ← target_operator, nextCG,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  simp_rw [local_intertwining]

end CopyQuantumMetrology.SpinPaths
