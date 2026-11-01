import FiniteCopy.Intertwining

open scoped BigOperators Kronecker
open Matrix
noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

def complexR (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (R n).map Complex.ofReal

def complexTensorR (n : ℕ) : Matrix (Input n) (Input n) ℂ :=
  (tensorR n).map Complex.ofReal

def complexBlockR (n : ℕ) : Matrix (Output (n+1)) (Output (n+1)) ℂ :=
  (blockR n).map Complex.ofReal

theorem CG_raising_succ (n : ℕ) :
    complexTensorR (n+1) * CG (n+1) = CG (n+1) * complexBlockR n := by
  ext p q
  have h := congrArg (fun M => (M p q : ℂ)) (realCG_raising_succ n)
  simpa only [complexTensorR, CG, complexBlockR, Matrix.mul_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul] using h

lemma adjoint_intertwining {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (C : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (h₁ : Cᴴ*C = 1) (h₂ : C*Cᴴ = 1) (h : A*C = C*B) :
    Aᴴ*C = C*Bᴴ := by
  have ht := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at ht
  calc
    _ = C * (Cᴴ*Aᴴ) * C := by simp [← Matrix.mul_assoc, h₂]
    _ = C * (Bᴴ*Cᴴ) * C := by rw [ht]
    _ = _ := by simp [Matrix.mul_assoc, h₁]

theorem CG_lowering_succ (n : ℕ) :
    (complexTensorR (n+1))ᴴ * CG (n+1) = CG (n+1) * (complexBlockR n)ᴴ :=
  adjoint_intertwining _ _ _ (CG_conjTranspose_mul _) (CG_mul_conjTranspose _)
    (CG_raising_succ n)

def Jx (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (2 : ℂ)⁻¹ • (complexR n + (complexR n)ᴴ)

def Jy (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (-Complex.I / 2) • (complexR n - (complexR n)ᴴ)

def tensorJx (n : ℕ) : Matrix (Input n) (Input n) ℂ :=
  Jx n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
  (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ Jx 1

def tensorJy (n : ℕ) : Matrix (Input n) (Input n) ℂ :=
  Jy n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
  (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ Jy 1

lemma complexTensorR_eq (n : ℕ) : complexTensorR n =
    complexR n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ⊗ₖ complexR 1 := by
  ext ⟨i,b⟩ ⟨j,c⟩
  by_cases hij : i = j <;> by_cases hbc : b = c <;>
    simp [complexTensorR, tensorR, complexR, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hij, hbc]

lemma complexBlockR_eq (n : ℕ) : complexBlockR n =
    Matrix.fromBlocks (complexR (n+2)) 0 0 (complexR n) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [complexBlockR, blockR, complexR, Matrix.fromBlocks]

lemma tensorJx_fromR (n : ℕ) : tensorJx n =
    (2 : ℂ)⁻¹ • (complexTensorR n + (complexTensorR n)ᴴ) := by
  rw [complexTensorR_eq]
  simp only [tensorJx, Jx, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.add_kronecker, Matrix.kronecker_add, smul_add]
  abel

lemma tensorJy_fromR (n : ℕ) : tensorJy n =
    (-Complex.I / 2) • (complexTensorR n - (complexTensorR n)ᴴ) := by
  rw [complexTensorR_eq]
  ext ⟨i,b⟩ ⟨j,c⟩
  by_cases hij : i = j <;> by_cases hbc : b = c <;>
    simp [tensorJy, Jy, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, hij, hbc, eq_comm] <;> ring

theorem CG_Jx_succ (n : ℕ) : tensorJx (n+1) * CG (n+1) =
    CG (n+1) * Matrix.fromBlocks (Jx (n+2)) 0 0 (Jx n) := by
  rw [tensorJx_fromR, Matrix.smul_mul, Matrix.add_mul,
    CG_raising_succ, CG_lowering_succ, ← Matrix.mul_add, ← Matrix.mul_smul]
  congr 1
  rw [complexBlockR_eq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Jx, Matrix.fromBlocks, Matrix.conjTranspose_apply] <;> ring

theorem CG_Jy_succ (n : ℕ) : tensorJy (n+1) * CG (n+1) =
    CG (n+1) * Matrix.fromBlocks (Jy (n+2)) 0 0 (Jy n) := by
  rw [tensorJy_fromR, Matrix.smul_mul, Matrix.sub_mul,
    CG_raising_succ, CG_lowering_succ, ← Matrix.mul_sub, ← Matrix.mul_smul]
  congr 1
  rw [complexBlockR_eq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Jy, Matrix.fromBlocks, Matrix.conjTranspose_apply]

-- n=0 的 minus 空间为空；以依赖匹配统一表示全部自旋。
def outputR : (n : ℕ) → Matrix (Output n) (Output n) ℂ
  | 0 => blockRzero.map Complex.ofReal
  | n+1 => complexBlockR n

def outputJx (n : ℕ) : Matrix (Output n) (Output n) ℂ :=
  (2 : ℂ)⁻¹ • (outputR n + (outputR n)ᴴ)

def outputJy (n : ℕ) : Matrix (Output n) (Output n) ℂ :=
  (-Complex.I / 2) • (outputR n - (outputR n)ᴴ)

theorem CG_raising (n : ℕ) : complexTensorR n * CG n = CG n * outputR n := by
  cases n with
  | zero =>
    ext p q
    have h := congrArg (fun M => (M p q : ℂ)) realCG_raising_zero
    simpa only [complexTensorR, CG, outputR, Matrix.mul_apply, Matrix.map_apply,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  | succ n => exact CG_raising_succ n

theorem CG_lowering (n : ℕ) : (complexTensorR n)ᴴ * CG n = CG n * (outputR n)ᴴ :=
  adjoint_intertwining _ _ _ (CG_conjTranspose_mul _) (CG_mul_conjTranspose _)
    (CG_raising n)

theorem CG_Jx (n : ℕ) : tensorJx n * CG n = CG n * outputJx n := by
  rw [tensorJx_fromR, outputJx, Matrix.smul_mul, Matrix.add_mul,
    CG_raising, CG_lowering, ← Matrix.mul_add, ← Matrix.mul_smul]

theorem CG_Jy (n : ℕ) : tensorJy n * CG n = CG n * outputJy n := by
  rw [tensorJy_fromR, outputJy, Matrix.smul_mul, Matrix.sub_mul,
    CG_raising, CG_lowering, ← Matrix.mul_sub, ← Matrix.mul_smul]

theorem outputJx_succ (n : ℕ) : outputJx (n+1) =
    Matrix.fromBlocks (Jx (n+2)) 0 0 (Jx n) := by
  rw [outputJx, outputR, complexBlockR_eq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Jx, Matrix.fromBlocks, Matrix.conjTranspose_apply] <;> ring

theorem outputJy_succ (n : ℕ) : outputJy (n+1) =
    Matrix.fromBlocks (Jy (n+2)) 0 0 (Jy n) := by
  rw [outputJy, outputR, complexBlockR_eq]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [Jy, Matrix.fromBlocks, Matrix.conjTranspose_apply]

theorem outputJx_zero : outputJx 0 =
    Matrix.fromBlocks (Jx 1) 0 0 (0 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · simp [outputJx, outputR, blockRzero, Jx, complexR, Matrix.fromBlocks,
      Matrix.conjTranspose_apply] <;> ring
  · exact Fin.elim0 q
  · exact Fin.elim0 p
  · exact Fin.elim0 p

theorem outputJy_zero : outputJy 0 =
    Matrix.fromBlocks (Jy 1) 0 0 (0 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · simp [outputJy, outputR, blockRzero, Jy, complexR, Matrix.fromBlocks,
      Matrix.conjTranspose_apply]
  · exact Fin.elim0 q
  · exact Fin.elim0 p
  · exact Fin.elim0 p

end CopyQuantumMetrology.ClebschGordan

