import FiniteCopy.NHBlockSDP
import FiniteCopy.ChainCertificate
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def axisX (C : Mat ι) : Mat ι := (1/2:ℝ) • (C+Cᴴ)
def axisY (C : Mat ι) : Mat ι := (-Complex.I/2) • (C-Cᴴ)

-- 等价于ρ=I/D、两切向2Jx/D和2Jy/D下的全部零均值与局部无偏约束。
structure FirstMomentFeasible (D : ℝ) (C X Y : Mat ι) : Prop where
  hermitianX : X.IsHermitian
  hermitianY : Y.IsHermitian
  meanX : tr X=0
  meanY : tr Y=0
  xx : tr (X*axisX C)=D/2
  xy : tr (X*axisY C)=0
  yx : tr (Y*axisX C)=0
  yy : tr (Y*axisY C)=D/2

def nhValues (D : ℝ) (C : Mat ι) : Set ℝ :=
  {v | ∃ X Y : Mat ι, FirstMomentFeasible D C X Y ∧ v ∈ nhBlockValues X Y}

def nhRisk (N D : ℝ) (C : Mat ι) : ℝ := (N/D)*sInf (nhValues D C)

-- 任意有限自旋块族；每个重数副本作为独立的块标签。
def blockRaising {B : Type*} [DecidableEq B] (n : B → ℕ) (x : B → ℕ → ℝ) :
    Matrix (Σ b:B,Fin (n b+1)) (Σ b:B,Fin (n b+1)) ℂ :=
  Matrix.blockDiagonal' (fun b=>raiseMatrix (n b) (x b))




lemma axisX_hermitian (C : Mat ι) : (axisX C).IsHermitian := by
  simp [axisX, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

lemma axisY_hermitian (C : Mat ι) : (axisY C).IsHermitian := by
  simp only [axisY, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  ext i j
  simp [Matrix.smul_apply, Complex.star_def]
  ring

lemma complexMoment_axes (C : Mat ι) : complexMoment (axisX C) (axisY C) = C := by
  ext i j
  simp [complexMoment, axisX, axisY, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma trace_adjoint_right (X C : Mat ι) (hX : X.IsHermitian) :
    Matrix.trace (X*Cᴴ) = star (Matrix.trace (X*C)) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq, Matrix.trace_mul_comm]

lemma pairing_trace (c : Matrix ι ι ℝ) (Z : Mat ι) :
    matrixPairing c Z = tr ((c.map Complex.ofReal)ᴴ*Z) := by
  simp only [matrixPairing, tr, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma combined_firstMoment (D : ℝ) (c : Matrix ι ι ℝ) (X Y : Mat ι)
    (h : FirstMomentFeasible D (c.map Complex.ofReal) X Y) :
    matrixPairing c (complexMoment X Y) = D := by
  let C := c.map Complex.ofReal
  have hx := trace_adjoint_right X C h.hermitianX
  have hy := trace_adjoint_right Y C h.hermitianY
  have hxx := h.xx
  have hyy := h.yy
  rw [pairing_trace]
  simp only [tr, complexMoment, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm Cᴴ X, Matrix.trace_mul_comm Cᴴ Y, hx, hy]
  simp only [tr, axisX, axisY, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, smul_eq_mul] at hxx hyy
  rw [hx] at hxx
  rw [hy] at hyy
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im] at hxx hyy ⊢
  linarith

lemma axes_firstMoment (D : ℝ) (C A : Mat ι)
    (hA : Matrix.trace A = 0) (hAC : Matrix.trace (A*C)=0)
    (hAdC : Matrix.trace (Aᴴ*C)=(D:ℂ)) :
    FirstMomentFeasible D C (axisX A) (axisY A) := by
  have hACd : Matrix.trace (A*Cᴴ)=(D:ℂ) := by
    have he := congrArg star hAdC
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm] at he
    simpa using he
  have hAdCd : Matrix.trace (Aᴴ*Cᴴ)=0 := by
    have he := congrArg star hAC
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,Matrix.trace_mul_comm] at he
    simpa using he
  refine ⟨axisX_hermitian A,axisY_hermitian A,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [tr,axisX,axisY,Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.sub_mul,
      Matrix.mul_add,Matrix.mul_sub,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,
      Matrix.trace_conjTranspose,hA,hAC,hAdC,hACd,hAdCd,Complex.mul_re,Complex.mul_im,
      Complex.star_def] <;> ring

end FiniteCopy.NHOperator
