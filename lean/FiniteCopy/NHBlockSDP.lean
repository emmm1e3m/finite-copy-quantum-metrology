import FiniteCopy.MatrixDual
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexMoment (X Y : Mat ι) : Mat ι := X+Complex.I • Y
def squareSum (X Y : Mat ι) : Mat ι := X*X+Y*Y
def commutator (X Y : Mat ι) : Mat ι := Complex.I • (X*Y-Y*X)

lemma complexMoment_adjoint (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (complexMoment X Y)ᴴ = X-Complex.I • Y := by
  simp [complexMoment, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq,hY.eq,
    Complex.star_def, sub_eq_add_neg]

lemma complexMoment_gram (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (complexMoment X Y)ᴴ*complexMoment X Y = squareSum X Y+commutator X Y := by
  rw [complexMoment_adjoint X Y hX hY]
  simp only [complexMoment,squareSum,commutator,Matrix.sub_mul,Matrix.mul_add,Matrix.add_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,neg_one_smul,smul_sub,smul_add]
  abel

lemma complexMoment_otherGram (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    complexMoment X Y*(complexMoment X Y)ᴴ = squareSum X Y-commutator X Y := by
  rw [complexMoment_adjoint X Y hX hY]
  simp only [complexMoment,squareSum,commutator,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,neg_one_smul,smul_sub,smul_add]
  abel

lemma squareSum_hermitian (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (squareSum X Y).IsHermitian := by
  simpa [squareSum,hX.eq,hY.eq] using
    (Matrix.isHermitian_conjTranspose_mul_self X).add (Matrix.isHermitian_conjTranspose_mul_self Y)

lemma commutator_hermitian (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (commutator X Y).IsHermitian := by
  unfold Matrix.IsHermitian commutator
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hX.eq,hY.eq,Complex.star_def,Complex.conj_I]
  ext i j
  simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

-- 辅助矩阵SDP，直接约束交换子；没有把它的值定义成变分目标。
def nhAuxValues (X Y : Mat ι) : Set ℝ := {v | ∃ T : Mat ι,
  T.IsHermitian ∧ (T-commutator X Y).PosSemidef ∧ (T+commutator X Y).PosSemidef ∧
  tr (squareSum X Y+T)=v}

theorem nhAux_eq_upperPrimal (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    nhAuxValues X Y = primalValues ((complexMoment X Y)ᴴ*complexMoment X Y)
      (complexMoment X Y*(complexMoment X Y)ᴴ) := by
  ext v
  constructor
  · rintro ⟨T,hT,hTm,hTp,he⟩
    refine ⟨squareSum X Y+T,?_,he⟩
    rw [complexMoment_gram X Y hX hY,complexMoment_otherGram X Y hX hY]
    constructor
    · convert hTm using 1 <;> abel
    · convert hTp using 1 <;> abel
  · rintro ⟨W,⟨hWP,hWQ⟩,he⟩
    rw [complexMoment_gram X Y hX hY] at hWP
    rw [complexMoment_otherGram X Y hX hY] at hWQ
    have hW : W.IsHermitian := by
      convert hWP.isHermitian.add ((squareSum_hermitian X Y hX hY).add (commutator_hermitian X Y hX hY)) using 1 <;> abel
    refine ⟨W-squareSum X Y,hW.sub (squareSum_hermitian X Y hX hY),?_,?_,?_⟩
    · convert hWP using 1 <;> abel
    · convert hWQ using 1 <;> abel
    · convert he using 1 <;> congr 1 <;> abel

theorem nhAux_minimum (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    IsLeast (nhAuxValues X Y) (operatorObjective (complexMoment X Y)) := by
  rw [nhAux_eq_upperPrimal X Y hX hY]
  exact operatorObjective_primal_minimum _

-- 原两参数NH块SDP：L为实对称的Hermitian算子块，L−XXᵀ为PSD。
def nhSlack (X Y Lx Ly Lxy : Mat ι) : Matrix (ι⊕ι) (ι⊕ι) ℂ :=
  Matrix.fromBlocks (Lx-X*X) (Lxy-X*Y) (Lxy-Y*X) (Ly-Y*Y)

def nhBlockValues (X Y : Mat ι) : Set ℝ := {v | ∃ Lx Ly Lxy : Mat ι,
  Lx.IsHermitian ∧ Ly.IsHermitian ∧ Lxy.IsHermitian ∧
  (nhSlack X Y Lx Ly Lxy).PosSemidef ∧ tr (Lx+Ly)=v}

def parameterColumn (u : ℂ) : Matrix (ι⊕ι) ι ℂ := Matrix.fromRows 1 (u • (1 : Mat ι))

lemma block_compression (A B C D : Mat ι) (u : ℂ) :
    (parameterColumn (ι:=ι) u)ᴴ*Matrix.fromBlocks A B C D*parameterColumn (ι:=ι) u =
      A+u • B+star u • C+(star u*u) • D := by
  simp only [parameterColumn,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one,Matrix.conjTranspose_smul,Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,smul_add, mul_comm u (star u)]
  abel

lemma block_outer (A : Mat ι) (u : ℂ) :
    parameterColumn (ι:=ι) u*A*(parameterColumn (ι:=ι) u)ᴴ =
      Matrix.fromBlocks A (star u • A) (u • A) ((u*star u) • A) := by
  unfold parameterColumn
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul (1 : Mat ι) (u • (1 : Mat ι)) A,
    Matrix.fromRows_mul_fromCols]
  simp only [Matrix.conjTranspose_one,Matrix.conjTranspose_smul,
    Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    mul_comm (star u) u]
lemma slack_compression_plus (X Y Lx Ly Lxy : Mat ι) :
    (parameterColumn (ι:=ι) Complex.I)ᴴ*nhSlack X Y Lx Ly Lxy*parameterColumn (ι:=ι) Complex.I =
      (Lx+Ly-squareSum X Y)-commutator X Y := by
  rw [nhSlack,block_compression]
  simp only [squareSum,commutator,Complex.star_def,Complex.conj_I,neg_mul,Complex.I_mul_I,
    neg_neg,one_smul,neg_smul,smul_sub]
  abel

lemma slack_compression_minus (X Y Lx Ly Lxy : Mat ι) :
    (parameterColumn (ι:=ι) (-Complex.I))ᴴ*nhSlack X Y Lx Ly Lxy*parameterColumn (ι:=ι) (-Complex.I) =
      (Lx+Ly-squareSum X Y)+commutator X Y := by
  rw [nhSlack,block_compression]
  simp only [squareSum,commutator,star_neg,Complex.star_def,Complex.conj_I,neg_neg,mul_neg,
    Complex.I_mul_I,one_smul,neg_smul,smul_sub]
  abel

lemma nhBlock_to_aux (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    nhBlockValues X Y ⊆ nhAuxValues X Y := by
  rintro v ⟨Lx,Ly,Lxy,hx,hy,hxy,hsl,he⟩
  refine ⟨Lx+Ly-squareSum X Y,(hx.add hy).sub (squareSum_hermitian X Y hX hY),?_,?_,?_⟩
  · have h := hsl.conjTranspose_mul_mul_same (parameterColumn (ι:=ι) Complex.I)
    rwa [slack_compression_plus] at h
  · have h := hsl.conjTranspose_mul_mul_same (parameterColumn (ι:=ι) (-Complex.I))
    rwa [slack_compression_minus] at h
  · convert he using 1 <;> congr 1 <;> abel

lemma canonical_slack_positive (T H : Mat ι) (hp : (T+H).PosSemidef) (hm : (T-H).PosSemidef) :
    (Matrix.fromBlocks ((1/2:ℝ) • T) ((Complex.I/2) • H)
      ((-Complex.I/2) • H) ((1/2:ℝ) • T)).PosSemidef := by
  have h := (hp.mul_mul_conjTranspose_same (parameterColumn (ι:=ι) (-Complex.I))).add
    (hm.mul_mul_conjTranspose_same (parameterColumn (ι:=ι) Complex.I))
  have hs := h.smul (by norm_num : (0:ℝ) ≤ 1/4)
  rw [block_outer,block_outer] at hs
  convert hs using 1
  ext (i|i) (j|j) <;>
    simp [Matrix.fromBlocks,Matrix.smul_apply,Complex.star_def,Complex.mul_re,
      Complex.mul_im,Complex.div_re,Complex.div_im] <;> ring

lemma nhAux_to_block (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    nhAuxValues X Y ⊆ nhBlockValues X Y := by
  rintro v ⟨T,hT,hTm,hTp,he⟩
  let Lx := X*X+(1/2:ℝ) • T
  let Ly := Y*Y+(1/2:ℝ) • T
  let Lxy := (1/2:ℝ) • (X*Y+Y*X)
  have hx2 : (X*X).IsHermitian := by simpa [hX.eq] using Matrix.isHermitian_conjTranspose_mul_self X
  have hy2 : (Y*Y).IsHermitian := by simpa [hY.eq] using Matrix.isHermitian_conjTranspose_mul_self Y
  have hxy : Lxy.IsHermitian := by
    simp only [Lxy,Matrix.IsHermitian,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul,hX.eq,hY.eq,star_trivial]
    rw [add_comm]
  refine ⟨Lx,Ly,Lxy,hx2.add (hT.smul (IsSelfAdjoint.all (1/2:ℝ))),hy2.add (hT.smul (IsSelfAdjoint.all (1/2:ℝ))),hxy,?_,?_⟩
  · have h := canonical_slack_positive T (commutator X Y) hTp hTm
    convert h using 1
    ext (i|i) (j|j) <;>
      simp [nhSlack,Lx,Ly,Lxy,commutator,Matrix.fromBlocks,Matrix.smul_apply,
        Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · convert he using 1
    congr 1
    dsimp [Lx,Ly,squareSum]
    module

-- 从原始块SDP得到效应变分目标的精确等价，包含达到。
theorem originalNH_block_minimum (X Y : Mat ι) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    IsLeast (nhBlockValues X Y) (operatorObjective (complexMoment X Y)) := by
  have he : nhBlockValues X Y = nhAuxValues X Y :=
    Set.Subset.antisymm (nhBlock_to_aux X Y hX hY) (nhAux_to_block X Y hX hY)
  rw [he]
  exact nhAux_minimum X Y hX hY

end FiniteCopy.NHOperator



