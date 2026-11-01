import FiniteCopy.NHModel
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open FiniteCopy.Algebra FiniteCopy.NHOptimization
noncomputable section
namespace FiniteCopy.NHOperator

variable {B : Type*} [Fintype B] [DecidableEq B]

def blockRealRaising (n : B → ℕ) (x : B → ℕ → ℝ) :=
  Matrix.blockDiagonal' (fun b=>raiseReal (n b) (x b))

lemma blockRaising_map (n : B → ℕ) (x : B → ℕ → ℝ) :
    (blockRealRaising n x).map Complex.ofReal = blockRaising n x := by
  exact Matrix.blockDiagonal'_map _ _ rfl

lemma capacity_trace {ι : Type*} [Fintype ι] (c a : Matrix ι ι ℝ) :
    matrixCapacity c a = Matrix.trace (aᵀ*c) := by
  simp only [matrixCapacity, Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Matrix.transpose_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma block_capacity (n : B → ℕ) :
    matrixCapacity (blockRealRaising n (fun b=>spinEdge (n b)))
      (blockRealRaising n (fun b=>canonicalA (n b))) = ∑ b,spinS (n b) := by
  rw [capacity_trace]
  simp only [blockRealRaising,Matrix.blockDiagonal'_transpose,
    ← Matrix.blockDiagonal'_mul,Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro b hb
  rw [← capacity_trace, canonical_pairing_capacity]

lemma block_fullmatrix_lower (n : B → ℕ) (Z : Mat (Σ b:B,Fin (n b+1))) :
    matrixPairing (blockRealRaising n (fun b=>spinEdge (n b))) Z ^ 2 ≤
      (∑ b,spinS (n b))*operatorObjective Z := by
  have h := matrix_certificate_bound (fun i:Σ b:B,Fin (n b+1)=>canonicalR (n i.1) i.2.val)
    (blockRealRaising n (fun b=>canonicalA (n b)))
    (blockRealRaising n (fun b=>spinEdge (n b))) Z
    (fun i=>canonicalR_bounds (n i.1) i.2.val (by omega))
    (by
      rintro ⟨b,i⟩ ⟨c,j⟩
      by_cases h:b=c
      · subst c
        simp only [blockRealRaising,Matrix.blockDiagonal'_apply_eq,raiseReal]
        split_ifs <;> first | exact canonicalA_nonneg _ _ | positivity
      · simp [blockRealRaising,Matrix.blockDiagonal'_apply_ne _ _ _ h])
    (by
      rintro ⟨b,i⟩ ⟨c,j⟩
      by_cases h:b=c
      · subst c
        simp only [blockRealRaising,Matrix.blockDiagonal'_apply_eq]
        exact canonical_matrix_certificate _ _ _
      · simp [blockRealRaising,Matrix.blockDiagonal'_apply_ne _ _ _ h])
  rwa [block_capacity] at h

lemma block_raise_objective (n : B → ℕ) (x : B → ℕ → ℝ)
    (hx : ∀ b,x b (n b)=0) :
    operatorObjective (blockRaising n x) = ∑ b,chainObjective (n b) (x b) := by
  have hp : (blockRaising n x)ᴴ*blockRaising n x =
      diagonalReal (fun i:Σ b:B,Fin (n b+1)=> x i.1 i.2.val*x i.1 i.2.val) := by
    simp only [blockRaising,Matrix.blockDiagonal'_conjTranspose,← Matrix.blockDiagonal'_mul,
      adjoint_raise_product _ _ _ (hx _),diagonalReal,Matrix.blockDiagonal'_diagonal]
  have hq : blockRaising n x*(blockRaising n x)ᴴ =
      diagonalReal (fun i:Σ b:B,Fin (n b+1)=> previous (x i.1) i.2.val*previous (x i.1) i.2.val) := by
    simp only [blockRaising,Matrix.blockDiagonal'_conjTranspose,← Matrix.blockDiagonal'_mul,
      raise_adjoint_product,diagonalReal,Matrix.blockDiagonal'_diagonal]
  rw [operatorObjective_diagonal_grams _ _ _ hp hq,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← raise_objective (n b) (x b) (hx b),
    operatorObjective_diagonal_grams _ _ _ (adjoint_raise_product _ _ _ (hx b)) (raise_adjoint_product _ _ _)]

lemma raise_smul (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    raiseMatrix n (fun i=>t*x i) = t • raiseMatrix n x := by
  ext i j
  simp only [raise_apply,Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

lemma block_raise_smul (n : B → ℕ) (x : B → ℕ → ℝ) (t : ℝ) :
    blockRaising n (fun b i=>t*x b i) = t • blockRaising n x := by
  simp only [blockRaising,raise_smul]
  exact Matrix.blockDiagonal'_smul t _

lemma canonical_block_objective (n : B → ℕ) (t : ℝ) :
    operatorObjective (t • blockRaising n (fun b=>canonicalA (n b))) =
      t^2*(∑ b,spinS (n b)) := by
  rw [← block_raise_smul,block_raise_objective n _ (by intro b; simp [canonicalA_last])]
  simp only [chainObjective_scale,canonical_attains,Finset.mul_sum]

lemma block_raise_trace (n : B → ℕ) (x : B → ℕ → ℝ) :
    Matrix.trace (blockRaising n x)=0 := by
  simp [blockRaising,Matrix.trace_blockDiagonal',raise_trace_zero]

lemma block_raise_product_trace (n : B → ℕ) (x y : B → ℕ → ℝ) :
    Matrix.trace (blockRaising n x*blockRaising n y)=0 := by
  simp only [blockRaising,← Matrix.blockDiagonal'_mul,Matrix.trace_blockDiagonal',raise_product_trace_zero,
    Finset.sum_const_zero]

lemma canonical_mixed_trace (n : ℕ) :
    Matrix.trace ((raiseMatrix n (canonicalA n))ᴴ*raiseMatrix n (spinEdge n))=(spinS n:ℂ) := by
  rw [adjoint_raise_product _ _ _ (canonicalA_last n)]
  simp only [diagonalReal,Matrix.trace_diagonal]
  have he : (∑ i:Fin (n+1),canonicalA n i.val*spinEdge n i.val)=spinS n := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,canonicalA_last,zero_mul,add_zero]
    rw [spinS,capSum,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact_mod_cast he

lemma canonical_block_mixed_trace (n : B → ℕ) :
    Matrix.trace ((blockRaising n (fun b=>canonicalA (n b)))ᴴ*
      blockRaising n (fun b=>spinEdge (n b)))=((∑ b,spinS (n b)):ℂ) := by
  simp only [blockRaising,Matrix.blockDiagonal'_conjTranspose,← Matrix.blockDiagonal'_mul,
    Matrix.trace_blockDiagonal',canonical_mixed_trace,Complex.ofReal_sum]

-- 全部零均值与四个局部无偏矩均由真实候选矩阵计算。
lemma canonical_block_feasible (n : B → ℕ) (D : ℝ) (hS : (∑ b,spinS (n b))≠0) :
    FirstMomentFeasible D (blockRaising n (fun b=>spinEdge (n b)))
      (axisX ((D/(∑ b,spinS (n b))) • blockRaising n (fun b=>canonicalA (n b))))
      (axisY ((D/(∑ b,spinS (n b))) • blockRaising n (fun b=>canonicalA (n b)))) := by
  apply axes_firstMoment
  · simp [Matrix.trace_smul,block_raise_trace]
  · simp [Matrix.smul_mul,Matrix.trace_smul,block_raise_product_trace]
  · simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.trace_smul,
      canonical_block_mixed_trace,Complex.real_smul]
    norm_cast
    exact div_mul_cancel₀ D hS

theorem block_NH_minimum (n : B → ℕ) (D : ℝ) (hD : 0<D)
    (hS : 0<∑ b,spinS (n b)) :
    IsLeast (nhValues D (blockRaising n (fun b=>spinEdge (n b))))
      (D^2/(∑ b,spinS (n b))) := by
  let A := (D/(∑ b,spinS (n b))) • blockRaising n (fun b=>canonicalA (n b))
  have hf := canonical_block_feasible n D (ne_of_gt hS)
  have he : operatorObjective A = D^2/(∑ b,spinS (n b)) := by
    rw [canonical_block_objective]
    field_simp
  constructor
  · refine ⟨axisX A,axisY A,hf,?_⟩
    have h := (originalNH_block_minimum (axisX A) (axisY A)
      (axisX_hermitian A) (axisY_hermitian A)).1
    rwa [complexMoment_axes,he] at h
  · rintro v ⟨X,Y,hXY,hv⟩
    have hp : matrixPairing (blockRealRaising n (fun b=>spinEdge (n b))) (complexMoment X Y)=D := by
      apply combined_firstMoment
      rwa [blockRaising_map]
    have hl := block_fullmatrix_lower n (complexMoment X Y)
    rw [hp] at hl
    have hmin := (originalNH_block_minimum X Y hXY.hermitianX hXY.hermitianY).2 hv
    apply (div_le_iff₀ hS).mpr
    simpa only [mul_comm v] using hl.trans (mul_le_mul_of_nonneg_left hmin hS.le)

theorem block_NH_risk (n : B → ℕ) (N D : ℝ) (hD : 0<D)
    (hS : 0<∑ b,spinS (n b)) :
    nhRisk N D (blockRaising n (fun b=>spinEdge (n b))) = N*D/(∑ b,spinS (n b)) := by
  rw [nhRisk,(block_NH_minimum n D hD hS).csInf_eq]
  field_simp

end FiniteCopy.NHOperator
