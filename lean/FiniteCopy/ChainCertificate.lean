import FiniteCopy.MatrixDual
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open FiniteCopy.Algebra FiniteCopy.NHOptimization
noncomputable section
namespace FiniteCopy.NHOperator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def diagonalReal (p : ι → ℝ) : Mat ι := Matrix.diagonal (fun i => (p i : ℂ))

lemma diagonalReal_sub (p q : ι → ℝ) : diagonalReal p-diagonalReal q = diagonalReal (fun i=>p i-q i) := by
  ext i j
  by_cases h:i=j <;> simp [diagonalReal,Matrix.diagonal,h]

lemma diagonalReal_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : (diagonalReal p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨hp i,rfl⟩

lemma operatorObjective_diagonal_grams (Z : Mat ι) (p q : ι → ℝ)
    (hP : Zᴴ*Z=diagonalReal p) (hQ : Z*Zᴴ=diagonalReal q) :
    operatorObjective Z = ∑ i, max (p i) (q i) := by
  let W := diagonalReal (fun i => max (p i) (q i))
  let r : ι → ℝ := fun i => if p i ≤ q i then 1 else 0
  let R := diagonalReal r
  have hW : upperFeasible (Zᴴ*Z) (Z*Zᴴ) W := by
    rw [hP,hQ]
    constructor
    · rw [show W=diagonalReal (fun i=>max (p i) (q i)) from rfl,diagonalReal_sub]
      exact diagonalReal_pos _ (fun i=>sub_nonneg.mpr (le_max_left _ _))
    · rw [show W=diagonalReal (fun i=>max (p i) (q i)) from rfl,diagonalReal_sub]
      exact diagonalReal_pos _ (fun i=>sub_nonneg.mpr (le_max_right _ _))
  have hR : Effect R := diagonal_effect r (fun i=>by dsimp [r]; split_ifs <;> norm_num)
  have he : Zᴴ*Z+R*(Z*Zᴴ-Zᴴ*Z)=W := by
    rw [hP,hQ]
    ext i j
    by_cases hij:i=j
    · subst j
      simp only [R,W,diagonalReal,Matrix.add_apply,Matrix.diagonal_mul,
        Matrix.sub_apply,Matrix.diagonal_apply_eq]
      dsimp [r]
      split_ifs with hi
      · simp [max_eq_right hi]
      · simp [max_eq_left (le_of_not_ge hi)]
    · simp [R,W,diagonalReal,Matrix.mul_sub,Matrix.diagonal_mul,hij]
  have ht : tr W = ∑ i,max (p i) (q i) := by simp [W,diagonalReal,tr]
  apply le_antisymm
  · apply csSup_le (operatorObjective_bdd Z).1
    rintro v ⟨R',hR',rfl⟩
    exact (weak_duality _ _ R' W hR' hW).trans_eq ht
  · rw [← ht,← he]
    exact dualValue_le_objective Z R hR

-- 相邻升矩阵：矩阵条目直接定义，无支撑约束施加给待优化算子。
def raiseReal (n : ℕ) (x : ℕ → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if i.val=j.val+1 then x j.val else 0

def raiseMatrix (n : ℕ) (x : ℕ → ℝ) : Mat (Fin (n+1)) :=
  (raiseReal n x).map Complex.ofReal

lemma raise_apply (n : ℕ) (x : ℕ → ℝ) (i j : Fin (n+1)) :
    raiseMatrix n x i j = if i.val=j.val+1 then (x j.val : ℂ) else 0 := by
  by_cases h : i.val=j.val+1 <;> simp [raiseMatrix,raiseReal,h]

lemma raise_trace_zero (n : ℕ) (x : ℕ → ℝ) : Matrix.trace (raiseMatrix n x)=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Matrix.diag,raise_apply]
  rw [if_neg (by omega)]

lemma raise_product_trace_zero (n : ℕ) (x y : ℕ → ℝ) :
    Matrix.trace (raiseMatrix n x*raiseMatrix n y)=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  change ∑ j, raiseMatrix n x i j * raiseMatrix n y j i = 0
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Matrix.diag,raise_apply]
  split_ifs <;> first | omega | simp

lemma adjoint_raise_product (n : ℕ) (x y : ℕ → ℝ) (hx : x n=0) :
    (raiseMatrix n x)ᴴ*raiseMatrix n y = diagonalReal (fun i:Fin (n+1)=>x i.val*y i.val) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply,raise_apply,Complex.star_def]
  by_cases hij:i=j
  · subst j
    rw [diagonalReal,Matrix.diagonal_apply_eq]
    by_cases hi:i.val<n
    · let k : Fin (n+1) := ⟨i.val+1,by omega⟩
      rw [Finset.sum_eq_single k]
      · simp [k,Complex.conj_ofReal]
      · intro l hl hlk
        have hli : l.val ≠ i.val+1 := by
          intro h
          apply hlk
          exact Fin.ext h
        simp [hli]
      · simp
    · have hin : i.val=n := by omega
      rw [hin,hx]
      simp only [zero_mul,Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k.val≠n+1 := by omega
      simp [hki]
  · rw [diagonalReal,Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki:k.val=i.val+1
    · have hkj : k.val≠j.val+1 := by
        intro h
        apply hij
        apply Fin.ext
        omega
      simp [hkj]
    · simp [hki]

lemma raise_adjoint_product (n : ℕ) (x y : ℕ → ℝ) :
    raiseMatrix n x*(raiseMatrix n y)ᴴ =
      diagonalReal (fun i:Fin (n+1)=>previous x i.val*previous y i.val) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply,raise_apply,Complex.star_def]
  by_cases hij:i=j
  · subst j
    rw [diagonalReal,Matrix.diagonal_apply_eq]
    by_cases hi:i.val=0
    · rw [hi]
      simp only [previous,zero_mul,Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro k hk
      simp
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
      let l : Fin (n+1) := ⟨k,by omega⟩
      rw [Finset.sum_eq_single l]
      · simp [l,hk,previous,Complex.conj_ofReal]
      · intro m hm hml
        have hmi : i.val≠m.val+1 := by
          intro h
          apply hml
          apply Fin.ext
          dsimp [l]
          omega
        simp [hmi]
      · simp
  · rw [diagonalReal,Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki:i.val=k.val+1
    · have hkj : j.val≠k.val+1 := by
        intro h
        apply hij
        apply Fin.ext
        omega
      simp [hkj]
    · simp [hki]

lemma raise_objective (n : ℕ) (x : ℕ → ℝ) (hx : x n=0) :
    operatorObjective (raiseMatrix n x)=chainObjective n x := by
  rw [operatorObjective_diagonal_grams _ _ _ (adjoint_raise_product n x x hx) (raise_adjoint_product n x x)]
  unfold chainObjective
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_two]
  rw [max_comm]

lemma canonical_matrix_certificate (n : ℕ) (i j : Fin (n+1)) :
    raiseReal n (canonicalA n) i j * (1+canonicalR n i.val-canonicalR n j.val) =
      raiseReal n (spinEdge n) i j := by
  unfold raiseReal
  split_ifs with h
  · rw [h]
    have hc := canonical_coefficient n j.val (by omega)
    nlinarith
  · simp

lemma canonical_pairing_capacity (n : ℕ) :
    matrixCapacity (raiseReal n (spinEdge n)) (raiseReal n (canonicalA n)) = spinS n := by
  unfold matrixCapacity
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hsum (j:Fin (n+1)) :
      (∑ i:Fin (n+1),raiseReal n (spinEdge n) i j*raiseReal n (canonicalA n) i j) =
        spinEdge n j.val*canonicalA n j.val := by
    by_cases hj:j.val<n
    · let k:Fin (n+1):=⟨j.val+1,by omega⟩
      rw [Finset.sum_eq_single k]
      · simp [raiseReal,k]
      · intro l hl hlk
        have hlj:l.val≠j.val+1 := by intro h; apply hlk; exact Fin.ext h
        simp [raiseReal,hlj]
      · simp
    · have hjn:j.val=n := by omega
      rw [hjn,spinEdge_last,zero_mul]
      apply Finset.sum_eq_zero
      intro i hi
      simp [raiseReal,hjn,show i.val≠n+1 by omega]
  simp_rw [hsum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,spinEdge_last,zero_mul,add_zero]
  exact Fin.sum_univ_eq_sum_range (fun i=>spinEdge n i*canonicalA n i) n

theorem canonical_fullmatrix_lower (n : ℕ) (Z : Mat (Fin (n+1))) :
    matrixPairing (raiseReal n (spinEdge n)) Z ^ 2 ≤ spinS n*operatorObjective Z := by
  have h := matrix_certificate_bound (fun i:Fin (n+1)=>canonicalR n i.val)
    (raiseReal n (canonicalA n)) (raiseReal n (spinEdge n)) Z
    (fun i=>canonicalR_bounds n i.val (by omega))
    (fun i j=>by dsimp [raiseReal]; split_ifs; exact canonicalA_nonneg n j.val; positivity)
    (canonical_matrix_certificate n)
  rwa [canonical_pairing_capacity] at h

end FiniteCopy.NHOperator

