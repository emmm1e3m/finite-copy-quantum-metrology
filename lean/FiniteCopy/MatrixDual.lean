import FiniteCopy.POVMLower
import FiniteCopy.SpinNH

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat (ι : Type*) := Matrix ι ι ℂ

def tr (A : Mat ι) : ℝ := (Matrix.trace A).re

def Effect (R : Mat ι) : Prop := R.PosSemidef ∧ (1-R).PosSemidef

def upperFeasible (P Q W : Mat ι) : Prop := (W-P).PosSemidef ∧ (W-Q).PosSemidef

def dualValue (P Q R : Mat ι) : ℝ := tr (P+R*(Q-P))

def dualValues (P Q : Mat ι) : Set ℝ := {v | ∃ R, Effect R ∧ dualValue P Q R = v}

def primalValues (P Q : Mat ι) : Set ℝ := {v | ∃ W, upperFeasible P Q W ∧ tr W = v}

def operatorObjective (Z : Mat ι) : ℝ := sSup (dualValues (Zᴴ*Z) (Z*Zᴴ))

lemma tr_add (A B : Mat ι) : tr (A+B) = tr A+tr B := by simp [tr]
lemma tr_sub (A B : Mat ι) : tr (A-B) = tr A-tr B := by simp [tr]
lemma tr_zero : tr (0 : Mat ι) = 0 := by simp [tr]
lemma tr_real_smul (a : ℝ) (A : Mat ι) : tr (a • A) = a*tr A := by
  simp only [tr, Matrix.trace_smul]
  change RCLike.re (a • A.trace) = a*A.trace.re
  rw [RCLike.smul_re]
  rfl

lemma trace_product_nonneg (A B : Mat ι) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ tr (A*B) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hC]
  have hp := hA.mul_mul_conjTranspose_same C
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  change 0 ≤ (Matrix.trace (A*(Cᴴ*C))).re
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact ht

lemma effect_zero : Effect (0 : Mat ι) := by
  exact ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one : (1 : Mat ι).PosSemidef)⟩

lemma weak_duality (P Q R W : Mat ι) (hR : Effect R) (hW : upperFeasible P Q W) :
    dualValue P Q R ≤ tr W := by
  have h1 := trace_product_nonneg (1-R) (W-P) hR.2 hW.1
  have h2 := trace_product_nonneg R (W-Q) hR.1 hW.2
  have he : (1-R)*(W-P)+R*(W-Q) = W-(P+R*(Q-P)) := by noncomm_ring
  have ht := tr_add ((1-R)*(W-P)) (R*(W-Q))
  rw [he, tr_sub] at ht
  unfold dualValue
  linarith

lemma operatorObjective_bdd (Z : Mat ι) :
    (dualValues (Zᴴ*Z) (Z*Zᴴ)).Nonempty ∧ BddAbove (dualValues (Zᴴ*Z) (Z*Zᴴ)) := by
  constructor
  · exact ⟨dualValue (Zᴴ*Z) (Z*Zᴴ) 0, 0, effect_zero, rfl⟩
  · refine ⟨tr (Zᴴ*Z+Z*Zᴴ), ?_⟩
    rintro v ⟨R,hR,rfl⟩
    apply weak_duality _ _ _ _ hR
    constructor
    · simpa using (Matrix.posSemidef_self_mul_conjTranspose Z)
    · simpa using (Matrix.posSemidef_conjTranspose_mul_self Z)

lemma operatorObjective_upper (Z : Mat ι) : operatorObjective Z ≤ 2*tr (Zᴴ*Z) := by
  apply csSup_le (operatorObjective_bdd Z).1
  rintro v ⟨R,hR,rfl⟩
  have h := weak_duality (Zᴴ*Z) (Z*Zᴴ) R (Zᴴ*Z+Z*Zᴴ) hR
    ⟨by simpa using (Matrix.posSemidef_self_mul_conjTranspose Z),
      by simpa using (Matrix.posSemidef_conjTranspose_mul_self Z)⟩
  rw [tr_add] at h
  have he : tr (Z*Zᴴ) = tr (Zᴴ*Z) := by unfold tr; rw [Matrix.trace_mul_comm]
  rw [he] at h
  linarith

lemma dualValue_le_objective (Z R : Mat ι) (hR : Effect R) :
    dualValue (Zᴴ*Z) (Z*Zᴴ) R ≤ operatorObjective Z :=
  le_csSup (operatorObjective_bdd Z).2 ⟨R,hR,rfl⟩

-- 谱分解只用于构造通用SDP的达到点，未假设其最优值。
lemma spectral_upper_dual_attain (P Q : Mat ι) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ∃ R W : Mat ι, Effect R ∧ upperFeasible P Q W ∧ dualValue P Q R = tr W := by
  let H := Q-P
  have hH : H.IsHermitian := hQ.sub hP
  let U : Mat ι := hH.eigenvectorUnitary
  let d : ι → ℝ := hH.eigenvalues
  let b : ι → ℝ := fun i => max (d i) 0
  let r : ι → ℝ := fun i => if 0 ≤ d i then 1 else 0
  let B : Mat ι := U * Matrix.diagonal (fun i => (b i : ℂ)) * Uᴴ
  let R : Mat ι := U * Matrix.diagonal (fun i => (r i : ℂ)) * Uᴴ
  have hU : Uᴴ*U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hU' : U*Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hspec : H = U*Matrix.diagonal (fun i => (d i : ℂ))*Uᴴ := by
    have hh := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hh
    convert hh using 1
    rfl
  have hb : (Matrix.diagonal (fun i => (b i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((max (d i) 0 : ℝ) : ℂ)
    exact Complex.nonneg_iff.mpr ⟨le_max_right (d i) 0, rfl⟩
  have hr : (Matrix.diagonal (fun i => (r i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [r]
    split_ifs <;> norm_num
  have hr' : (Matrix.diagonal (fun i => ((1-r i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [r]
    split_ifs <;> norm_num
  have hR : Effect R := by
    constructor
    · exact hr.mul_mul_conjTranspose_same U
    · have he : (1 : Mat ι)-R = U*Matrix.diagonal (fun i => ((1-r i : ℝ) : ℂ))*Uᴴ := by
        have he0 : Matrix.diagonal (fun i => ((1-r i : ℝ) : ℂ)) =
            (1 : Mat ι)-Matrix.diagonal (fun i => (r i : ℂ)) := by
          ext i j
          by_cases hij : i=j <;> simp [Matrix.diagonal, hij]
        rw [he0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU']
      rw [he]
      exact hr'.mul_mul_conjTranspose_same U
  have hBH : (B-H).PosSemidef := by
    have hp : (Matrix.diagonal (fun i => ((b i-d i : ℝ) : ℂ))).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      change (0 : ℂ) ≤ ((max (d i) 0-d i : ℝ) : ℂ)
      exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (le_max_left (d i) 0), rfl⟩
    have he : B-H = U*Matrix.diagonal (fun i => ((b i-d i : ℝ) : ℂ))*Uᴴ := by
      have he0 : Matrix.diagonal (fun i => ((b i-d i : ℝ) : ℂ)) =
          Matrix.diagonal (fun i => (b i : ℂ))-Matrix.diagonal (fun i => (d i : ℂ)) := by
        ext i j
        by_cases hij : i=j <;> simp [Matrix.diagonal, hij]
      rw [hspec, he0, Matrix.mul_sub, Matrix.sub_mul]
    rw [he]
    exact hp.mul_mul_conjTranspose_same U
  have hRH : R*H = B := by
    rw [hspec]
    dsimp [R, B]
    have he : (Matrix.diagonal (fun i => (r i : ℂ))) * Matrix.diagonal (fun i => (d i : ℂ)) =
        Matrix.diagonal (fun i => (b i : ℂ)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      dsimp [r,b]
      split_ifs with hi
      · simp [max_eq_left hi]
      · simp [max_eq_right (le_of_not_ge hi)]
    calc
      _ = U * ((Matrix.diagonal (fun i => (r i : ℂ))) * (Uᴴ*U) * Matrix.diagonal (fun i => (d i : ℂ))) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one, he]
  refine ⟨R,P+B,hR,?_,?_⟩
  · constructor
    · simpa using hb.mul_mul_conjTranspose_same U
    · convert hBH using 1 <;> dsimp [H] <;> abel
  · unfold dualValue
    change tr (P+R*H) = _
    rw [hRH]








lemma upper_primal_dual_optimum (P Q : Mat ι) (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ∃ v, IsGreatest (dualValues P Q) v ∧ IsLeast (primalValues P Q) v := by
  obtain ⟨R,W,hR,hW,he⟩ := spectral_upper_dual_attain P Q hP hQ
  refine ⟨tr W, ⟨⟨R,hR,he⟩,?_⟩,⟨⟨W,hW,rfl⟩,?_⟩⟩
  · rintro v ⟨R',hR',rfl⟩
    exact weak_duality P Q R' W hR' hW
  · rintro v ⟨W',hW',rfl⟩
    rw [← he]
    exact weak_duality P Q R W' hR hW'

-- 因而算子目标确实等于共同上界的原始SDP最小值。
theorem operatorObjective_primal_minimum (Z : Mat ι) :
    IsLeast (primalValues (Zᴴ*Z) (Z*Zᴴ)) (operatorObjective Z) := by
  obtain ⟨v,hmax,hmin⟩ := upper_primal_dual_optimum (Zᴴ*Z) (Z*Zᴴ)
    (Matrix.isHermitian_conjTranspose_mul_self Z) (Matrix.isHermitian_mul_conjTranspose_self Z)
  have he : operatorObjective Z = v := hmax.csSup_eq
  rwa [he]

lemma operatorObjective_nonneg (Z : Mat ι) : 0 ≤ operatorObjective Z := by
  have h := dualValue_le_objective Z 0 effect_zero
  simp only [dualValue, Matrix.zero_mul, add_zero] at h
  have h0 : 0 ≤ tr (Zᴴ*Z) := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self Z).trace_nonneg).1
  exact h0.trans h

lemma tr_gram (Z : Mat ι) : tr (Z*Zᴴ) = ∑ i, ∑ j, Complex.normSq (Z i j) := by
  simp [tr, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj]

lemma tr_diagonal_mul (r : ι → ℝ) (A : Mat ι) :
    tr (Matrix.diagonal (fun i => (r i : ℂ))*A) = ∑ i, r i*(A i i).re := by
  simp [tr, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.mul_re]

lemma gram_diag (Z : Mat ι) (i : ι) : (Z*Zᴴ) i i = ∑ j, (Complex.normSq (Z i j) : ℂ) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]

lemma adjoint_gram_diag (Z : Mat ι) (i : ι) : (Zᴴ*Z) i i = ∑ j, (Complex.normSq (Z j i) : ℂ) := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using gram_diag Zᴴ i

lemma diagonal_effect (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    Effect (Matrix.diagonal (fun i => (r i : ℂ))) := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.nonneg_iff.mpr ⟨(hr i).1,rfl⟩
  · have he : (1 : Mat ι)-Matrix.diagonal (fun i => (r i : ℂ)) =
        Matrix.diagonal (fun i => ((1-r i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal, hij]
    rw [he]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hr i).2,rfl⟩

lemma diagonal_dualValue (Z : Mat ι) (r : ι → ℝ) :
    dualValue (Zᴴ*Z) (Z*Zᴴ) (Matrix.diagonal (fun i => (r i : ℂ))) =
      ∑ p : ι×ι, (1+r p.1-r p.2)*Complex.normSq (Z p.1 p.2) := by
  unfold dualValue
  rw [Matrix.mul_sub, tr_add, tr_sub, tr_diagonal_mul, tr_diagonal_mul]
  have hp : tr (Zᴴ*Z) = ∑ i, ∑ j, Complex.normSq (Z i j) := by
    unfold tr
    rw [Matrix.trace_mul_comm]
    exact tr_gram Z
  rw [hp]
  simp_rw [gram_diag, adjoint_gram_diag]
  simp only [Complex.re_sum, Complex.ofReal_re, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => r i*Complex.normSq (Z j i)), Fintype.sum_prod_type]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def matrixPairing (c : Matrix ι ι ℝ) (Z : Mat ι) : ℝ :=
  ∑ p : ι×ι, c p.1 p.2 * (Z p.1 p.2).re

def matrixCapacity (c a : Matrix ι ι ℝ) : ℝ :=
  ∑ p : ι×ι, c p.1 p.2 * a p.1 p.2

-- 全矩阵对偶证书：未限制Z的支撑、实性、秩或块结构。
theorem matrix_certificate_bound (r : ι → ℝ) (a c : Matrix ι ι ℝ) (Z : Mat ι)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (ha : ∀ i j, 0 ≤ a i j)
    (hc : ∀ i j, a i j*(1+r i-r j) = c i j) :
    matrixPairing c Z ^ 2 ≤ matrixCapacity c a * operatorObjective Z := by
  have hk (i j : ι) : 0 ≤ 1+r i-r j := by have := hr i; have := hr j; linarith
  have hca (p : ι×ι) : 0 ≤ c p.1 p.2 * a p.1 p.2 := by
    rw [← hc]
    exact mul_nonneg (mul_nonneg (ha _ _) (hk _ _)) (ha _ _)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun p _ => hca p)
    (fun p _ => mul_nonneg (hk p.1 p.2) (Complex.normSq_nonneg (Z p.1 p.2)))
    (r := fun p : ι×ι => c p.1 p.2*(Z p.1 p.2).re) (fun p _ => by
      have hsq : (Z p.1 p.2).re^2 ≤ Complex.normSq (Z p.1 p.2) := by
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (Z p.1 p.2).im]
      calc
        _ = (a p.1 p.2*(1+r p.1-r p.2))^2 * (Z p.1 p.2).re^2 := by rw [← hc]; ring
        _ ≤ (a p.1 p.2*(1+r p.1-r p.2))^2 * Complex.normSq (Z p.1 p.2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = _ := by rw [← hc]; ring)
  have hdual := dualValue_le_objective Z _ (diagonal_effect r hr)
  rw [diagonal_dualValue] at hdual
  exact hcs.trans (mul_le_mul_of_nonneg_left hdual (Finset.sum_nonneg (fun p _ => hca p)))

end FiniteCopy.NHOperator

