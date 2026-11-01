import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

open scoped BigOperators Kronecker
open Matrix

noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

abbrev Input (n : ℕ) := Fin (n+1) × Fin 2
abbrev Output (n : ℕ) := Fin (n+2) ⊕ Fin n

-- 分母独立开方使后续根式恒等式直接化为多项式恒等式。
def a (n l : ℕ) : ℝ := Real.sqrt ((n+1 : ℝ) - l) / Real.sqrt (n+1 : ℝ)
def b (n l : ℕ) : ℝ := Real.sqrt (l : ℝ) / Real.sqrt (n+1 : ℝ)

@[simp] theorem a_last (n : ℕ) : a n (n+1) = 0 := by simp [a]
@[simp] theorem b_zero (n : ℕ) : b n 0 = 0 := by simp [b]

theorem a_sq (n l : ℕ) (hl : l ≤ n+1) :
    a n l ^ 2 = ((n+1 : ℝ) - l) / (n+1 : ℝ) := by
  rw [a, div_pow, Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hl)),
    Real.sq_sqrt (by positivity)]

theorem b_sq (n l : ℕ) : b n l ^ 2 = (l : ℝ) / (n+1 : ℝ) := by
  rw [b, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

theorem a_sq_add_b_sq (n l : ℕ) (hl : l ≤ n+1) : a n l ^ 2 + b n l ^ 2 = 1 := by
  rw [a_sq n l hl, b_sq]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

-- 行是 (m 升序的自旋基, 量子比特基)，列是 plus 与 minus 分支。
def realCG (n : ℕ) : Matrix (Input n) (Output n) ℝ := fun p q =>
  match q with
  | Sum.inl l =>
      if p.2 = 0 then (if p.1.castSucc = l then a n l.val else 0)
      else (if p.1.succ = l then b n l.val else 0)
  | Sum.inr k =>
      if p.2 = 0 then (if k.succ = p.1 then -b n (k.val+1) else 0)
      else (if k.castSucc = p.1 then a n (k.val+1) else 0)

def CG (n : ℕ) : Matrix (Input n) (Output n) ℂ := (realCG n).map Complex.ofReal

lemma sum_castSucc (n : ℕ) (l : Fin (n+2)) (x : ℝ)
    (hx : l = Fin.last (n+1) → x = 0) :
    (∑ i : Fin (n+1), if i.castSucc = l then x else 0) = x := by
  have hh := Fin.sum_univ_castSucc (fun i : Fin (n+2) => if i = l then x else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hh
  have hz : (if Fin.last (n+1) = l then x else 0) = 0 := by
    split_ifs with h
    · exact hx h.symm
    · rfl
  rw [hz, add_zero] at hh
  exact hh.symm

lemma sum_succ (n : ℕ) (l : Fin (n+2)) (x : ℝ)
    (hx : l = 0 → x = 0) :
    (∑ i : Fin (n+1), if i.succ = l then x else 0) = x := by
  have hh := Fin.sum_univ_succ (fun i : Fin (n+2) => if i = l then x else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hh
  have hz : (if (0 : Fin (n+2)) = l then x else 0) = 0 := by
    split_ifs with h
    · exact hx h.symm
    · rfl
  rw [hz, zero_add] at hh
  exact hh.symm

theorem realCG_plus_plus (n : ℕ) (l m : Fin (n+2)) :
    (∑ p : Input n, realCG n p (Sum.inl l) * realCG n p (Sum.inl m)) =
      if l = m then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, realCG, Fin.isValue, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide]
  rw [Finset.sum_add_distrib]
  by_cases h : l = m
  · subst m
    simp only [ite_mul_ite, mul_zero, zero_mul, if_true]
    have h₁ := sum_castSucc n l (a n l.val * a n l.val) (by intro hl; simp [hl])
    have h₂ := sum_succ n l (b n l.val * b n l.val) (by intro hl; simp [hl])
    rw [h₁, h₂]
    simpa [pow_two] using a_sq_add_b_sq n l.val (by omega)
  · rw [if_neg h]
    have h₁ : (∑ i : Fin (n+1),
        (if i.castSucc = l then a n l.val else 0) *
        (if i.castSucc = m then a n m.val else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs <;> simp_all
    have h₂ : (∑ i : Fin (n+1),
        (if i.succ = l then b n l.val else 0) *
        (if i.succ = m then b n m.val else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs <;> simp_all
    rw [h₁, h₂, add_zero]

theorem realCG_minus_minus (n : ℕ) (k t : Fin n) :
    (∑ p : Input n, realCG n p (Sum.inr k) * realCG n p (Sum.inr t)) =
      if k = t then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, realCG, Fin.isValue, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide]
  rw [Finset.sum_add_distrib]
  by_cases h : k = t
  · subst t
    simp only [ite_mul_ite, mul_zero, neg_mul_neg, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    simpa [pow_two, add_comm] using a_sq_add_b_sq n (k.val+1) (by omega)
  · simp only [h, ↓reduceIte]
    have hs : k.succ ≠ t.succ := fun he => h (Fin.succ_injective _ he)
    have hc : k.castSucc ≠ t.castSucc := fun he => h (Fin.castSucc_injective _ he)
    have h₁ : (∑ i : Fin (n+1),
        (if k.succ = i then -b n (k.val+1) else 0) *
        (if t.succ = i then -b n (t.val+1) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs <;> simp_all
    have h₂ : (∑ i : Fin (n+1),
        (if k.castSucc = i then a n (k.val+1) else 0) *
        (if t.castSucc = i then a n (t.val+1) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs <;> simp_all
    rw [h₁, h₂, add_zero]

theorem realCG_plus_minus (n : ℕ) (l : Fin (n+2)) (k : Fin n) :
    (∑ p : Input n, realCG n p (Sum.inl l) * realCG n p (Sum.inr k)) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, realCG, Fin.isValue, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide]
  simp only [mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have he : k.succ.castSucc = k.castSucc.succ := rfl
  rw [he]
  by_cases h : k.castSucc.succ = l
  · subst l
    simp only [↓reduceIte, Fin.val_succ, Fin.val_castSucc]
    ring
  · simp [h]

theorem realCG_transpose_mul (n : ℕ) : (realCG n)ᵀ * realCG n = 1 := by
  ext q r
  rcases q with l | k <;> rcases r with m | t
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      realCG_plus_plus n l m
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      realCG_plus_minus n l t
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using
      realCG_plus_minus n m k
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      realCG_minus_minus n k t

theorem CG_conjTranspose_mul (n : ℕ) : (CG n)ᴴ * CG n = 1 := by
  ext q r
  have h := congrArg (fun M : Matrix (Output n) (Output n) ℝ => (M q r : ℂ))
    (realCG_transpose_mul n)
  simpa [CG, Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Matrix.one_apply, apply_ite] using h

theorem CG_mul_conjTranspose (n : ℕ) : CG n * (CG n)ᴴ = 1 := by
  apply (Matrix.mul_eq_one_comm_of_card_eq (Output n) (Input n) ℂ
    (by simp [Input, Output]; omega)).mp
  exact CG_conjTranspose_mul n

end CopyQuantumMetrology.ClebschGordan

