import FiniteCopy.SpinInterface
import FiniteCopy.Schur
import Mathlib.Tactic

open scoped BigOperators
open Finset Filter Asymptotics

namespace FiniteCopy.NHOptimization
open FiniteCopy.Algebra NHLowerBound

/-- NH 约化后的实际逐扇区凸目标，右边界另要求 x n=0。 -/
noncomputable def chainObjective (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), max ((previous x i)^2) ((x i)^2)

def edgePairing (n : ℕ) (c x : ℕ → ℝ) : ℝ := ∑ i ∈ range n, c i * x i

def capSum (n : ℕ) (c a : ℕ → ℝ) : ℝ := ∑ i ∈ range n, c i * a i

theorem chainObjective_nonneg (n : ℕ) (x : ℕ → ℝ) : 0 ≤ chainObjective n x :=
  sum_nonneg (fun _ _ => (sq_nonneg _).trans (le_max_right _ _))

theorem support_sum (n : ℕ) (r x : ℕ → ℝ) :
    (∑ i ∈ range (n + 1), (r i * (previous x i)^2 + (1-r i) * (x i)^2)) =
      (∑ i ∈ range n, (1-r i+r (i+1)) * (x i)^2) + (1-r n) * (x n)^2 := by
  induction n with
  | zero => simp [previous]
  | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ]
      simp only [previous]
      ring

theorem chain_support (n : ℕ) (r x : ℕ → ℝ)
    (hx : x n = 0) (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1) :
    (∑ i ∈ range n, (1-r i+r (i+1)) * (x i)^2) ≤ chainObjective n x := by
  have hs := support_sum n r x
  rw [hx] at hs
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hs
  rw [← hs]
  apply sum_le_sum
  intro i hi
  obtain ⟨h0,h1⟩ := hr i (by simpa using mem_range.mp hi)
  have hleft := mul_le_mul_of_nonneg_left (le_max_left ((previous x i)^2) ((x i)^2)) h0
  have hright := mul_le_mul_of_nonneg_left (le_max_right ((previous x i)^2) ((x i)^2)) (sub_nonneg.mpr h1)
  nlinarith

theorem chain_cs (n : ℕ) (c a r x : ℕ → ℝ)
    (hx : x n = 0) (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (ha : ∀ i < n, 0 ≤ a i)
    (hc : ∀ i < n, a i * (1-r i+r (i+1)) = c i) :
    (edgePairing n c x)^2 ≤ capSum n c a * chainObjective n x := by
  have hq : ∀ i ∈ range n, 0 ≤ 1-r i+r (i+1) := by
    intro i hi
    have hh := hr i (by have := mem_range.mp hi; omega)
    have hh' := hr (i+1) (by have := mem_range.mp hi; omega)
    linarith
  have hca : ∀ i ∈ range n, 0 ≤ c i * a i := by
    intro i hi
    rw [← hc i (mem_range.mp hi)]
    exact mul_nonneg (mul_nonneg (ha i (mem_range.mp hi)) (hq i hi)) (ha i (mem_range.mp hi))
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (range n) hca
    (fun i hi => mul_nonneg (hq i hi) (sq_nonneg (x i)))
    (r := fun i => c i * x i) (fun i hi => by
      rw [← hc i (mem_range.mp hi)]
      exact le_of_eq (by ring))
  exact hcs.trans (mul_le_mul_of_nonneg_left (chain_support n r x hx hr) (sum_nonneg hca))

theorem chainObjective_scale (n : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    chainObjective n (fun i => t * x i) = t^2 * chainObjective n x := by
  unfold chainObjective
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have hp : previous (fun i => t*x i) i = t * previous x i := by cases i <;> simp [previous]
  rw [hp, mul_pow, mul_pow, ← mul_max_of_nonneg _ _ (sq_nonneg t)]

theorem edgePairing_scale (n : ℕ) (c x : ℕ → ℝ) (t : ℝ) :
    edgePairing n c (fun i => t*x i) = t * edgePairing n c x := by
  unfold edgePairing
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

end FiniteCopy.NHOptimization

