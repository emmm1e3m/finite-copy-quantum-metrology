import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

open scoped BigOperators
open Finset Set

namespace FiniteCopy.ConvexRoof

section Reduction
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- 选择让目标的关系和非正的消点方向。 -/
theorem improving_relation {s : Finset E} (g : E → ℝ)
    (hs : ¬ AffineIndependent ℝ ((↑) : s → E)) :
    ∃ r : E → ℝ, (∑ x ∈ s, r x • x)=0 ∧ (∑ x ∈ s, r x)=0 ∧
      (∃ x ∈ s, r x ≠ 0) ∧ (∑ x ∈ s, r x*g x) ≤ 0 := by
  obtain ⟨r,hrx,hr1,hrne⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind hs
  by_cases hg : (∑ x ∈ s, r x*g x) ≤ 0
  · exact ⟨r,hrx,hr1,hrne,hg⟩
  · refine ⟨fun x => -r x, ?_, ?_, ?_, ?_⟩
    · simp only [neg_smul, sum_neg_distrib, hrx, neg_zero]
    · simp only [sum_neg_distrib, hr1, neg_zero]
    · obtain ⟨x,hx,hne⟩ := hrne
      exact ⟨x,hx,neg_ne_zero.mpr hne⟩
    · simp only [neg_mul, sum_neg_distrib]
      linarith

/-- 保持重心并提高目标，删除一个仿射相关的支撑点。 -/
theorem improving_erase [DecidableEq E] (s : Finset E) (w g : E → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (h1 : (∑ x ∈ s, w x)=1)
    (hs : ¬ AffineIndependent ℝ ((↑) : s → E)) :
    ∃ i ∈ s, ∃ v : E → ℝ,
      (∀ x ∈ s.erase i, 0 ≤ v x) ∧ (∑ x ∈ s.erase i, v x)=1 ∧
      (∑ x ∈ s.erase i, v x • x)=(∑ x ∈ s, w x • x) ∧
      (∑ x ∈ s, w x*g x) ≤ ∑ x ∈ s.erase i, v x*g x := by
  obtain ⟨r,hrx,hr1,hrne,hrg⟩ := improving_relation g hs
  have hrpos := exists_pos_of_sum_zero_of_exists_nonzero r hr1 hrne
  let t := {x ∈ s | 0 < r x}
  obtain ⟨i,hit,hmin⟩ : ∃ i ∈ t, ∀ x ∈ t, w i/r i ≤ w x/r x := by
    apply t.exists_min_image (fun x => w x/r x)
    obtain ⟨x,hx,hr⟩ := hrpos
    exact ⟨x,mem_filter.mpr ⟨hx,hr⟩⟩
  have hi : i ∈ s := (mem_filter.mp hit).1
  have hri : 0 < r i := (mem_filter.mp hit).2
  have hstep : 0 ≤ w i/r i := div_nonneg (hw i hi) hri.le
  let v : E → ℝ := fun x => w x-(w i/r i)*r x
  have hvi : v i=0 := by simp [v,hri.ne']
  have hv : ∀ x ∈ s, 0 ≤ v x := by
    intro x hx
    dsimp [v]
    by_cases hxt : x ∈ t
    · have hr : 0 < r x := (mem_filter.mp hxt).2
      have hh := (le_div_iff₀ hr).mp (hmin x hxt)
      linarith
    · have hr : r x ≤ 0 := by simpa [t,hx] using hxt
      have hh := mul_nonpos_of_nonneg_of_nonpos hstep hr
      linarith [hw x hx]
  have hsum : (∑ x ∈ s, v x)=1 := by
    simp only [v, sum_sub_distrib, ← mul_sum, h1, hr1, mul_zero, sub_zero]
  refine ⟨i,hi,v,fun x hx => hv x (mem_of_mem_erase hx), ?_, ?_, ?_⟩
  · rw [sum_erase _ hvi, hsum]
  · rw [sum_erase s (f := fun x => v x • x) (by rw [hvi,zero_smul])]
    simp only [v,sub_smul,mul_smul,sum_sub_distrib,← smul_sum,hrx,smul_zero,sub_zero]
  · rw [sum_erase s (f := fun x => v x*g x) (by rw [hvi,zero_mul])]
    simp only [v,sub_mul,mul_assoc,sum_sub_distrib,← mul_sum]
    have hh := mul_nonpos_of_nonneg_of_nonpos hstep hrg
    linarith

/-- 有限混合可压到仿射无关支撑，且不降低任意标量目标。 -/
theorem reduce_support (S : Set E) (g : E → ℝ) (x : E) (z : ℝ)
    (h : ∃ s : Finset E, (s : Set E) ⊆ S ∧ ∃ w : E → ℝ,
      (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p)=1 ∧
      (∑ p ∈ s, w p • p)=x ∧ z ≤ ∑ p ∈ s, w p*g p) :
    ∃ s : Finset E, (s : Set E) ⊆ S ∧ AffineIndependent ℝ ((↑) : s → E) ∧
      ∃ w : E → ℝ, (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p)=1 ∧
        (∑ p ∈ s, w p • p)=x ∧ z ≤ ∑ p ∈ s, w p*g p := by
  classical
  let good : Set (Finset E) := {s | (s : Set E) ⊆ S ∧ ∃ w : E → ℝ,
      (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p)=1 ∧
      (∑ p ∈ s, w p • p)=x ∧ z ≤ ∑ p ∈ s, w p*g p}
  have hgood : good.Nonempty := h
  let s := Function.argminOn Finset.card good hgood
  have hs : s ∈ good := Function.argminOn_mem Finset.card good hgood
  obtain ⟨hS,w,hw,h1,hx,hz⟩ := hs
  have hind : AffineIndependent ℝ ((↑) : s → E) := by
    by_contra hnot
    obtain ⟨i,hi,v,hv,hv1,hvx,hvz⟩ := improving_erase s w g hw h1 hnot
    have he : s.erase i ∈ good :=
      ⟨Set.Subset.trans (Finset.erase_subset i s) hS, v,hv,hv1,hvx.trans hx,hz.trans hvz⟩
    have hcard : s.card ≤ (s.erase i).card := Function.argminOn_le Finset.card good he
    have hlt := card_erase_lt_of_mem hi
    omega
  exact ⟨s,hS,hind,w,hw,h1,hx,hz⟩

end Reduction
end FiniteCopy.ConvexRoof
