import FiniteCopy.WeightedReduction
import Mathlib.Data.Fin.Embedding

open scoped BigOperators
open Finset Set
set_option linter.deprecated false

noncomputable section
namespace FiniteCopy.ConvexRoof

abbrev Simplex (d : ℕ) := stdSimplex ℝ (Fin d)
def uniform (d : ℕ) : Fin d → ℝ := fun _ => 1/(d : ℝ)

theorem uniform_mem (d : ℕ) (hd : 0 < d) : uniform d ∈ Simplex d := by
  constructor
  · intro i
    dsimp [uniform]
    positivity
  · simp only [uniform, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem simplex_affine_card_le (d : ℕ) (s : Finset (Fin d → ℝ))
    (hS : (s : Set (Fin d → ℝ)) ⊆ Simplex d)
    (hi : AffineIndependent ℝ ((↑) : s → (Fin d → ℝ))) : s.card ≤ d := by
  classical
  let v : Fin d → (Fin d → ℝ) := fun i => Pi.single i 1
  let t : Finset (Fin d → ℝ) := Finset.univ.image v
  have hv : Function.Injective v := by
    intro i j hij
    by_contra hne
    have h := congrFun hij i
    simp [v, Pi.single_apply, hne, Ne.symm hne] at h
  have ht : (t : Set (Fin d → ℝ)) = Set.range v := by simp [t]
  have hc : t.card = d := by simp [t, Finset.card_image_of_injective _ hv]
  have hs : (s : Set (Fin d → ℝ)) ⊆ affineSpan ℝ (t : Set (Fin d → ℝ)) := by
    intro p hp
    apply convexHull_subset_affineSpan (t : Set (Fin d → ℝ))
    rw [ht, show Set.range v = Set.range (fun i : Fin d => Pi.single i (1 : ℝ)) from rfl,
      convexHull_rangle_single_eq_stdSimplex]
    exact hS hp
  exact (hi.card_le_card_of_subset_affineSpan hs).trans_eq hc

/-- 用零权重填充，精确保留有限支撑上所有标量函数的平均。 -/
theorem pad_simplex_mixture (d : ℕ) (hd : 0 < d) (s : Finset (Fin d → ℝ))
    (hS : (s : Set (Fin d → ℝ)) ⊆ Simplex d) (hcard : s.card ≤ d)
    (w : (Fin d → ℝ) → ℝ) (hw : ∀ p ∈ s, 0 ≤ w p) (h1 : (∑ p ∈ s, w p)=1) :
    ∃ (p : Fin d → Fin d → ℝ) (q : Fin d → ℝ),
      (∀ a, p a ∈ Simplex d) ∧ (∀ a, 0 ≤ q a) ∧ (∑ a, q a)=1 ∧
      ∀ f : (Fin d → ℝ) → ℝ, (∑ a, q a*f (p a))=∑ x ∈ s, w x*f x := by
  classical
  have hc : Fintype.card s ≤ d := by simpa using hcard
  let e : s ↪ Fin d := (Fintype.equivFin s).toEmbedding.trans (Fin.castLEEmb hc)
  let p : Fin d → Fin d → ℝ := Function.extend e (fun x : s => x.val) (fun _ => uniform d)
  let q : Fin d → ℝ := Function.extend e (fun x : s => w x.val) 0
  have hp : ∀ a, p a ∈ Simplex d := by
    intro a
    by_cases ha : ∃ x : s, e x=a
    · obtain ⟨x,rfl⟩ := ha
      simpa [p, e.injective.extend_apply] using hS x.property
    · rw [show p a=uniform d from Function.extend_apply' _ _ _ ha]
      exact uniform_mem d hd
  have hq : ∀ a, 0 ≤ q a := by
    intro a
    by_cases ha : ∃ x : s, e x=a
    · obtain ⟨x,rfl⟩ := ha
      simpa [q, e.injective.extend_apply] using hw x.val x.property
    · rw [show q a=0 from Function.extend_apply' _ _ _ ha]
  have hall (f : (Fin d → ℝ) → ℝ) :
      (∑ a, q a*f (p a))=∑ x ∈ s, w x*f x := by
    have he : (fun a => q a*f (p a)) =
        Function.extend e (fun x : s => w x.val*f x.val) 0 := by
      funext a
      by_cases ha : ∃ x : s, e x=a
      · obtain ⟨x,rfl⟩ := ha
        simp [p,q,e.injective.extend_apply]
      · simp [p,q,Function.extend_apply' _ _ _ ha]
    rw [he, sum_extend_zero_of_injective _ e.injective (fun _ => mem_univ _)]
    exact sum_attach s (fun x => w x*f x)
  refine ⟨p,q,hp,hq,?_,hall⟩
  have h := hall (fun _ => 1)
  simpa [h1] using h

/-- 任意有限概率混合，在保持重心时可由d点混合达到或提高其目标。 -/
theorem finite_mixture_reduce (d : ℕ) (hd : 0 < d) (g : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (s : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ)
    (hS : (s : Set (Fin d → ℝ)) ⊆ Simplex d) (hw : ∀ p ∈ s, 0 ≤ w p)
    (h1 : (∑ p ∈ s, w p)=1) (hx : (∑ p ∈ s, w p • p)=x) :
    ∃ (p : Fin d → Fin d → ℝ) (q : Fin d → ℝ),
      (∀ a, p a ∈ Simplex d) ∧ (∀ a, 0 ≤ q a) ∧ (∑ a, q a)=1 ∧
      (∀ i, (∑ a, q a*p a i)=x i) ∧ (∑ z ∈ s, w z*g z) ≤ ∑ a, q a*g (p a) := by
  obtain ⟨t,htS,htind,v,hv,hv1,hvx,hvg⟩ := reduce_support (Simplex d) g x
    (∑ z ∈ s, w z*g z) ⟨s,hS,w,hw,h1,hx,le_rfl⟩
  obtain ⟨p,q,hp,hq,hq1,hall⟩ := pad_simplex_mixture d hd t htS
    (simplex_affine_card_le d t htS htind) v hv hv1
  refine ⟨p,q,hp,hq,hq1,?_,?_⟩
  · intro i
    rw [hall (fun z => z i)]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun hvx i
  · rw [hall g]
    exact hvg

end FiniteCopy.ConvexRoof
