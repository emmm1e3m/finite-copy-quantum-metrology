import FiniteCopy.Primal
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open scoped BigOperators Topology
open Finset Set
set_option linter.deprecated false

noncomputable section
namespace FiniteCopy.ConvexRoof

def hypCone (d : ℕ) (g : (Fin d → ℝ) → ℝ) : Set ((Fin d → ℝ) × ℝ) :=
  {z | ∃ s : Finset (Fin d → ℝ), (s : Set (Fin d → ℝ)) ⊆ Simplex d ∧
    ∃ w : (Fin d → ℝ) → ℝ, (∀ p ∈ s, 0 ≤ w p) ∧
      (∑ p ∈ s, w p • p)=z.1 ∧ z.2 ≤ ∑ p ∈ s, w p*g p}

theorem sum_if_mem_of_subset {α V : Type*} [DecidableEq α] [AddCommMonoid V]
    (s t : Finset α) (hst : s ⊆ t) (f : α → V) :
    (∑ x ∈ t, if x ∈ s then f x else 0)=∑ x ∈ s, f x := by
  rw [← sum_subset hst (f := fun x => if x ∈ s then f x else 0)
    (fun x _ hx => if_neg hx)]
  exact sum_congr rfl (fun x hx => if_pos hx)

theorem sum_union_mix {E V : Type*} [DecidableEq E] [AddCommMonoid V] [Module ℝ V]
    (s t : Finset E) (w v : E → ℝ) (a b : ℝ) (f : E → V) :
    (∑ x ∈ s ∪ t, ((if x ∈ s then a*w x else 0)+(if x ∈ t then b*v x else 0)) • f x) =
      a • (∑ x ∈ s, w x • f x)+b • (∑ x ∈ t, v x • f x) := by
  simp only [add_smul,ite_smul,zero_smul,mul_smul,sum_add_distrib]
  rw [sum_if_mem_of_subset s (s∪t) subset_union_left,
    sum_if_mem_of_subset t (s∪t) subset_union_right, smul_sum, smul_sum]

theorem hypCone_convex (d : ℕ) (g : (Fin d → ℝ) → ℝ) : Convex ℝ (hypCone d g) := by
  classical
  rintro x ⟨s,hS,w,hw,hx,hvx⟩ y ⟨t,hT,v,hv,hy,hvy⟩ a b ha hb _
  let W := fun p => (if p ∈ s then a*w p else 0)+(if p ∈ t then b*v p else 0)
  refine ⟨s∪t, ?_, W, ?_, ?_, ?_⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hS hp
    · exact hT hp
  · intro p _
    dsimp [W]
    apply add_nonneg
    · split_ifs with h
      · exact mul_nonneg ha (hw p h)
      · rfl
    · split_ifs with h
      · exact mul_nonneg hb (hv p h)
      · rfl
  · change (∑ p ∈ s∪t, W p • p)=a • x.1+b • y.1
    rw [sum_union_mix, hx, hy]
  · change a*x.2+b*y.2 ≤ ∑ p ∈ s∪t, W p*g p
    have hs := sum_union_mix s t w v a b g
    simp only [smul_eq_mul] at hs
    rw [hs]
    exact add_le_add (mul_le_mul_of_nonneg_left hvx ha) (mul_le_mul_of_nonneg_left hvy hb)

theorem hypCone_zero (d : ℕ) (g : (Fin d → ℝ) → ℝ) : (0,0) ∈ hypCone d g := by
  refine ⟨∅, by simp, fun _ => 0, by simp, by simp, by simp⟩

theorem hypCone_down (d : ℕ) (g : (Fin d → ℝ) → ℝ) : (0,-1) ∈ hypCone d g := by
  refine ⟨∅, by simp, fun _ => 0, by simp, by simp, by norm_num⟩

theorem hypCone_graph (d : ℕ) (g : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ)
    (hp : p ∈ Simplex d) : (p,g p) ∈ hypCone d g := by
  classical
  refine ⟨{p}, ?_, fun _ => 1, by simp, by simp, by simp⟩
  simpa using hp

theorem hypCone_smul (d : ℕ) (g : (Fin d → ℝ) → ℝ) {z : (Fin d → ℝ) × ℝ}
    (hz : z ∈ hypCone d g) (a : ℝ) (ha : 0 ≤ a) : a • z ∈ hypCone d g := by
  obtain ⟨s,hS,w,hw,hx,hv⟩ := hz
  refine ⟨s,hS,fun p => a*w p,fun p hp => mul_nonneg ha (hw p hp), ?_, ?_⟩
  · change (∑ p ∈ s, (a*w p) • p)=a • z.1
    simp only [mul_smul, ← smul_sum, hx]
  · change a*z.2 ≤ ∑ p ∈ s, (a*w p)*g p
    simp only [mul_assoc, ← mul_sum]
    exact mul_le_mul_of_nonneg_left hv ha

theorem sum_fiber_weights {α E V : Type*} [Fintype α] [DecidableEq E]
    [AddCommMonoid V] [Module ℝ V] (p : α → E) (w : α → ℝ) (f : E → V) :
    (∑ x ∈ Finset.univ.image p, (∑ a, if p a=x then w a else 0) • f x)=∑ a, w a • f (p a) := by
  simp only [sum_smul,ite_smul,zero_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [mem_image_of_mem p (mem_univ a)]

theorem hypCone_indexed {α : Type*} [Fintype α] (d : ℕ) (g : (Fin d → ℝ) → ℝ)
    (p : α → Fin d → ℝ) (w : α → ℝ) (hp : ∀ a, p a ∈ Simplex d)
    (hw : ∀ a, 0 ≤ w a) :
    ((∑ a, w a • p a), (∑ a, w a*g (p a))) ∈ hypCone d g := by
  classical
  refine ⟨Finset.univ.image p, ?_, (fun x => ∑ a, if p a=x then w a else 0), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact hp a
  · intro x _
    apply sum_nonneg
    intro a _
    split_ifs
    · exact hw a
    · exact le_rfl
  · exact sum_fiber_weights p w id
  · exact le_of_eq (sum_fiber_weights p w g).symm

def vertex (d : ℕ) (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem hypCone_below_vertices (d : ℕ) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (t : ℝ) (ht : t ≤ ∑ i, x i*g (vertex d i)) :
    (x,t) ∈ hypCone d g := by
  have h := hypCone_indexed d g (vertex d) x
    (fun i => single_mem_stdSimplex ℝ i) hx
  have he : (∑ i, x i • vertex d i)=x := by
    ext j
    simp [vertex,Pi.single_apply,Finset.sum_apply,Pi.smul_apply]
  rw [he] at h
  obtain ⟨s,hS,w,hw,hx',hv⟩ := h
  exact ⟨s,hS,w,hw,hx',ht.trans hv⟩

theorem hypCone_interior_nonempty (d : ℕ) (g : (Fin d → ℝ) → ℝ) :
    (interior (hypCone d g)).Nonempty := by
  let U : Set ((Fin d → ℝ) × ℝ) :=
    {z | (∀ i, 0 < z.1 i) ∧ z.2 < ∑ i, z.1 i*g (vertex d i)}
  have hU : IsOpen U := by
    have hpos : IsOpen {z : (Fin d → ℝ) × ℝ | ∀ i, 0 < z.1 i} := by
      rw [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt continuous_const
        (show Continuous (fun z : (Fin d → ℝ) × ℝ => z.1 i) from
          (continuous_apply i).comp continuous_fst)
    have hgraph : IsOpen {z : (Fin d → ℝ) × ℝ |
        z.2 < ∑ i, z.1 i*g (vertex d i)} := by
      apply isOpen_lt continuous_snd
      exact continuous_finset_sum _ (fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul continuous_const)
    exact hpos.inter hgraph
  have hsub : U ⊆ hypCone d g := by
    intro z hz
    exact hypCone_below_vertices d g z.1 (fun i => (hz.1 i).le) z.2 hz.2.le
  let z : (Fin d → ℝ) × ℝ := (fun _ => 1, (∑ i, g (vertex d i))-1)
  have hz : z ∈ U := by
    constructor
    · intro i
      norm_num [z]
    · simp only [z,one_mul]
      linarith
  exact ⟨z, interior_maximal hsub hU hz⟩

end FiniteCopy.ConvexRoof
