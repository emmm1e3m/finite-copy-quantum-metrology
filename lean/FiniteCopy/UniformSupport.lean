import FiniteCopy.HypographCone
open scoped BigOperators Topology
open Finset Set
set_option linter.deprecated false

noncomputable section
namespace FiniteCopy.ConvexRoof

theorem mass_of_simplex_barycenter (d : ℕ) (hd : 0 < d)
    (s : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ)
    (hS : (s : Set (Fin d → ℝ)) ⊆ Simplex d)
    (hx : (∑ p ∈ s, w p • p)=uniform d) : (∑ p ∈ s, w p)=1 := by
  have h := congrArg (fun z : Fin d → ℝ => ∑ i, z i) hx
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h
  rw [sum_comm] at h
  have he : (∑ p ∈ s, ∑ i, w p*p i)=∑ p ∈ s, w p := by
    apply sum_congr rfl
    intro p hp
    rw [← mul_sum, (hS hp).2, mul_one]
  rw [he, (uniform_mem d hd).2] at h
  exact h

theorem param_mem_hypCone (d : ℕ) (g : (Fin d → ℝ) → ℝ) (P : Param d) :
    (mixMean P,mixValue g P) ∈ hypCone d g := by
  have h := hypCone_indexed d g (fun a => (P.1 a).val) P.2.val
    (fun a => (P.1 a).property) P.2.property.1
  have he : (∑ a, P.2.val a • (P.1 a).val)=mixMean P := by
    ext i
    simp [mixMean,Finset.sum_apply,Pi.smul_apply]
  simpa only [he,mixValue] using h

theorem dual_coordinates (d : ℕ) (f : StrongDual ℝ ((Fin d → ℝ) × ℝ))
    (p : Fin d → ℝ) (t : ℝ) :
    f (p,t)=(∑ i, p i*f (vertex d i,0))+t*f (0,1) := by
  classical
  have he : (p,t)=(∑ i, p i • (vertex d i,(0 : ℝ)))+t • (0,1) := by
    apply Prod.ext
    · ext j
      simp [vertex,Pi.single_apply,Finset.sum_apply,Pi.smul_apply,Prod.fst_sum]
    · simp [Prod.snd_sum]
  rw [he,map_add,map_sum]
  simp only [map_smul,smul_eq_mul]

/-- 连续目标在均匀重心处的真实最优混合，以及同值的共同线性上界。 -/
theorem exists_uniform_support (d : ℕ) (hd : 0 < d)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (stdSimplex ℝ (Fin d))) :
    ∃ (p : Fin d → Fin d → ℝ) (q lam : Fin d → ℝ),
      (∀ a, p a ∈ stdSimplex ℝ (Fin d)) ∧
      (∀ a, 0 ≤ q a) ∧ (∑ a, q a)=1 ∧
      (∀ i, (∑ a, q a*p a i)=1/(d : ℝ)) ∧
      (∀ p ∈ stdSimplex ℝ (Fin d), g p ≤ ∑ i, lam i*p i) ∧
      (∑ a, q a*g (p a))=(∑ i, lam i)/(d : ℝ) := by
  classical
  obtain ⟨P,hmean,hmax⟩ := primal_attained d hd g hg
  let v := mixValue g P
  have hbound : ∀ t : ℝ, (uniform d,t) ∈ hypCone d g → t ≤ v := by
    intro t ht
    obtain ⟨s,hS,w,hw,hx,hval⟩ := ht
    exact hval.trans (hmax s w hS hw (mass_of_simplex_barycenter d hd s w hS hx) hx)
  have hpoint : (uniform d,v) ∈ hypCone d g := by
    simpa only [hmean] using param_mem_hypCone d g P
  have hboundary : (uniform d,v) ∉ interior (hypCone d g) := by
    intro hin
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hin)
    have hmem : (uniform d,v+ε/2) ∈ Metric.ball (uniform d,v) ε := by
      rw [Metric.mem_ball,Prod.dist_eq]
      simp only [dist_self,Real.dist_eq,add_sub_cancel_left]
      rw [abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
      exact half_lt_self hε
    have hh := hbound (v+ε/2) (hball hmem)
    linarith
  obtain ⟨f,hf,hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (hypCone_convex d g) hboundary (hypCone_interior_nonempty d g)
  have hfpoint : f (uniform d,v)=0 := by
    have h0 := hsep (0,0) (hypCone_zero d g)
    have h2 := hsep (2 • (uniform d,v)) (hypCone_smul d g hpoint 2 (by norm_num))
    simp only [show ((0 : Fin d → ℝ),(0 : ℝ))=0 from rfl, map_zero] at h0
    simp only [map_smul,smul_eq_mul] at h2
    linarith
  have hnonpos : ∀ z ∈ hypCone d g, f z ≤ 0 := by
    intro z hz
    simpa only [hfpoint] using hsep z hz
  let A : Fin d → ℝ := fun i => f (vertex d i,0)
  let c : ℝ := f (0,1)
  have hc0 : 0 ≤ c := by
    have h := hnonpos (0,-1) (hypCone_down d g)
    have he : ((0 : Fin d → ℝ),(-1 : ℝ))= -((0 : Fin d → ℝ),(1 : ℝ)) := by simp
    rw [he,map_neg] at h
    exact neg_nonpos.mp h
  have hcs : c ≠ 0 := by
    intro hc
    have hA : ∀ i, A i ≤ 0 := by
      intro i
      have h := hnonpos (vertex d i,g (vertex d i))
        (hypCone_graph d g (vertex d i) (single_mem_stdSimplex ℝ i))
      have he : (vertex d i,g (vertex d i))=
          (vertex d i,(0 : ℝ))+g (vertex d i) • (0,1) := by
        ext <;> simp
      rw [he,map_add,map_smul] at h
      change A i+g (vertex d i)*c ≤ 0 at h
      simpa only [hc,mul_zero,add_zero] using h
    have hs : (∑ i, A i)=0 := by
      rw [dual_coordinates] at hfpoint
      change (∑ i, (1/(d : ℝ))*A i)+v*c=0 at hfpoint
      rw [hc,mul_zero,add_zero,← mul_sum] at hfpoint
      exact (mul_eq_zero.mp hfpoint).resolve_left (one_div_ne_zero (by exact_mod_cast hd.ne'))
    have hAz : ∀ i, A i=0 := by
      intro i
      have hle := sum_le_sum_of_subset_of_nonpos (s := {i}) (t := Finset.univ)
        (singleton_subset_iff.mpr (mem_univ i)) (fun j _ _ => hA j)
      simp only [sum_singleton,hs] at hle
      exact le_antisymm (hA i) hle
    apply hf
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨p,t⟩
    change f (p,t)=0
    rw [dual_coordinates]
    change (∑ i, p i*A i)+t*c=0
    simp only [hAz,hc,mul_zero,sum_const_zero,add_zero]
  have hc : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcs)
  let lam : Fin d → ℝ := fun i => -A i/c
  have hlam (p : Fin d → ℝ) : (∑ i, lam i*p i)= -(∑ i, p i*A i)/c := by
    simp only [lam,div_mul_eq_mul_div,← sum_div,← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  have hmajor : ∀ p ∈ Simplex d, g p ≤ ∑ i, lam i*p i := by
    intro p hp
    have h := hnonpos (p,g p) (hypCone_graph d g p hp)
    rw [dual_coordinates] at h
    change (∑ i, p i*A i)+g p*c ≤ 0 at h
    rw [hlam,le_div_iff₀ hc]
    linarith
  have hvalue : v=(∑ i, lam i)/(d : ℝ) := by
    have he : v=∑ i, lam i*uniform d i := by
      rw [hlam,eq_div_iff (ne_of_gt hc)]
      rw [dual_coordinates] at hfpoint
      change (∑ i, uniform d i*A i)+v*c=0 at hfpoint
      linarith
    rw [he]
    simp only [uniform,mul_one_div,← sum_div]
  refine ⟨fun a => (P.1 a).val,P.2.val,lam,fun a => (P.1 a).property,
    P.2.property.1,P.2.property.2,?_,hmajor,hvalue⟩
  intro i
  exact congrFun hmean i

end FiniteCopy.ConvexRoof
