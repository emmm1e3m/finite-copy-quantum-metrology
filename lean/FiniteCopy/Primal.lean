import FiniteCopy.SimplexReduction
import Mathlib.Topology.Order.Compact

open scoped BigOperators
open Finset Set
set_option linter.deprecated false

noncomputable section
namespace FiniteCopy.ConvexRoof

abbrev Param (d : ℕ) := (Fin d → Simplex d) × Simplex d

def mixMean {d : ℕ} (P : Param d) : Fin d → ℝ :=
  fun i => ∑ a, P.2.val a * (P.1 a).val i

def mixValue {d : ℕ} (g : (Fin d → ℝ) → ℝ) (P : Param d) : ℝ :=
  ∑ a, P.2.val a * g (P.1 a).val

theorem continuous_mixMean (d : ℕ) : Continuous (@mixMean d) := by
  apply continuous_pi
  intro i
  apply continuous_finset_sum
  intro a _
  apply Continuous.mul
  · exact (continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)
  · exact (continuous_apply i).comp (continuous_subtype_val.comp
      ((continuous_apply a).comp continuous_fst))

theorem continuous_mixValue (d : ℕ) (g : (Fin d → ℝ) → ℝ)
    (hg : ContinuousOn g (Simplex d)) : Continuous (mixValue g) := by
  have hrestr : Continuous (fun p : Simplex d => g p.val) :=
    (continuousOn_iff_continuous_restrict).mp hg
  unfold mixValue
  apply continuous_finset_sum
  intro a _
  apply Continuous.mul
  · exact (continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)
  · exact hrestr.comp ((continuous_apply a).comp continuous_fst)

/-- d点参数空间紧，消点定理使其中的最优者支配任意有限概率混合。 -/
theorem primal_attained (d : ℕ) (hd : 0 < d) (g : (Fin d → ℝ) → ℝ)
    (hg : ContinuousOn g (Simplex d)) :
    ∃ P : Param d, mixMean P=uniform d ∧
      ∀ (s : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ),
        (s : Set (Fin d → ℝ)) ⊆ Simplex d → (∀ p ∈ s, 0 ≤ w p) →
        (∑ p ∈ s, w p)=1 → (∑ p ∈ s, w p • p)=uniform d →
        (∑ p ∈ s, w p*g p) ≤ mixValue g P := by
  let A : Set (Param d) := {P | mixMean P=uniform d}
  have hA : IsCompact A := (isClosed_eq (continuous_mixMean d) continuous_const).isCompact
  have hne : A.Nonempty := by
    let u : Simplex d := ⟨uniform d, uniform_mem d hd⟩
    refine ⟨(fun _ => u,u), ?_⟩
    change mixMean (fun _ => u,u)=uniform d
    ext i
    change (∑ a, (uniform d a)*(uniform d i))=uniform d i
    rw [← sum_mul, (uniform_mem d hd).2, one_mul]
  obtain ⟨P,hP,hmax⟩ := hA.exists_isMaxOn hne (continuous_mixValue d g hg).continuousOn
  refine ⟨P,hP,?_⟩
  intro s w hS hw h1 hx
  obtain ⟨p,q,hp,hq,hq1,hmean,hval⟩ := finite_mixture_reduce d hd g (uniform d) s w hS hw h1 hx
  let Q : Param d := (fun a => ⟨p a,hp a⟩, ⟨q,hq,hq1⟩)
  have hQ : Q ∈ A := by
    apply funext
    intro i
    exact hmean i
  exact hval.trans (hmax hQ)

end FiniteCopy.ConvexRoof
