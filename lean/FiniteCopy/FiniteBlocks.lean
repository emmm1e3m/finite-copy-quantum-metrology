import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace FiniteCopy.GaussianLift

variable {B Ω : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
variable [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

-- 块标签采用计数测度；有限和形式避免额外假定联合可测性。
lemma count_prod_eq_sum_map :
    (Measure.count : Measure B).prod μ = ∑ b : B, μ.map (Prod.mk b) := by
  rw [Measure.count, Measure.prod_sum_left, Measure.sum_fintype]
  simp_rw [Measure.dirac_prod]

lemma count_prod_integrable {E : Type*} [NormedAddCommGroup E]
    (f : B × Ω → E) (hi : ∀ b, Integrable (fun z => f (b,z)) μ) :
    Integrable f ((Measure.count : Measure B).prod μ) := by
  rw [count_prod_eq_sum_map]
  apply integrable_finsetSum_measure.2
  intro b hb
  exact (measurableEmbedding_prodMk_left b).integrable_map_iff.2 (hi b)

lemma count_prod_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : B × Ω → E) (hi : ∀ b, Integrable (fun z => f (b,z)) μ) :
    (∫ z, f z ∂(Measure.count : Measure B).prod μ) = ∑ b : B, ∫ z, f (b,z) ∂μ := by
  rw [count_prod_eq_sum_map, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (measurableEmbedding_prodMk_left b).integral_map f
  · intro b hb
    exact (measurableEmbedding_prodMk_left b).integrable_map_iff.2 (hi b)

end FiniteCopy.GaussianLift

