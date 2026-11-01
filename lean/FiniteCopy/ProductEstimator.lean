import FiniteCopy.ProductExperiment
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]
local instance : MeasurableSpace (ZMod L) := ⊤
local instance : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

lemma gaussian_estimator_mean_point (n : ℕ) (eps f : ℝ) (z : ℝ × ZMod L) (a : Fin 2) :
    gaussianOutcomeProbability n eps z * gaussianOutcomeEstimator n eps f z a =
      (phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a)) / f := by
  rw [gaussianOutcomeProbability_eq]
  unfold gaussianOutcomeEstimator
  ring

lemma gaussian_estimator_second_point (n : ℕ) (eps f : ℝ) (z : ℝ × ZMod L) (a b : Fin 2) :
    gaussianOutcomeProbability n eps z * gaussianOutcomeEstimator n eps f z a *
      gaussianOutcomeEstimator n eps f z b =
      (phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate b)) / (f*f) := by
  rw [gaussianOutcomeProbability_eq]
  unfold gaussianOutcomeEstimator
  ring

lemma gaussian_estimator_cross_point (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (f : ℝ) (z : ℝ × ZMod L) (a b : Fin 2) :
    gaussianOutcomeEstimator n eps f z a * gaussianOutcomeTangent n eps z b =
      (phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate b)) / f := by
  rw [gaussianOutcomeTangent_eq n heps]
  unfold gaussianOutcomeEstimator
  ring

theorem gaussianProduct_estimator_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (f : ℝ) :
    (∀ a, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeProbability n eps z *
      gaussianOutcomeEstimator n eps f z a) (gaussianOutcomeMeasure L)) ∧
    (∀ a, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeProbability n eps z *
      (gaussianOutcomeEstimator n eps f z a)^2) (gaussianOutcomeMeasure L)) ∧
    (∀ a b, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeEstimator n eps f z a *
      gaussianOutcomeTangent n eps z b) (gaussianOutcomeMeasure L)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp_rw [gaussian_estimator_mean_point]
    exact (gaussianProduct_first_integrable n heps a).div_const f
  · intro a
    simp_rw [pow_two, ← mul_assoc, gaussian_estimator_second_point]
    exact (gaussianProduct_second_integrable n heps a a).div_const (f*f)
  · intro a b
    simp_rw [gaussian_estimator_cross_point n heps]
    exact (gaussianProduct_second_integrable n heps a b).div_const f

theorem gaussianProduct_estimator_mean (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (f : ℝ) (a : Fin 2) :
    (∫ z : ℝ × ZMod L, gaussianOutcomeProbability n eps z *
      gaussianOutcomeEstimator n eps f z a ∂gaussianOutcomeMeasure L) = 0 := by
  simp_rw [gaussian_estimator_mean_point]
  rw [integral_div, gaussianProduct_first n heps hL, zero_div]

theorem gaussianProduct_estimator_cross (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (f : ℝ) (a b : Fin 2) :
    (∫ z : ℝ × ZMod L, gaussianOutcomeEstimator n eps f z a *
      gaussianOutcomeTangent n eps z b ∂gaussianOutcomeMeasure L) =
      if a = b then gaussianFisher n eps / f else 0 := by
  simp_rw [gaussian_estimator_cross_point n heps]
  rw [integral_div, gaussianProduct_second n heps hL]
  split_ifs <;> simp

theorem gaussianProduct_estimator_covariance (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (f : ℝ) (a b : Fin 2) :
    (∫ z : ℝ × ZMod L, gaussianOutcomeProbability n eps z *
      gaussianOutcomeEstimator n eps f z a * gaussianOutcomeEstimator n eps f z b
      ∂gaussianOutcomeMeasure L) = if a = b then gaussianFisher n eps / (f*f) else 0 := by
  simp_rw [gaussian_estimator_second_point]
  rw [integral_div, gaussianProduct_second n heps hL]
  split_ifs <;> simp

-- 与035 MomentUnbiased的五个字段逐项一致，无循环导入。
theorem gaussianProduct_moment_unbiased (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) :
    (∀ a, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeProbability n eps z *
      gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a) (gaussianOutcomeMeasure L)) ∧
    (∀ a, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeProbability n eps z *
      (gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a)^2) (gaussianOutcomeMeasure L)) ∧
    (∀ a b, Integrable (fun z : ℝ × ZMod L => gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a *
      gaussianOutcomeTangent n eps z b) (gaussianOutcomeMeasure L)) ∧
    (∀ a, (∫ z : ℝ × ZMod L, gaussianOutcomeProbability n eps z *
      gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a ∂gaussianOutcomeMeasure L) = 0) ∧
    (∀ a b, (∫ z : ℝ × ZMod L, gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a *
      gaussianOutcomeTangent n eps z b ∂gaussianOutcomeMeasure L) = if a = b then 1 else 0) := by
  have hi := gaussianProduct_estimator_integrable (L := L) n heps (gaussianFisher n eps)
  refine ⟨hi.1, hi.2.1, hi.2.2, gaussianProduct_estimator_mean n heps hL _, ?_⟩
  intro a b
  rw [gaussianProduct_estimator_cross n heps hL]
  simp [ne_of_gt (gaussianFisher_pos hn heps)]

end CopyQuantumMetrology

