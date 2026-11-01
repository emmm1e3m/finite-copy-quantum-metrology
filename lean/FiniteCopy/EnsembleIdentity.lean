import FiniteCopy.OptimizationObjects
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

namespace PureEnsemble
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def toPOVM (E : PureEnsemble n Ω μ) : DensityPOVM (Fin (n+1)) Ω μ where
  effect z := ((n+1 : ℝ) * E.probability z) • rankOne (E.state z)
  positive z := (Matrix.posSemidef_vecMulVec_self_star _).smul
    (mul_nonneg (by positivity) (E.nonneg z))
  integrable := E.integrable
  complete := E.complete

lemma born_observable (E : PureEnsemble n Ω μ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (z : Ω) :
    born A (E.toPOVM.effect z) =
      (n+1) * E.probability z * (quadratic A (E.state z)).re := by
  rw [toPOVM, born_smul_right]
  simp only [born, trace_mul_rankOne]

lemma born_probability (E : PureEnsemble n Ω μ) (z : Ω) :
    born (POVM.state n) (E.toPOVM.effect z) = E.probability z := by
  rw [← spinReference_eq_state, toPOVM, born_smul_right]
  simp only [spinReference, born_maximallyMixed_rankOne, E.normalized]
  field_simp

lemma probability_integrable (E : PureEnsemble n Ω μ) : Integrable E.probability μ := by
  have h := (trace_mul_integrable μ E.toPOVM.effect (POVM.state n) E.integrable).re
  change Integrable (fun z => born (POVM.state n) (E.toPOVM.effect z)) μ at h
  simpa only [E.born_probability] using h

lemma probability_integral (E : PureEnsemble n Ω μ) : (∫ z, E.probability z ∂μ) = 1 := by
  simp_rw [← E.born_probability]
  exact born_density_normalized μ n E.toPOVM.effect E.integrable E.complete

lemma born_tangent (E : PureEnsemble n Ω μ) (a : Fin 2) (z : Ω) :
    born (if a=0 then tangentX n (Algebra.spinEdge n) else tangentY n (Algebra.spinEdge n))
      (E.toPOVM.effect z) =
      2 * E.probability z *
        (quadratic (spinObservable (spinCoefficient n) (phaseCoordinate a)) (E.state z)).re := by
  rw [← spinTangent_eq_canonical, toPOVM, born_smul_right]
  simp only [spinTangent, born_tangent_rankOne]
  have hd : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

lemma fisher_pointwise (E : PureEnsemble n Ω μ) (z : Ω) :
    fisherDensity n (Algebra.spinEdge n) (E.toPOVM.effect z) =
      4 * E.probability z *
        ((quadratic (spinX (spinCoefficient n)) (E.state z)).re ^ 2 +
         (quadratic (spinY (spinCoefficient n)) (E.state z)).re ^ 2) := by
  have hx := E.born_tangent 0 z
  have hy := E.born_tangent 1 z
  simp [phaseCoordinate, spinObservable] at hx hy
  rw [fisherDensity, hx, hy, E.born_probability]
  by_cases hp : E.probability z = 0
  · simp [hp]
  · field_simp
    <;> ring

lemma variance_pointwise (E : PureEnsemble n Ω μ) (z : Ω) :
    E.probability z *
      (pureVariance (spinX (spinCoefficient n)) (E.state z) +
       pureVariance (spinY (spinCoefficient n)) (E.state z)) =
      (born (spinX (spinCoefficient n) * spinX (spinCoefficient n)) (E.toPOVM.effect z) +
       born (spinY (spinCoefficient n) * spinY (spinCoefficient n)) (E.toPOVM.effect z)) /
        (n+1) - fisherDensity n (Algebra.spinEdge n) (E.toPOVM.effect z) / 4 := by
  simp only [pureVariance, normalizedMoment, E.normalized, div_one,
    E.born_observable, E.fisher_pointwise]
  have hd : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

lemma variance_integrable (E : PureEnsemble n Ω μ) :
    Integrable (fun z => E.probability z *
      (pureVariance (spinX (spinCoefficient n)) (E.state z) +
       pureVariance (spinY (spinCoefficient n)) (E.state z))) μ := by
  simp_rw [E.variance_pointwise]
  apply Integrable.sub
  · exact ((trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re.add
      (trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re).div_const _
  · exact (canonical_arbitrary_density_fisher_bound μ n E.toPOVM.effect
      E.toPOVM.positive E.integrable E.complete).1.div_const 4

theorem fisher_variance (E : PureEnsemble n Ω μ) :
    (∫ z, fisherDensity n (Algebra.spinEdge n) (E.toPOVM.effect z) ∂μ) =
      (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - 4 * E.variance := by
  have hf := (canonical_arbitrary_density_fisher_bound μ n E.toPOVM.effect
    E.toPOVM.positive E.integrable E.complete).1
  have hb (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
      (∫ z, born A (E.toPOVM.effect z) ∂μ) = (Matrix.trace A).re := by
    have h := integral_re (trace_mul_integrable μ E.toPOVM.effect A E.integrable)
    simp only [RCLike.re_eq_complex_re] at h
    unfold born
    rw [h, integral_trace_mul μ E.toPOVM.effect A E.integrable E.complete]
  have hv : E.variance =
      ((Matrix.trace (spinX (spinCoefficient n) * spinX (spinCoefficient n))).re +
       (Matrix.trace (spinY (spinCoefficient n) * spinY (spinCoefficient n))).re) /
       (n+1) - (∫ z, fisherDensity n (Algebra.spinEdge n) (E.toPOVM.effect z) ∂μ)/4 := by
    unfold variance
    simp_rw [E.variance_pointwise]
    rw [integral_sub,
      integral_div, integral_add, hb, hb, integral_div]
    · exact (trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re
    · exact (trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re
    · exact ((trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re.add
        (trace_mul_integrable μ E.toPOVM.effect _ E.integrable).re).div_const _
    · exact hf.div_const 4
  rw [spin_trace_value] at hv
  have hd : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp at hv
  nlinarith

end PureEnsemble
end FiniteCopy.Optimization

