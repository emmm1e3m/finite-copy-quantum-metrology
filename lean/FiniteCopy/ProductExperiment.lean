import FiniteCopy.GaussianStatistics
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

-- 有限相位采用离散可测结构，联合测度是实轴体积与计数测度的乘积。
local instance phaseMeasurableSpace : MeasurableSpace (ZMod L) := ⊤
local instance phaseMeasurableSingleton : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

def gaussianOutcomeMeasure (L : ℕ) [NeZero L] : Measure (ℝ × ZMod L) := volume.prod Measure.count

def phaseCoordinate (a : Fin 2) : Bool := decide (a = 1)

@[simp] lemma phaseCoordinate_eq_iff (a b : Fin 2) : phaseCoordinate a = phaseCoordinate b ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

def gaussianOutcomeEffect (n : ℕ) (eps : ℝ) (z : ℝ × ZMod L) := spinEffect n eps z.1 z.2

def gaussianOutcomeProbability (n : ℕ) (eps : ℝ) (z : ℝ × ZMod L) : ℝ :=
  born (spinReference n) (gaussianOutcomeEffect n eps z)

def gaussianOutcomeTangent (n : ℕ) (eps : ℝ) (z : ℝ × ZMod L) (a : Fin 2) : ℝ :=
  born (spinTangent (spinCoefficient n) (phaseCoordinate a)) (gaussianOutcomeEffect n eps z)

def gaussianOutcomeEstimator (n : ℕ) (eps f : ℝ) (z : ℝ × ZMod L) (a : Fin 2) : ℝ :=
  phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) / f

lemma product_count_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : ℝ × ZMod L → E) (hc : ∀ k, Continuous fun t => f (t,k))
    (hi : ∀ k, Integrable fun t => f (t,k)) : Integrable f (gaussianOutcomeMeasure L) := by
  apply (integrable_prod_iff' (μ := volume) (ν := Measure.count)
    (measurable_from_prod_countable_left (fun k => (hc k).measurable)).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hi, integrable_count_iff.2 ((hasSum_fintype _).summable)⟩

lemma product_count_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × ZMod L → E) (hf : Integrable f (gaussianOutcomeMeasure L)) :
    (∫ z, f z ∂gaussianOutcomeMeasure L) = ∫ t, ∑ k : ZMod L, f (t,k) := by
  rw [gaussianOutcomeMeasure, integral_prod f hf]
  simp only [integral_count]

lemma gaussianOutcomeEffect_continuous (n : ℕ) (eps : ℝ) (k : ZMod L)
    (i j : Fin (n+1)) : Continuous fun t => gaussianOutcomeEffect n eps (t,k) i j := by
  have hc := spinColumn_continuous n eps
  simp only [gaussianOutcomeEffect, spinEffect, effect, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, rotatedSeed]
  fun_prop

theorem gaussianProduct_positive (n : ℕ) (eps : ℝ) (z : ℝ × ZMod L) :
    (gaussianOutcomeEffect n eps z).PosSemidef := spinEffect_positive n eps z.1 z.2

theorem gaussianProduct_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (i j : Fin (n+1)) :
    Integrable (fun z : ℝ × ZMod L => gaussianOutcomeEffect n eps z i j) (gaussianOutcomeMeasure L) :=
  product_count_integrable _ (fun k => gaussianOutcomeEffect_continuous n eps k i j)
    (fun k => spinEffect_integrable n heps k i j)

theorem gaussianProduct_complete (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hd : n+1 ≤ L) (i j : Fin (n+1)) :
    (∫ z : ℝ × ZMod L, gaussianOutcomeEffect n eps z i j ∂gaussianOutcomeMeasure L) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j := by
  rw [product_count_integral _ (gaussianProduct_integrable n heps i j)]
  exact congrFun (congrFun (spinEffect_complete n heps hd) i) j

lemma gaussianOutcomeProbability_eq (n : ℕ) (eps : ℝ) (z : ℝ × ZMod L) :
    gaussianOutcomeProbability n eps z = phaseProbability (L := L) (spinColumn n eps z.1) :=
  spin_born_reference _ z.2

lemma gaussianOutcomeTangent_eq (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (z : ℝ × ZMod L) (a : Fin 2) :
    gaussianOutcomeTangent n eps z a = phaseProbability (L := L) (spinColumn n eps z.1) *
      phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) := by
  rw [gaussianOutcomeTangent, gaussianOutcomeEffect, gaussian_effect_eq, spin_born_tangent]
  have hm := ne_of_gt (seedMass_pos _ (spinColumn_pos n heps z.1))
  dsimp [phaseProbability, phaseScore]
  field_simp

lemma gaussianOutcomeScore_continuous (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (k : ZMod L) (a : Fin 2) :
    Continuous fun t => phaseScore (spinCoefficient n) (spinColumn n eps t) k (phaseCoordinate a) :=
  continuous_phaseScore _ _ (spinColumn_continuous n eps)
    (fun t => ne_of_gt (seedMass_pos _ (spinColumn_pos n heps t))) k _

lemma gaussianProduct_first_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (a : Fin 2) : Integrable (fun z : ℝ × ZMod L =>
      phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a))
      (gaussianOutcomeMeasure L) := by
  apply product_count_integrable
  · intro k
    have hm := continuous_seedMass _ (spinColumn_continuous n eps)
    exact (hm.div_const _).mul (gaussianOutcomeScore_continuous n heps k a)
  · intro k
    exact (gaussian_statistics_integrable n heps k (phaseCoordinate a) (phaseCoordinate a)).2.1

lemma gaussianProduct_second_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (a b : Fin 2) : Integrable (fun z : ℝ × ZMod L =>
      phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate b))
      (gaussianOutcomeMeasure L) := by
  apply product_count_integrable
  · intro k
    have hm := continuous_seedMass _ (spinColumn_continuous n eps)
    exact ((hm.div_const _).mul (gaussianOutcomeScore_continuous n heps k a)).mul
      (gaussianOutcomeScore_continuous n heps k b)
  · intro k
    exact (gaussian_statistics_integrable n heps k (phaseCoordinate a) (phaseCoordinate b)).2.2

lemma gaussianProduct_first (n : ℕ) {eps : ℝ} (heps : 0 < eps) (hL : 3 ≤ L) (a : Fin 2) :
    (∫ z : ℝ × ZMod L, phaseProbability (L := L) (spinColumn n eps z.1) *
      phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a)
      ∂gaussianOutcomeMeasure L) = 0 := by
  rw [product_count_integral _ (gaussianProduct_first_integrable n heps a)]
  simp_rw [phaseScore_mean hL]
  simp

lemma gaussianProduct_second (n : ℕ) {eps : ℝ} (heps : 0 < eps) (hL : 3 ≤ L) (a b : Fin 2) :
    (∫ z : ℝ × ZMod L, phaseProbability (L := L) (spinColumn n eps z.1) *
      phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate a) *
      phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate b)
      ∂gaussianOutcomeMeasure L) = if a = b then gaussianFisher n eps else 0 := by
  rw [product_count_integral _ (gaussianProduct_second_integrable n heps a b)]
  simp_rw [phaseScore_second hL _ _ (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps _))),
    phaseCoordinate_eq_iff]
  by_cases hab : a = b
  · simp only [hab, ite_true, gaussianFisher, integratedSpinFisher]
  · simp [hab]

end CopyQuantumMetrology

