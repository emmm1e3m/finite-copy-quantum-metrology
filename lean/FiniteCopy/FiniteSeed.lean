import FiniteCopy.GaussianRisk
import FiniteCopy.SpinTrace
import Mathlib.Analysis.Convex.StdSimplex

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder Classical
noncomputable section
namespace FiniteCopy.SeedPOVM
open CopyQuantumMetrology FiniteCopy.Risk

/-- 有限单纯形方案；零权重保留，不附加正权重假设。 -/
structure Scheme (n k : ℕ) where
  p : Fin k → Fin (n+1) → ℝ
  q : Fin k → ℝ
  p_simplex : ∀ a, p a ∈ stdSimplex ℝ (Fin (n+1))
  q_nonneg : ∀ a, 0 ≤ q a
  q_sum : ∑ a, q a = 1
  population_mean : ∀ i, ∑ a, q a * p a i = 1 / ((n : ℝ)+1)

namespace Scheme
variable {n k L : ℕ} [NeZero L]
local instance : MeasurableSpace (ZMod L) := ⊤
local instance : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

def amplitude (S : Scheme n k) (a : Fin k) (i : Fin (n+1)) : ℝ := Real.sqrt (S.p a i)
def gamma (S : Scheme n k) (a : Fin k) : ℝ := seedMoment (spinCoefficient n) (S.amplitude a)
def value (S : Scheme n k) : ℝ := ∑ a, S.q a * S.gamma a ^ 2
def totalFisher (S : Scheme n k) : ℝ := 4 * S.value

theorem amplitude_sq (S : Scheme n k) (a : Fin k) (i : Fin (n+1)) :
    S.amplitude a i ^ 2 = S.p a i := Real.sq_sqrt ((S.p_simplex a).1 i)

theorem amplitude_mass (S : Scheme n k) (a : Fin k) : seedMass (S.amplitude a) = 1 := by
  simp only [seedMass, S.amplitude_sq]
  exact (S.p_simplex a).2

def outcomeEffect (S : Scheme n k) (z : Fin k × ZMod L) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (((n : ℝ)+1) * S.q z.1) • seedPhaseEffect (S.amplitude z.1) z.2

def probability (S : Scheme n k) (z : Fin k × ZMod L) : ℝ :=
  born (spinReference n) (S.outcomeEffect z)

def tangent (S : Scheme n k) (z : Fin k × ZMod L) (a : Fin 2) : ℝ :=
  born (spinTangent (spinCoefficient n) (phaseCoordinate a)) (S.outcomeEffect z)

def simpleScore (S : Scheme n k) (z : Fin k × ZMod L) (a : Fin 2) : ℝ :=
  phaseScore (spinCoefficient n) (S.amplitude z.1) z.2 (phaseCoordinate a)

def outcomeScore (S : Scheme n k) : (Fin k × ZMod L) → Fin 2 → ℝ :=
  FiniteCopy.Risk.score S.probability S.tangent

theorem finite_integrable {E : Type*} [NormedAddCommGroup E]
    (f : Fin k × ZMod L → E) : Integrable f Measure.count :=
  integrable_count_iff.mpr (hasSum_fintype (fun z => ‖f z‖)).summable

theorem outcomeEffect_positive (S : Scheme n k) (z : Fin k × ZMod L) :
    (S.outcomeEffect z).PosSemidef :=
  (effect_positive _ _ _).smul (mul_nonneg (by positivity) (S.q_nonneg z.1))

theorem phase_effect_sum (S : Scheme n k) (hd : n+1 ≤ L) (a : Fin k)
    (i j : Fin (n+1)) :
    (∑ l : ZMod L, seedPhaseEffect (S.amplitude a) l i j) =
      if i=j then (S.p a i : ℂ) else 0 := by
  have h := phase_average_effect (L := L) (fun i => (S.amplitude a i : ℂ))
    spinFrequency (PhaseMoments.fin_neg_zmod_injective hd) i j
  simpa only [seedPhaseEffect, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← pow_two, ← Complex.ofReal_pow, S.amplitude_sq] using h

theorem outcomeEffect_complete (S : Scheme n k) (hd : n+1 ≤ L) :
    (∑ z : Fin k × ZMod L, S.outcomeEffect z) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, outcomeEffect, Matrix.smul_apply,
    ← Finset.smul_sum, S.phase_effect_sum hd]
  by_cases hij : i=j
  · subst j
    simp only [ite_true, RCLike.real_smul_eq_coe_mul, Matrix.one_apply_eq]
    have h : ∑ a, (((n : ℝ)+1) * S.q a) * S.p a i = 1 := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, S.population_mean]
      field_simp
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul]
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_one] using
      congrArg (fun x : ℝ => (x : ℂ)) h
  · simp [hij, Matrix.one_apply]

def densityPOVM (S : Scheme n k) (hd : n+1 ≤ L) :
    DensityPOVM (Fin (n+1)) (Fin k × ZMod L) Measure.count where
  effect := S.outcomeEffect
  positive := S.outcomeEffect_positive
  integrable := fun i j => finite_integrable _
  complete := by
    intro i j
    rw [integral_count]
    simpa only [Matrix.sum_apply] using congrFun (congrFun (S.outcomeEffect_complete hd) i) j

theorem probability_scaled (S : Scheme n k) (z : Fin k × ZMod L) :
    S.probability z = (((n : ℝ)+1) * S.q z.1) * phaseProbability (L := L) (S.amplitude z.1) := by
  rw [probability, outcomeEffect, born_smul_right, spin_born_reference]

theorem probability_eq (S : Scheme n k) (z : Fin k × ZMod L) :
    S.probability z = S.q z.1 / L := by
  rw [S.probability_scaled]
  simp only [phaseProbability, S.amplitude_mass]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem tangent_eq (S : Scheme n k) (z : Fin k × ZMod L) (a : Fin 2) :
    S.tangent z a = S.probability z * S.simpleScore z a := by
  rw [tangent, outcomeEffect, born_smul_right, spin_born_tangent, S.probability_scaled]
  simp only [simpleScore, phaseProbability, phaseScore, S.amplitude_mass]
  ring

theorem probability_nonneg (S : Scheme n k) (z : Fin k × ZMod L) : 0 ≤ S.probability z := by
  rw [S.probability_eq]
  exact div_nonneg (S.q_nonneg _) (Nat.cast_nonneg _)

theorem weighted_score (S : Scheme n k) (z : Fin k × ZMod L) (a : Fin 2) :
    S.probability z * S.outcomeScore z a = S.probability z * S.simpleScore z a := by
  unfold outcomeScore FiniteCopy.Risk.score
  rw [S.tangent_eq]
  by_cases hp : S.probability z = 0
  · simp [hp]
  · field_simp

theorem weighted_second (S : Scheme n k) (z : Fin k × ZMod L) (a b : Fin 2) :
    S.probability z * S.outcomeScore z a * S.outcomeScore z b =
      S.probability z * S.simpleScore z a * S.simpleScore z b := by
  by_cases hp : S.probability z = 0
  · simp [hp]
  · have hs (c : Fin 2) : S.outcomeScore z c = S.simpleScore z c := by
      unfold outcomeScore FiniteCopy.Risk.score
      rw [S.tangent_eq]
      field_simp
    rw [hs a, hs b]

theorem phase_first (S : Scheme n k) (hL : 3 ≤ L) (a : Fin k) (b : Fin 2) :
    (∑ l : ZMod L, S.probability (a,l) * S.simpleScore (a,l) b) = 0 := by
  have he (l : ZMod L) : S.probability (a,l) * S.simpleScore (a,l) b =
      (((n : ℝ)+1) * S.q a) * (phaseProbability (L := L) (S.amplitude a) *
        phaseScore (spinCoefficient n) (S.amplitude a) l (phaseCoordinate b)) := by
    rw [S.probability_scaled]
    unfold simpleScore
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, phaseScore_mean hL, mul_zero]

theorem phase_second (S : Scheme n k) (hL : 3 ≤ L) (a : Fin k) (b c : Fin 2) :
    (∑ l : ZMod L, S.probability (a,l) * S.simpleScore (a,l) b * S.simpleScore (a,l) c) =
      if b=c then 2 * S.q a * S.gamma a ^ 2 else 0 := by
  have hm : seedMass (S.amplitude a) ≠ 0 := by rw [S.amplitude_mass]; norm_num
  have he (l : ZMod L) : S.probability (a,l) * S.simpleScore (a,l) b * S.simpleScore (a,l) c =
      (((n : ℝ)+1) * S.q a) * (phaseProbability (L := L) (S.amplitude a) *
        phaseScore (spinCoefficient n) (S.amplitude a) l (phaseCoordinate b) *
        phaseScore (spinCoefficient n) (S.amplitude a) l (phaseCoordinate c)) := by
    rw [S.probability_scaled]
    unfold simpleScore
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, phaseScore_second hL _ _ hm]
  simp only [phaseCoordinate_eq_iff]
  by_cases hbc : b=c
  · simp only [hbc, ite_true, seedFisher, S.amplitude_mass, mul_one, gamma]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  · simp [hbc]

theorem score_mean (S : Scheme n k) (hL : 3 ≤ L) (a : Fin 2) :
    (∫ z : Fin k × ZMod L, S.probability z * S.outcomeScore z a ∂Measure.count) = 0 := by
  simp_rw [S.weighted_score]
  rw [integral_count, Fintype.sum_prod_type]
  simp_rw [S.phase_first hL]
  simp

theorem fisher_entry (S : Scheme n k) (hL : 3 ≤ L) (a b : Fin 2) :
    fisherEntry (Measure.count : Measure (Fin k × ZMod L)) S.probability S.outcomeScore a b =
      if a=b then 2 * S.value else 0 := by
  unfold fisherEntry
  simp_rw [S.weighted_second]
  rw [integral_count, Fintype.sum_prod_type]
  simp_rw [S.phase_second hL]
  by_cases hab : a=b
  · simp only [hab, ite_true, value, mul_assoc, Finset.mul_sum]
  · simp [hab]

theorem fisher_matrix (S : Scheme n k) (hL : 3 ≤ L) :
    (fun a b : Fin 2 => fisherEntry (Measure.count : Measure (Fin k × ZMod L)) S.probability S.outcomeScore a b) =
      (2 * S.value) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  rw [S.fisher_entry hL]
  simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite]

theorem fisher_trace (S : Scheme n k) (hL : 3 ≤ L) :
    FiniteCopy.POVM.statisticalFisherTrace (Measure.count : Measure (Fin k × ZMod L)) S.probability S.outcomeScore = S.totalFisher := by
  unfold FiniteCopy.POVM.statisticalFisherTrace
  have he (z : Fin k × ZMod L) : S.probability z * ((S.outcomeScore z 0)^2 + (S.outcomeScore z 1)^2) =
      S.probability z * S.outcomeScore z 0 * S.outcomeScore z 0 +
        S.probability z * S.outcomeScore z 1 * S.outcomeScore z 1 := by ring
  simp_rw [he]
  rw [integral_add (finite_integrable _) (finite_integrable _)]
  change fisherEntry Measure.count S.probability S.outcomeScore 0 0 +
    fisherEntry Measure.count S.probability S.outcomeScore 1 1 = _
  rw [S.fisher_entry hL, S.fisher_entry hL]
  simp [totalFisher]
  ring

def estimator (S : Scheme n k) (z : Fin k × ZMod L) (a : Fin 2) : ℝ :=
  S.outcomeScore z a / (2 * S.value)

theorem diagonal_ne_zero (S : Scheme n k) (hT : 0 < S.totalFisher) : 2 * S.value ≠ 0 := by
  unfold totalFisher at hT
  nlinarith

theorem estimator_mean (S : Scheme n k) (hL : 3 ≤ L) (a : Fin 2) :
    (∫ z : Fin k × ZMod L, S.probability z * S.estimator z a ∂Measure.count) = 0 := by
  simp only [estimator, ← mul_div_assoc, integral_div, S.score_mean hL, zero_div]

theorem estimator_cross (S : Scheme n k) (hL : 3 ≤ L) (hT : 0 < S.totalFisher) (a b : Fin 2) :
    (∫ z : Fin k × ZMod L, S.estimator z a * S.tangent z b ∂Measure.count) = if a=b then 1 else 0 := by
  have hp (z : Fin k × ZMod L) : S.probability z * S.outcomeScore z b = S.tangent z b := by
    rw [S.weighted_score, S.tangent_eq]
  have he (z : Fin k × ZMod L) : S.estimator z a * S.tangent z b =
      (S.probability z * S.outcomeScore z a * S.outcomeScore z b) / (2*S.value) := by
    rw [← hp]
    unfold estimator
    ring
  simp_rw [he]
  rw [integral_div]
  change fisherEntry Measure.count S.probability S.outcomeScore a b / (2*S.value) = _
  rw [S.fisher_entry hL]
  split_ifs <;> simp [S.diagonal_ne_zero hT]

theorem estimator_covariance (S : Scheme n k) (hL : 3 ≤ L) (hT : 0 < S.totalFisher) (a b : Fin 2) :
    (∫ z : Fin k × ZMod L, S.probability z * S.estimator z a * S.estimator z b ∂Measure.count) =
      if a=b then (2*S.value)⁻¹ else 0 := by
  exact isotropic_score_covariance Measure.count S.probability S.outcomeScore (2*S.value)
    (S.diagonal_ne_zero hT) (S.fisher_entry hL) a b

theorem momentUnbiased (S : Scheme n k) (hL : 3 ≤ L) (hT : 0 < S.totalFisher) :
    MomentUnbiased (Measure.count : Measure (Fin k × ZMod L)) S.probability S.tangent S.estimator := by
  exact ⟨fun _ => finite_integrable _, fun _ => finite_integrable _, fun _ _ => finite_integrable _,
    S.estimator_mean hL, S.estimator_cross hL hT⟩

theorem estimator_risk (S : Scheme n k) (hL : 3 ≤ L) (hT : 0 < S.totalFisher) (N : ℕ) :
    risk (Measure.count : Measure (Fin k × ZMod L)) N S.probability S.estimator = 4*N / S.totalFisher := by
  have hu := S.momentUnbiased hL hT
  have hsec (a : Fin 2) :
      (∫ z : Fin k × ZMod L, S.probability z * (S.estimator z a)^2 ∂Measure.count) =
        (2*S.value)⁻¹ := by
    simpa only [pow_two, ← mul_assoc, ite_true] using S.estimator_covariance hL hT a a
  unfold risk FiniteCopy.POVM.statisticalCovTrace
  simp_rw [hu.mean_zero, sub_zero, mul_add]
  rw [integral_add (hu.second_integrable 0) (hu.second_integrable 1), hsec, hsec]
  unfold totalFisher
  ring

theorem risk_attainable (S : Scheme n k) (hd : n+1 ≤ L) (hL : 3 ≤ L)
    (hT : 0 < S.totalFisher) (N : ℕ) :
    4*N / S.totalFisher ∈ attainableRisks N (spinReference n)
      (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a)) := by
  refine ⟨Fin k × ZMod L, inferInstance, Measure.count, S.densityPOVM hd, S.estimator, ?_, ?_⟩
  · exact S.momentUnbiased hL hT
  · exact (S.estimator_risk hL hT N).symm

def ensembleWeight (S : Scheme n k) (z : Fin k × ZMod L) : ℝ := S.q z.1 / L
def ensembleState (S : Scheme n k) (z : Fin k × ZMod L) : Fin (n+1) → ℂ :=
  phaseVector (S.amplitude z.1) z.2

theorem ensembleWeight_nonneg (S : Scheme n k) (z : Fin k × ZMod L) : 0 ≤ S.ensembleWeight z :=
  div_nonneg (S.q_nonneg _) (Nat.cast_nonneg _)

theorem ensembleWeight_sum (S : Scheme n k) : (∑ z : Fin k × ZMod L, S.ensembleWeight z) = 1 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [Fintype.sum_prod_type, ensembleWeight, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  simp only [mul_div_cancel₀ _ hL]
  convert S.q_sum using 1

theorem ensembleState_mass (S : Scheme n k) (z : Fin k × ZMod L) :
    vectorMass (S.ensembleState z) = 1 := by
  rw [ensembleState, phaseVector_mass, S.amplitude_mass]

theorem outcomeEffect_rankOne (S : Scheme n k) (z : Fin k × ZMod L) :
    S.outcomeEffect z = (((n : ℝ)+1) * S.ensembleWeight z) • rankOne (S.ensembleState z) := by
  rw [outcomeEffect, seedPhaseEffect_eq, smul_smul]
  congr 1
  dsimp [ensembleWeight, ensembleState]
  ring

theorem ensemble_complete (S : Scheme n k) (hd : n+1 ≤ L) :
    (∑ z : Fin k × ZMod L, S.ensembleWeight z • rankOne (S.ensembleState z)) = spinReference n := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have he (z : Fin k × ZMod L) : S.ensembleWeight z • rankOne (S.ensembleState z) =
      ((n : ℝ)+1)⁻¹ • S.outcomeEffect z := by
    rw [S.outcomeEffect_rankOne, smul_smul]
    congr 1
    field_simp
  simp_rw [he]
  rw [← Finset.smul_sum, S.outcomeEffect_complete hd]
  rfl

theorem ensemble_quadratic_average (S : Scheme n k) (hd : n+1 ≤ L)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (∑ z : Fin k × ZMod L, S.ensembleWeight z * (quadratic A (S.ensembleState z)).re) =
      (Matrix.trace A).re / ((n : ℝ)+1) := by
  have h := congrArg (fun B => born A B) (S.ensemble_complete hd)
  simp only [born, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
    Matrix.mul_smul, Matrix.trace_smul, RCLike.real_smul_eq_coe_mul, Complex.mul_re,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, trace_mul_rankOne] at h
  rw [h]
  simp only [spinReference, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    RCLike.real_smul_eq_coe_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    RCLike.ofReal_eq_complex_ofReal, zero_mul, sub_zero]
  ring

theorem ensemble_gamma_second (S : Scheme n k) :
    (∑ z : Fin k × ZMod L, S.ensembleWeight z * S.gamma z.1 ^ 2) = S.value := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [Fintype.sum_prod_type, ensembleWeight, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, value]
  apply Finset.sum_congr rfl
  intro a ha
  field_simp

theorem ensemble_variance_point (S : Scheme n k) (z : Fin k × ZMod L) :
    pureVariance (spinX (spinCoefficient n)) (S.ensembleState z) +
      pureVariance (spinY (spinCoefficient n)) (S.ensembleState z) =
    (quadratic (spinX (spinCoefficient n) * spinX (spinCoefficient n)) (S.ensembleState z)).re +
      (quadratic (spinY (spinCoefficient n) * spinY (spinCoefficient n)) (S.ensembleState z)).re -
      S.gamma z.1 ^ 2 := by
  simp only [pureVariance, normalizedMoment, S.ensembleState_mass, div_one]
  simp only [ensembleState, spinX_phase_quadratic, spinY_phase_quadratic, gamma]
  have h := PhaseMoments.cx_sq_add_cy_sq z.2
  have hw := congrArg (fun t : ℝ => seedMoment (spinCoefficient n) (S.amplitude z.1)^2 * t) h
  nlinarith [hw]

theorem ensemble_variance (S : Scheme n k) (hd : n+1 ≤ L) :
    (∑ z : Fin k × ZMod L, S.ensembleWeight z *
      (pureVariance (spinX (spinCoefficient n)) (S.ensembleState z) +
        pureVariance (spinY (spinCoefficient n)) (S.ensembleState z))) =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - S.value := by
  simp_rw [S.ensemble_variance_point, mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    S.ensemble_quadratic_average hd, S.ensemble_quadratic_average hd, S.ensemble_gamma_second,
    ← add_div, spin_trace_value]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem ensemble_variance_trace_identity (S : Scheme n k) (hd : n+1 ≤ L) :
    S.totalFisher = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * (∑ z : Fin k × ZMod L, S.ensembleWeight z *
        (pureVariance (spinX (spinCoefficient n)) (S.ensembleState z) +
          pureVariance (spinY (spinCoefficient n)) (S.ensembleState z))) := by
  rw [S.ensemble_variance hd]
  unfold totalFisher
  ring

end Scheme
end FiniteCopy.SeedPOVM

