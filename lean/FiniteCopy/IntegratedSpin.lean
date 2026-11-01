import FiniteCopy.SpinStatistics

open scoped BigOperators ComplexOrder
open MeasureTheory Matrix Complex
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

lemma born_add_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ E : Matrix ι ι ℂ) : born (ρ + σ) E = born ρ E + born σ E := by
  simp [born, Matrix.add_mul, Matrix.trace_add]

lemma born_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ E : Matrix ι ι ℂ) (a : ℝ) : born (a • ρ) E = a * born ρ E := by
  simp only [born, Matrix.smul_mul, Matrix.trace_smul]
  change RCLike.re (a • Matrix.trace (ρ * E)) = _
  rw [RCLike.smul_re]
  rfl

-- 以真实矩阵参考态与切向构成的局部曲线。
def spinAffine (c : Fin n → ℝ) (b : Bool) (θ : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  spinReference n + θ • spinTangent c b

lemma spin_born_affine (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (hv : seedMass v ≠ 0) (k : ZMod L) (b : Bool) (θ : ℝ) :
    born (spinAffine c b θ) (seedPhaseEffect v k) =
      phaseProbability (L := L) v * (1 + θ * phaseScore c v k b) := by
  rw [spinAffine, born_add_left, born_smul_left, spin_born_reference, spin_born_tangent]
  dsimp [phaseProbability, phaseScore]
  field_simp
  <;> ring

lemma phase_estimator_expectation (hL : 3 ≤ L) (c : Fin n → ℝ)
    (v : Fin (n+1) → ℝ) (hv : seedMass v ≠ 0) (f θ : ℝ) (a b : Bool) :
    (∑ k : ZMod L, (phaseScore c v k a / f) * born (spinAffine c b θ) (seedPhaseEffect v k)) =
      if a = b then (θ / f) * seedFisher c v else 0 := by
  simp_rw [spin_born_affine c v hv]
  have he (k : ZMod L) :
      phaseScore c v k a / f * (phaseProbability (L := L) v * (1 + θ * phaseScore c v k b)) =
      (phaseProbability (L := L) v * phaseScore c v k a) / f +
      (θ / f) * (phaseProbability (L := L) v * phaseScore c v k a * phaseScore c v k b) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, phaseScore_mean hL,
    ← Finset.mul_sum, phaseScore_second hL c v hv]
  split_ifs <;> simp

lemma phase_estimator_second (hL : 3 ≤ L) (c : Fin n → ℝ)
    (v : Fin (n+1) → ℝ) (hv : seedMass v ≠ 0) (f : ℝ) (a b : Bool) :
    (∑ k : ZMod L, born (spinReference n) (seedPhaseEffect v k) *
      (phaseScore c v k a / f) * (phaseScore c v k b / f)) =
      if a = b then seedFisher c v / (f*f) else 0 := by
  simp_rw [spin_born_reference]
  have he (k : ZMod L) :
      phaseProbability (L := L) v * (phaseScore c v k a / f) * (phaseScore c v k b / f) =
      (phaseProbability (L := L) v * phaseScore c v k a * phaseScore c v k b) / (f*f) := by ring
  simp_rw [he]
  rw [← Finset.sum_div, phaseScore_second hL c v hv]
  split_ifs <;> simp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def integratedSpinFisher (c : Fin n → ℝ) (v : X → Fin (n+1) → ℝ) : ℝ :=
  ∫ t, seedFisher c (v t) ∂μ

def spinEstimatorExpectation (c : Fin n → ℝ) (v : X → Fin (n+1) → ℝ)
    (a b : Bool) (θ : ℝ) : ℝ :=
  ∫ t, ∑ k : ZMod L,
    (phaseScore c (v t) k a / integratedSpinFisher μ c v) *
      born (spinAffine c b θ) (seedPhaseEffect (v t) k) ∂μ

-- 零均值、实际 Fisher 与局部导数均由相位恒等式推出。
theorem integrated_spin_local_unbiased (hL : 3 ≤ L) (c : Fin n → ℝ)
    (v : X → Fin (n+1) → ℝ) (hv : ∀ t, seedMass (v t) ≠ 0)
    (hf : integratedSpinFisher μ c v ≠ 0) (a b : Bool) :
    spinEstimatorExpectation (L := L) μ c v a b 0 = 0 ∧
    HasDerivAt (spinEstimatorExpectation (L := L) μ c v a b)
      (if a = b then 1 else 0) 0 := by
  have he (θ : ℝ) : spinEstimatorExpectation (L := L) μ c v a b θ =
      θ * (if a = b then 1 else 0) := by
    simp only [spinEstimatorExpectation]
    simp_rw [phase_estimator_expectation hL c _ (hv _)]
    by_cases hab : a = b
    · simp only [hab, ite_true, integral_const_mul, integratedSpinFisher]
      unfold integratedSpinFisher at hf
      field_simp [hf]
    · simp [hab]
  constructor
  · rw [he]; simp
  · have heq : spinEstimatorExpectation (L := L) μ c v a b =
        fun θ => θ * (if a = b then 1 else 0) := funext he
    rw [heq]
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (if a = b then (1 : ℝ) else 0)

theorem integrated_spin_covariance (hL : 3 ≤ L) (c : Fin n → ℝ)
    (v : X → Fin (n+1) → ℝ) (hv : ∀ t, seedMass (v t) ≠ 0)
    (hf : integratedSpinFisher μ c v ≠ 0) (a b : Bool) :
    (∫ t, ∑ k : ZMod L, born (spinReference n) (seedPhaseEffect (v t) k) *
      (phaseScore c (v t) k a / integratedSpinFisher μ c v) *
      (phaseScore c (v t) k b / integratedSpinFisher μ c v) ∂μ) =
      if a = b then (integratedSpinFisher μ c v)⁻¹ else 0 := by
  simp_rw [phase_estimator_second hL c _ (hv _)]
  by_cases hab : a = b
  · simp only [hab, ite_true, integral_div, integratedSpinFisher]
    unfold integratedSpinFisher at hf
    field_simp [hf]
  · simp [hab]

end CopyQuantumMetrology

