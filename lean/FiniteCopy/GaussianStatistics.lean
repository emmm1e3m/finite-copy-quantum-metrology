import FiniteCopy.FisherPositive
import FiniteCopy.Construction
import FiniteCopy.Schur

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

-- 012 的实际高斯效果与017的矩阵统计接口逐项相同。
lemma gaussian_effect_eq (n : ℕ) (eps t : ℝ) (k : ZMod L) :
    spinEffect n eps t k = seedPhaseEffect (spinColumn n eps t) k := rfl

def gaussianFisher (n : ℕ) (eps : ℝ) : ℝ :=
  integratedSpinFisher volume (spinCoefficient n) (spinColumn n eps)

lemma gaussianFisher_nonneg (n : ℕ) (eps : ℝ) : 0 ≤ gaussianFisher n eps := by
  exact integral_nonneg fun t => seedFisher_nonneg _ _

lemma gaussianFisher_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Integrable fun t => seedFisher (spinCoefficient n) (spinColumn n eps t) := by
  exact integrable_seedFisher _ (fun r => (spinCoefficient_pos r).le) _
    (spinColumn_pos n heps) (spinColumn_continuous n eps) (spinColumn_integrable_sq n heps)

theorem gaussianFisher_pos (hn : 0 < n) {eps : ℝ} (heps : 0 < eps) :
    0 < gaussianFisher n eps := by
  exact integrated_spinFisher_pos hn _ (spinColumn_pos n heps)
    (spinColumn_continuous n eps) (spinColumn_integrable_sq n heps)

theorem gaussian_born_probability (n : ℕ) (eps t : ℝ) (k : ZMod L) :
    born (spinReference n) (spinEffect n eps t k) =
      seedMass (spinColumn n eps t) / ((L : ℝ) * (n+1)) := by
  exact spin_born_reference _ k

theorem gaussian_probability_pos (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (t : ℝ) (k : ZMod L) : 0 < born (spinReference n) (spinEffect n eps t k) := by
  rw [gaussian_born_probability]
  exact div_pos (seedMass_pos _ (spinColumn_pos n heps t))
    (mul_pos (Nat.cast_pos.mpr (NeZero.pos L)) (by positivity))


lemma gaussian_mass_integral (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    (∫ t, seedMass (spinColumn n eps t)) = (n+1 : ℝ) := by
  unfold seedMass
  rw [integral_finsetSum _ (fun i _ => spinColumn_integrable_sq n heps i)]
  simp [spinColumn_normalized n heps]

theorem gaussian_probability_normalized (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    (∫ t, ∑ k : ZMod L, born (spinReference n) (spinEffect n eps t k)) = 1 := by
  simp_rw [gaussian_born_probability]
  have he (t : ℝ) :
      (∑ _k : ZMod L, seedMass (spinColumn n eps t) / ((L : ℝ) * (n+1))) =
      seedMass (spinColumn n eps t) / (n+1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    field_simp
  simp_rw [he]
  rw [integral_div, gaussian_mass_integral n heps]
  exact div_self (by positivity)

-- 此处 Fisher 直接用 Born 概率和实际矩阵切向的比值定义。
theorem gaussian_actual_fisher (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (a b : Bool) :
    (∫ t, ∑ k : ZMod L, born (spinReference n) (spinEffect n eps t k) *
      (born (spinTangent (spinCoefficient n) a) (spinEffect n eps t k) /
        born (spinReference n) (spinEffect n eps t k)) *
      (born (spinTangent (spinCoefficient n) b) (spinEffect n eps t k) /
        born (spinReference n) (spinEffect n eps t k))) =
      if a = b then gaussianFisher n eps else 0 := by
  simp_rw [gaussian_effect_eq, spin_born_score _ _
    (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps _))), spin_born_reference,
    phaseScore_second hL _ _ (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps _)))]
  by_cases hab : a = b
  · simp only [hab, ite_true, gaussianFisher, integratedSpinFisher]
  · simp [hab]

lemma gaussian_statistics_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (k : ZMod L) (a b : Bool) :
    Integrable (fun t => phaseProbability (L := L) (spinColumn n eps t)) ∧
    Integrable (fun t => phaseProbability (L := L) (spinColumn n eps t) *
      phaseScore (spinCoefficient n) (spinColumn n eps t) k a) ∧
    Integrable (fun t => phaseProbability (L := L) (spinColumn n eps t) *
      phaseScore (spinCoefficient n) (spinColumn n eps t) k a *
      phaseScore (spinCoefficient n) (spinColumn n eps t) k b) := by
  exact phase_statistics_integrable _ (fun r => (spinCoefficient_pos r).le) _
    (spinColumn_pos n heps) (spinColumn_continuous n eps) (spinColumn_integrable_sq n heps) k a b

-- n≥1 时局部无偏性不再携带待证的 Fisher 正性、均值或二阶矩前提。
theorem gaussian_locally_unbiased (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (a b : Bool) :
    spinEstimatorExpectation (L := L) volume (spinCoefficient n) (spinColumn n eps) a b 0 = 0 ∧
    HasDerivAt (spinEstimatorExpectation (L := L) volume (spinCoefficient n) (spinColumn n eps) a b)
      (if a = b then 1 else 0) 0 := by
  exact integrated_spin_local_unbiased volume hL _ _
    (fun t => ne_of_gt (seedMass_pos _ (spinColumn_pos n heps t)))
    (ne_of_gt (gaussianFisher_pos hn heps)) a b

theorem gaussian_covariance (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (a b : Bool) :
    (∫ t, ∑ k : ZMod L, born (spinReference n) (spinEffect n eps t k) *
      (phaseScore (spinCoefficient n) (spinColumn n eps t) k a / gaussianFisher n eps) *
      (phaseScore (spinCoefficient n) (spinColumn n eps t) k b / gaussianFisher n eps)) =
      if a = b then (gaussianFisher n eps)⁻¹ else 0 := by
  exact integrated_spin_covariance volume hL _ _
    (fun t => ne_of_gt (seedMass_pos _ (spinColumn_pos n heps t)))
    (ne_of_gt (gaussianFisher_pos hn heps)) a b

-- 显式对数宽度和实际二项式 Schur 权重。
def logarithmicFisher (n : ℕ) : ℝ := gaussianFisher n (epsilon (spinJ n))

def globalGaussianFisher (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N/2+1), FiniteCopy.Schur.weight N k * logarithmicFisher (N-2*k)

lemma logarithmicFisher_nonneg (n : ℕ) : 0 ≤ logarithmicFisher n := gaussianFisher_nonneg _ _

lemma logarithmicFisher_pos (hn : 0 < n) : 0 < logarithmicFisher n :=
  gaussianFisher_pos hn (epsilon_pos (spinJ_pos n).le)

lemma top_schur_weight_pos (N : ℕ) : 0 < FiniteCopy.Schur.weight N 0 := by
  simp only [FiniteCopy.Schur.weight, FiniteCopy.Schur.binom, Nat.choose_zero_right,
    Nat.cast_one, Nat.cast_zero, mul_zero, sub_zero, ite_true]
  positivity

-- 对每个有限 N≥1 严格正，使用最大自旋块而非渐近 eventually。
theorem globalGaussianFisher_pos (N : ℕ) (hN : 0 < N) : 0 < globalGaussianFisher N := by
  apply Finset.sum_pos'
  · intro k hk
    have hk' : k ≤ N/2 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    exact mul_nonneg (FiniteCopy.Schur.weight_nonneg hk') (logarithmicFisher_nonneg _)
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [mul_zero, Nat.sub_zero]
    exact mul_pos (top_schur_weight_pos N) (logarithmicFisher_pos hN)


def globalGaussianExpectation (N : ℕ) (a b : Bool) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N/2+1), FiniteCopy.Schur.weight N k *
    ∫ t, ∑ q : ZMod L,
      (phaseScore (spinCoefficient (N-2*k))
        (spinColumn (N-2*k) (epsilon (spinJ (N-2*k))) t) q a / globalGaussianFisher N) *
      born (spinAffine (spinCoefficient (N-2*k)) b θ)
        (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q)

lemma gaussian_scaled_expectation (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (f θ : ℝ) (a b : Bool) :
    (∫ t, ∑ q : ZMod L,
      (phaseScore (spinCoefficient n) (spinColumn n eps t) q a / f) *
      born (spinAffine (spinCoefficient n) b θ) (spinEffect n eps t q)) =
      if a = b then (θ / f) * gaussianFisher n eps else 0 := by
  simp_rw [gaussian_effect_eq, phase_estimator_expectation hL _ _
    (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps _)))]
  by_cases hab : a = b
  · simp only [hab, ite_true, integral_const_mul, gaussianFisher, integratedSpinFisher]
  · simp [hab]

theorem globalGaussianExpectation_formula (N : ℕ) (hN : 0 < N)
    (hL : 3 ≤ L) (a b : Bool) (θ : ℝ) :
    globalGaussianExpectation (L := L) N a b θ = θ * (if a = b then 1 else 0) := by
  unfold globalGaussianExpectation
  simp_rw [gaussian_scaled_expectation _ (epsilon_pos (spinJ_pos _).le) hL]
  by_cases hab : a = b
  · simp only [hab, ite_true]
    have he (k : ℕ) :
        FiniteCopy.Schur.weight N k *
          (θ / globalGaussianFisher N * gaussianFisher (N-2*k) (epsilon (spinJ (N-2*k)))) =
        (θ / globalGaussianFisher N) *
          (FiniteCopy.Schur.weight N k * logarithmicFisher (N-2*k)) := by
      unfold logarithmicFisher
      ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    change (θ / globalGaussianFisher N) * globalGaussianFisher N = θ * 1
    field_simp [ne_of_gt (globalGaussianFisher_pos N hN)]
  · simp [hab]

-- 这是实际有限权重块实验的全部有限 N 的显式 score 估计器。
theorem globalGaussian_locally_unbiased (N : ℕ) (hN : 0 < N)
    (hL : 3 ≤ L) (a b : Bool) :
    globalGaussianExpectation (L := L) N a b 0 = 0 ∧
    HasDerivAt (globalGaussianExpectation (L := L) N a b) (if a = b then 1 else 0) 0 := by
  constructor
  · rw [globalGaussianExpectation_formula N hN hL]; simp
  · have he : globalGaussianExpectation (L := L) N a b =
        fun θ => θ * (if a = b then 1 else 0) :=
      funext (globalGaussianExpectation_formula N hN hL a b)
    rw [he]
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (if a = b then (1 : ℝ) else 0)

def globalGaussianCovariance (N : ℕ) (a b : Bool) : ℝ :=
  ∑ k ∈ Finset.range (N/2+1), FiniteCopy.Schur.weight N k *
    ∫ t, ∑ q : ZMod L,
      born (spinReference (N-2*k)) (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q) *
      (phaseScore (spinCoefficient (N-2*k))
        (spinColumn (N-2*k) (epsilon (spinJ (N-2*k))) t) q a / globalGaussianFisher N) *
      (phaseScore (spinCoefficient (N-2*k))
        (spinColumn (N-2*k) (epsilon (spinJ (N-2*k))) t) q b / globalGaussianFisher N)

lemma gaussian_scaled_second (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (f : ℝ) (a b : Bool) :
    (∫ t, ∑ q : ZMod L, born (spinReference n) (spinEffect n eps t q) *
      (phaseScore (spinCoefficient n) (spinColumn n eps t) q a / f) *
      (phaseScore (spinCoefficient n) (spinColumn n eps t) q b / f)) =
      if a = b then gaussianFisher n eps / (f*f) else 0 := by
  simp_rw [gaussian_effect_eq, phase_estimator_second hL _ _
    (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps _)))]
  by_cases hab : a = b
  · simp only [hab, ite_true, integral_div, gaussianFisher, integratedSpinFisher]
  · simp [hab]

theorem globalGaussianCovariance_formula (N : ℕ) (hN : 0 < N)
    (hL : 3 ≤ L) (a b : Bool) :
    globalGaussianCovariance (L := L) N a b = if a = b then (globalGaussianFisher N)⁻¹ else 0 := by
  unfold globalGaussianCovariance
  simp_rw [gaussian_scaled_second _ (epsilon_pos (spinJ_pos _).le) hL]
  by_cases hab : a = b
  · simp only [hab, ite_true]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    change globalGaussianFisher N / (globalGaussianFisher N * globalGaussianFisher N) = _
    field_simp [ne_of_gt (globalGaussianFisher_pos N hN)]
  · simp [hab]

theorem globalGaussian_risk (N : ℕ) (hN : 0 < N) (hL : 3 ≤ L) :
    (N : ℝ) * (globalGaussianCovariance (L := L) N false false +
      globalGaussianCovariance (L := L) N true true) = 2 * N / globalGaussianFisher N := by
  rw [globalGaussianCovariance_formula N hN hL, globalGaussianCovariance_formula N hN hL]
  simp only [ite_true]
  ring


-- 全局 Fisher 的定义仍是带块标签的实际 Born score 二阶矩。
theorem globalGaussian_actual_fisher (N : ℕ) (hL : 3 ≤ L) (a b : Bool) :
    (∑ k ∈ Finset.range (N/2+1), FiniteCopy.Schur.weight N k *
      ∫ t, ∑ q : ZMod L,
        born (spinReference (N-2*k)) (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q) *
        (born (spinTangent (spinCoefficient (N-2*k)) a)
          (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q) /
          born (spinReference (N-2*k)) (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q)) *
        (born (spinTangent (spinCoefficient (N-2*k)) b)
          (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q) /
          born (spinReference (N-2*k)) (spinEffect (N-2*k) (epsilon (spinJ (N-2*k))) t q))) =
      if a = b then globalGaussianFisher N else 0 := by
  simp_rw [gaussian_actual_fisher _ (epsilon_pos (spinJ_pos _).le) hL]
  by_cases hab : a = b
  · simp only [hab, ite_true, globalGaussianFisher, logarithmicFisher]
  · simp [hab]


end CopyQuantumMetrology


