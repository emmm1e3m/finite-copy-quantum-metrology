import FiniteCopy.GaussianStatistics
import FiniteCopy.SpinTrace
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix Complex
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

lemma born_seedPhaseEffect (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (v : Fin (n+1) → ℝ) (k : ZMod L) :
    born A (seedPhaseEffect v k) = (quadratic A (phaseVector v k)).re / L := by
  rw [seedPhaseEffect_eq, born_smul_right]
  simp only [born, trace_mul_rankOne]
  ring

lemma gaussian_quadratic_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Integrable (fun t => ∑ k : ZMod L,
      (quadratic A (phaseVector (spinColumn n eps t) k)).re / L) := by
  simp_rw [← born_seedPhaseEffect, ← gaussian_effect_eq]
  apply integrable_finsetSum
  intro k hk
  exact (trace_mul_integrable volume (fun t => spinEffect n eps t k) A
    (spinEffect_integrable n heps k)).re

-- 完整高斯效果固定每一个实际矩阵二次型的积分。
theorem gaussian_quadratic_average (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : n+1 ≤ L) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (∫ t, ∑ k : ZMod L, (quadratic A (phaseVector (spinColumn n eps t) k)).re / L) =
      (Matrix.trace A).re := by
  let M : ℝ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    fun t => ∑ k : ZMod L, spinEffect n eps t k
  have hi (i j : Fin (n+1)) : Integrable (fun t => M t i j) := by
    simp only [M, Matrix.sum_apply]
    exact integrable_finsetSum _ (fun k _ => spinEffect_integrable n heps k i j)
  have hc (i j : Fin (n+1)) : (∫ t, M t i j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j := by
    have hh := congrFun (congrFun (spinEffect_complete n heps hL) i) j
    simpa only [M, Matrix.sum_apply] using hh
  have he (t : ℝ) :
      (∑ k : ZMod L, (quadratic A (phaseVector (spinColumn n eps t) k)).re / L) =
      (Matrix.trace (A * M t)).re := by
    simp_rw [← born_seedPhaseEffect, ← gaussian_effect_eq]
    simp [M, born, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  simp_rw [he]
  have hr := integral_re (trace_mul_integrable volume M A hi)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, integral_trace_mul volume M A hi hc]

lemma phase_fisher_density (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (k : ZMod L) :
    fisherTraceDensity (n+1) (spinX c) (spinY c) (phaseVector v k) / L =
      phaseProbability (L := L) v * phaseScore c v k false * phaseScore c v k false +
      phaseProbability (L := L) v * phaseScore c v k true * phaseScore c v k true := by
  simp only [fisherTraceDensity, normalizedMoment, phaseVector_mass,
    spinX_phase_quadratic, spinY_phase_quadratic, phaseScore, phaseProbability, phaseDirection,
    Bool.false_eq_true, ite_false, ite_true]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

lemma phase_variance_identity (hL : 3 ≤ L) (c : Fin n → ℝ)
    (v : Fin (n+1) → ℝ) (hv : seedMass v ≠ 0) :
    2 * seedFisher c v + 4 *
      (∑ k : ZMod L, varianceDensity (n+1) (spinX c) (spinY c) (phaseVector v k) / L) =
      (4 / (n+1 : ℝ)) *
      ((∑ k : ZMod L, (quadratic (spinX c * spinX c) (phaseVector v k)).re / L) +
       (∑ k : ZMod L, (quadratic (spinY c * spinY c) (phaseVector v k)).re / L)) := by
  have hp (k : ZMod L) := fisher_variance_pointwise (n+1) (spinX c) (spinY c)
    (phaseVector v k) (by simpa only [phaseVector_mass] using hv)
  have hh := congrArg (fun f : ZMod L → ℝ => ∑ k, f k / L) (funext hp)
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hf : (∑ k : ZMod L, fisherTraceDensity (n+1) (spinX c) (spinY c)
      (phaseVector v k) / L) = 2 * seedFisher c v := by
    simp_rw [phase_fisher_density]
    rw [Finset.sum_add_distrib, phaseScore_second hL c v hv, phaseScore_second hL c v hv]
    simp only [ite_true]
    ring
  rw [hf] at hh
  convert hh using 1 <;> ring

-- 使用同一纯态分解的两项量子方差。
def gaussianVariance (n : ℕ) (eps : ℝ) (L : ℕ) [NeZero L] : ℝ :=
  ∫ t, ∑ k : ZMod L,
    varianceDensity (n+1) (spinX (spinCoefficient n)) (spinY (spinCoefficient n))
      (phaseVector (spinColumn n eps t) k) / L

theorem gaussian_fisher_variance (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (hd : n+1 ≤ L) :
    2 * gaussianFisher n eps = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * gaussianVariance n eps L := by
  let c := spinCoefficient n
  let v := spinColumn n eps
  let qx := fun t => ∑ k : ZMod L, (quadratic (spinX c * spinX c) (phaseVector (v t) k)).re / L
  let qy := fun t => ∑ k : ZMod L, (quadratic (spinY c * spinY c) (phaseVector (v t) k)).re / L
  let w := fun t => ∑ k : ZMod L, varianceDensity (n+1) (spinX c) (spinY c) (phaseVector (v t) k) / L
  have hx : Integrable qx := gaussian_quadratic_integrable n heps _
  have hy : Integrable qy := gaussian_quadratic_integrable n heps _
  have hf := gaussianFisher_integrable n heps
  have he (t : ℝ) : w t = (1 / (n+1 : ℝ)) * (qx t + qy t) -
      (1/2 : ℝ) * seedFisher c (v t) := by
    have hp := phase_variance_identity hL c (v t)
      (ne_of_gt (seedMass_pos _ (spinColumn_pos n heps t)))
    change 2 * seedFisher c (v t) + 4 * w t = (4 / (n+1 : ℝ)) * (qx t + qy t) at hp
    ring_nf at hp ⊢
    linarith
  change Integrable (fun t => seedFisher c (v t)) at hf
  have hleft : Integrable (fun t => (1 / (n+1 : ℝ)) * (qx t + qy t)) := (hx.add hy).const_mul _
  have hright : Integrable (fun t => (1/2 : ℝ) * seedFisher c (v t)) := hf.const_mul _
  have hid := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall he)
  rw [integral_sub hleft hright, integral_const_mul,
    integral_add hx hy, integral_const_mul] at hid
  have hxv : (∫ t, qx t) = (Matrix.trace (spinX c * spinX c)).re := gaussian_quadratic_average n heps hd _
  have hyv : (∫ t, qy t) = (Matrix.trace (spinY c * spinY c)).re := gaussian_quadratic_average n heps hd _
  rw [hxv, hyv, spin_trace_value n] at hid
  change gaussianVariance n eps L = _ at hid
  change 2 * (∫ t, seedFisher c (v t)) = _
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hcancel : (1 / (n+1 : ℝ)) *
      ((2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) * (n+1)) =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) := by field_simp
  rw [hcancel] at hid
  linarith


-- 每个 n 固定一个合法有限相位数；方差由真实矩阵而非独立标量指定。
def actualGaussianVariance (n : ℕ) : ℝ :=
  gaussianVariance n (epsilon (spinJ n)) (n+3)

theorem logarithmic_fisher_variance (n : ℕ) :
    2 * logarithmicFisher n = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * actualGaussianVariance n :=
  gaussian_fisher_variance n (epsilon_pos (spinJ_pos n).le) (by omega) (by omega)

-- 真实二项式权重的精确二阶矩给出有限 N 恒等式。
theorem globalGaussian_fisher_variance (N : ℕ) :
    2 * globalGaussianFisher N =
      2 * N - 4 * FiniteCopy.Schur.schurAverage actualGaussianVariance N := by
  rw [← FiniteCopy.Schur.schurAverage_fisher actualGaussianVariance N]
  unfold globalGaussianFisher FiniteCopy.Schur.schurAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show 2 * (FiniteCopy.Schur.weight N k * logarithmicFisher (N-2*k)) =
    FiniteCopy.Schur.weight N k * (2 * logarithmicFisher (N-2*k)) by ring]
  rw [logarithmic_fisher_variance]

theorem globalGaussian_risk_variance (N : ℕ) (hN : 0 < N) (hL : 3 ≤ L) :
    (N : ℝ) * (globalGaussianCovariance (L := L) N false false +
      globalGaussianCovariance (L := L) N true true) =
      4 * N / (2 * N - 4 * FiniteCopy.Schur.schurAverage actualGaussianVariance N) := by
  rw [globalGaussian_risk N hN hL, ← globalGaussian_fisher_variance N]
  ring

end CopyQuantumMetrology

