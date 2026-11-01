import FiniteCopy.GaussianVariance
import FiniteCopy.ContinuousEnergy
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

lemma continuousEnergy_mass_eq (n : ℕ) (eps t : ℝ) :
    FiniteCopy.Algebra.mass n (ContinuousEnergy.spinV n eps t) = seedMass (spinColumn n eps t) := by
  unfold FiniteCopy.Algebra.mass seedMass
  rw [← Fin.sum_univ_eq_sum_range (fun i => ContinuousEnergy.spinV n eps t i ^ 2)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ContinuousEnergy.spinV, i.isLt]

lemma continuousEnergy_moment_eq (n : ℕ) (eps t : ℝ) :
    FiniteCopy.Algebra.moment n (FiniteCopy.Algebra.spinEdge n) (ContinuousEnergy.spinV n eps t) =
      seedMoment (spinCoefficient n) (spinColumn n eps t) := by
  unfold FiniteCopy.Algebra.moment seedMoment
  rw [← Fin.sum_univ_eq_sum_range (fun i => FiniteCopy.Algebra.spinEdge n i *
    ContinuousEnergy.spinV n eps t i * ContinuousEnergy.spinV n eps t (i+1))]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i.val < n+1 := by omega
  have hi1 : i.val+1 < n+1 := by omega
  simp only [ContinuousEnergy.spinV, hi0, hi1, dif_pos, spinCoefficient_eq_spinEdge]
  rfl

lemma continuousEnergy_quotient_eq (n : ℕ) (eps t : ℝ) :
    ContinuousEnergy.quotient n eps t =
      seedMoment (spinCoefficient n) (spinColumn n eps t)^2 / seedMass (spinColumn n eps t) := by
  rw [ContinuousEnergy.quotient, continuousEnergy_mass_eq, continuousEnergy_moment_eq]

lemma gaussianFisher_quotient (n : ℕ) (eps : ℝ) :
    gaussianFisher n eps = (2 / (n+1 : ℝ)) * ∫ t, ContinuousEnergy.quotient n eps t := by
  unfold gaussianFisher integratedSpinFisher
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [continuousEnergy_quotient_eq]
  unfold seedFisher
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

lemma continuousEnergy_fisher_variance (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    2 * gaussianFisher n eps = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * ContinuousEnergy.W n eps := by
  rw [gaussianFisher_quotient]
  unfold ContinuousEnergy.W ContinuousEnergy.varianceDensity
  rw [integral_sub (ContinuousEnergy.diagonal_integrable n heps)
    (ContinuousEnergy.quotient_integrable n heps), ContinuousEnergy.integral_diagonal n heps,
    FiniteCopy.Algebra.spinA_sum]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

-- 两个分别由真实矩阵和031能量定义给出的量严格相同。
theorem gaussianVariance_eq_W (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (hd : n+1 ≤ L) : gaussianVariance n eps L = ContinuousEnergy.W n eps := by
  have hq := gaussian_fisher_variance n heps hL hd
  have he := continuousEnergy_fisher_variance n heps
  linarith

theorem actualGaussianVariance_eq_W (n : ℕ) :
    actualGaussianVariance n = ContinuousEnergy.W n (epsilon (spinJ n)) := by
  exact gaussianVariance_eq_W n (epsilon_pos (spinJ_pos n).le) (by omega) (by omega)

end CopyQuantumMetrology

