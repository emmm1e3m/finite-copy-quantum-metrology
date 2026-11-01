import FiniteCopy.RiskTerminal
import FiniteCopy.ProductEstimator
open scoped BigOperators Topology
open MeasureTheory
noncomputable section
namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM
variable {L : ℕ} [NeZero L]
local instance : MeasurableSpace (ZMod L) := ⊤
local instance : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

-- 实际产品结果空间上的完整高斯测量，全部密度条件已由构造证明。
def gaussianDensityPOVM (n : ℕ) (eps : ℝ) (heps : 0 < eps) (hd : n+1 ≤ L) :
    DensityPOVM (Fin (n+1)) (ℝ × ZMod L) (gaussianOutcomeMeasure L) where
  effect := gaussianOutcomeEffect n eps
  positive := gaussianProduct_positive n eps
  integrable := gaussianProduct_integrable n heps
  complete := gaussianProduct_complete n heps hd

theorem gaussianMomentUnbiased {n : ℕ} (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) :
    MomentUnbiased (gaussianOutcomeMeasure L) (gaussianOutcomeProbability n eps)
      (gaussianOutcomeTangent n eps) (gaussianOutcomeEstimator n eps (gaussianFisher n eps)) := by
  have h := gaussianProduct_moment_unbiased (L := L) hn heps hL
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem gaussianProduct_risk (N n : ℕ) (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) :
    risk (gaussianOutcomeMeasure L) N (gaussianOutcomeProbability n eps)
      (gaussianOutcomeEstimator n eps (gaussianFisher n eps)) = 2*N / gaussianFisher n eps := by
  have hu := gaussianMomentUnbiased hn heps hL
  have hsec (a : Fin 2) :
      (∫ z, gaussianOutcomeProbability n eps z *
        (gaussianOutcomeEstimator n eps (gaussianFisher n eps) z a)^2
        ∂gaussianOutcomeMeasure L) = (gaussianFisher n eps)⁻¹ := by
    have h := gaussianProduct_estimator_covariance n heps hL (gaussianFisher n eps) a a
    simp only [ite_true] at h
    simp_rw [pow_two, ← mul_assoc]
    rw [h]
    field_simp [ne_of_gt (gaussianFisher_pos hn heps)]
  unfold risk statisticalCovTrace
  simp_rw [hu.mean_zero, sub_zero, mul_add]
  rw [integral_add (hu.second_integrable 0) (hu.second_integrable 1), hsec, hsec]
  ring

-- 该定理给出真实风险集合中的一个元素，直接供 sInf 上界调用。
theorem gaussian_risk_attainable (N n : ℕ) (hn : 0 < n) {eps : ℝ} (heps : 0 < eps)
    (hL : 3 ≤ L) (hd : n+1 ≤ L) :
    2*N / gaussianFisher n eps ∈ attainableRisks N (spinReference n)
      (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a)) := by
  refine ⟨ℝ × ZMod L, inferInstance, gaussianOutcomeMeasure L,
    gaussianDensityPOVM n eps heps hd, gaussianOutcomeEstimator n eps (gaussianFisher n eps), ?_, ?_⟩
  · exact gaussianMomentUnbiased hn heps hL
  · exact (gaussianProduct_risk N n hn heps hL).symm

end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM
open FiniteCopy.Algebra

lemma spinReference_eq_state (n : ℕ) : spinReference n = state n := by
  simp [spinReference, state]

lemma raising_eq_spin (n : ℕ) : raising n (spinEdge n) = raisingMatrix (spinCoefficient n) := by
  unfold raising raisingMatrix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  have h0 : vertex n r.val = r.castSucc := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (Nat.le_of_lt r.isLt)]
  have h1 : vertex n (r.val+1) = r.succ := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (show r.val+1 ≤ n by omega)]
  rw [h0, h1]
  rfl

lemma lowering_eq_spin (n : ℕ) : lowering n (spinEdge n) = loweringMatrix (spinCoefficient n) := by
  unfold lowering loweringMatrix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  have h0 : vertex n r.val = r.castSucc := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (Nat.le_of_lt r.isLt)]
  have h1 : vertex n (r.val+1) = r.succ := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (show r.val+1 ≤ n by omega)]
  rw [h0, h1]
  rfl

lemma spinTangent_eq_canonical (n : ℕ) (a : Fin 2) :
    spinTangent (spinCoefficient n) (phaseCoordinate a) =
      if a = 0 then tangentX n (spinEdge n) else tangentY n (spinEdge n) := by
  fin_cases a
  · simp only [phaseCoordinate, spinTangent, spinObservable, tangentX, spinX,
      raising_eq_spin, lowering_eq_spin]
    ext i j
    simp [Matrix.smul_apply, smul_smul, RCLike.real_smul_eq_coe_mul]
    <;> ring
  · simp only [phaseCoordinate, spinTangent, spinObservable, tangentY, spinY,
      raising_eq_spin, lowering_eq_spin]
    ext i j
    simp [Matrix.smul_apply, smul_smul, RCLike.real_smul_eq_coe_mul]
    <;> ring

def singleSpinResolution (n : ℕ) :
    BlockResolution (spinReference n)
      (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a))
      (fun _ : Unit => n) (fun _ : Unit => 1) where
  embedding _ := 1
  isometry _ := by simp
  weight_nonneg _ := by norm_num
  reference := by simp [spinReference_eq_state]
  tangent a := by simp [spinTangent_eq_canonical]

-- 单个真实自旋实验上，全密度风险下确界已由实际高斯成员完成两侧夹逼。
theorem spin_optimalRisk_sandwich (N n : ℕ) (hn : 0 < n) {eps : ℝ} (heps : 0 < eps) :
    4*N / capFisherBound n ≤ optimalRisk N (spinReference n)
      (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a)) ∧
    optimalRisk N (spinReference n) (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a)) ≤
      2*N / gaussianFisher n eps := by
  have h := optimalRisk_sandwich_of_resolution (spinReference n)
    (fun a => spinTangent (spinCoefficient n) (phaseCoordinate a))
    (fun _ : Unit => n) (fun _ : Unit => 1) (singleSpinResolution n) N _
    (gaussian_risk_attainable (L := n+3) N n hn heps (by omega) (by omega))
  simpa using h

end FiniteCopy.Risk

