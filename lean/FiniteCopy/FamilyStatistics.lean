import FiniteCopy.RiskTerminal
import FiniteCopy.ProductEstimator
import FiniteCopy.FiniteBlocks
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.GaussianLift
open FiniteCopy.Risk CopyQuantumMetrology

variable {B : Type} [Fintype B] [DecidableEq B] {L : ℕ} [NeZero L]
local instance : MeasurableSpace B := ⊤
local instance : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (ZMod L) := ⊤
local instance : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

instance gaussianOutcomeMeasure_sFinite : SFinite (gaussianOutcomeMeasure L) := by
  unfold gaussianOutcomeMeasure
  infer_instance

variable (n : B → ℕ) (w eps : B → ℝ)

def familyFisher : ℝ := ∑ b, w b * gaussianFisher (n b) (eps b)

def familyProbability (z : B × (ℝ × ZMod L)) : ℝ :=
  w z.1 * gaussianOutcomeProbability (n z.1) (eps z.1) z.2

def familyTangent (z : B × (ℝ × ZMod L)) (a : Fin 2) : ℝ :=
  w z.1 * gaussianOutcomeTangent (n z.1) (eps z.1) z.2 a

def familyEstimator (z : B × (ℝ × ZMod L)) (a : Fin 2) : ℝ :=
  gaussianOutcomeEstimator (n z.1) (eps z.1) (familyFisher n w eps) z.2 a

abbrev familyMeasure : Measure (B × (ℝ × ZMod L)) :=
  (Measure.count : Measure B).prod (gaussianOutcomeMeasure L)

lemma familyFisher_pos (hw : ∀ b, 0 ≤ w b) (heps : ∀ b, 0 < eps b)
    (hactive : ∃ b, 0 < w b ∧ 0 < n b) : 0 < familyFisher n w eps := by
  apply Finset.sum_pos'
  · intro b hb
    exact mul_nonneg (hw b) (gaussianFisher_nonneg _ _)
  · obtain ⟨b, hwb, hnb⟩ := hactive
    exact ⟨b, Finset.mem_univ b, mul_pos hwb (gaussianFisher_pos hnb (heps b))⟩

lemma family_integrable_slices (heps : ∀ b, 0 < eps b) (b : B) :
    (∀ a, Integrable (fun z : ℝ × ZMod L => familyProbability n w eps (b,z) *
      familyEstimator n w eps (b,z) a) (gaussianOutcomeMeasure L)) ∧
    (∀ a, Integrable (fun z : ℝ × ZMod L => familyProbability n w eps (b,z) *
      (familyEstimator n w eps (b,z) a)^2) (gaussianOutcomeMeasure L)) ∧
    (∀ a c, Integrable (fun z : ℝ × ZMod L => familyEstimator n w eps (b,z) a *
      familyTangent n w eps (b,z) c) (gaussianOutcomeMeasure L)) := by
  have hi := gaussianProduct_estimator_integrable (L := L) (n b) (heps b) (familyFisher n w eps)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simpa only [familyProbability, familyEstimator, mul_assoc] using (hi.1 a).const_mul (w b)
  · intro a
    simpa only [familyProbability, familyEstimator, mul_assoc] using (hi.2.1 a).const_mul (w b)
  · intro a c
    convert (hi.2.2 a c).const_mul (w b) using 1
    ext z
    dsimp [familyTangent, familyEstimator]
    ring

lemma family_mean_slice (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L) (b : B) (a : Fin 2) :
    (∫ z : ℝ × ZMod L, familyProbability n w eps (b,z) * familyEstimator n w eps (b,z) a
      ∂gaussianOutcomeMeasure L) = 0 := by
  simp only [familyProbability, familyEstimator, mul_assoc]
  rw [integral_const_mul, gaussianProduct_estimator_mean (n b) (heps b) hL]
  simp

lemma family_cross_slice (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L)
    (b : B) (a c : Fin 2) :
    (∫ z : ℝ × ZMod L, familyEstimator n w eps (b,z) a * familyTangent n w eps (b,z) c
      ∂gaussianOutcomeMeasure L) =
      if a = c then w b * (gaussianFisher (n b) (eps b) / familyFisher n w eps) else 0 := by
  have he (z : ℝ × ZMod L) :
      familyEstimator n w eps (b,z) a * familyTangent n w eps (b,z) c =
      w b * (gaussianOutcomeEstimator (n b) (eps b) (familyFisher n w eps) z a *
        gaussianOutcomeTangent (n b) (eps b) z c) := by
    dsimp [familyEstimator, familyTangent]
    ring
  simp_rw [he]
  rw [integral_const_mul, gaussianProduct_estimator_cross (n b) (heps b) hL]
  split_ifs <;> simp

lemma family_second_slice (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L)
    (b : B) (a : Fin 2) :
    (∫ z : ℝ × ZMod L, familyProbability n w eps (b,z) * (familyEstimator n w eps (b,z) a)^2
      ∂gaussianOutcomeMeasure L) =
      w b * (gaussianFisher (n b) (eps b) / (familyFisher n w eps * familyFisher n w eps)) := by
  simp only [familyProbability, familyEstimator, mul_assoc]
  rw [integral_const_mul]
  have hs := gaussianProduct_estimator_covariance (n b) (heps b) hL (familyFisher n w eps) a a
  simpa only [ite_true, pow_two, mul_assoc] using congrArg (fun x => w b * x) hs

-- 同一全局 Fisher 缩放可同时容纳零权重块与零自旋块。
theorem familyMomentUnbiased (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L)
    (hf : familyFisher n w eps ≠ 0) :
    MomentUnbiased (familyMeasure (B := B) (L := L)) (familyProbability n w eps)
      (familyTangent n w eps) (familyEstimator n w eps) where
  mean_integrable a := count_prod_integrable (gaussianOutcomeMeasure L) _
    (fun b => (family_integrable_slices n w eps heps b).1 a)
  second_integrable a := count_prod_integrable (gaussianOutcomeMeasure L) _
    (fun b => (family_integrable_slices n w eps heps b).2.1 a)
  cross_integrable a c := count_prod_integrable (gaussianOutcomeMeasure L) _
    (fun b => (family_integrable_slices n w eps heps b).2.2 a c)
  mean_zero a := by
    rw [count_prod_integral (gaussianOutcomeMeasure L) _
      (fun b => (family_integrable_slices n w eps heps b).1 a)]
    simp_rw [family_mean_slice n w eps heps hL]
    simp
  tangent_identity a c := by
    rw [count_prod_integral (gaussianOutcomeMeasure L) _
      (fun b => (family_integrable_slices n w eps heps b).2.2 a c)]
    simp_rw [family_cross_slice n w eps heps hL]
    by_cases hac : a = c
    · simp only [hac, ite_true, ← mul_div_assoc, ← Finset.sum_div]
      change familyFisher n w eps / familyFisher n w eps = 1
      exact div_self hf
    · simp [hac]

lemma family_second (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L)
    (hf : familyFisher n w eps ≠ 0) (a : Fin 2) :
    (∫ z, familyProbability n w eps z * (familyEstimator n w eps z a)^2
      ∂familyMeasure (B := B) (L := L)) = (familyFisher n w eps)⁻¹ := by
  rw [count_prod_integral (gaussianOutcomeMeasure L) _
    (fun b => (family_integrable_slices n w eps heps b).2.1 a)]
  simp_rw [family_second_slice n w eps heps hL, ← mul_div_assoc]
  rw [← Finset.sum_div]
  change familyFisher n w eps / (familyFisher n w eps * familyFisher n w eps) = _
  field_simp

theorem family_risk (N : ℕ) (heps : ∀ b, 0 < eps b) (hL : 3 ≤ L)
    (hf : familyFisher n w eps ≠ 0) :
    risk (familyMeasure (B := B) (L := L)) N (familyProbability n w eps)
      (familyEstimator n w eps) = 2 * N / familyFisher n w eps := by
  have hu := familyMomentUnbiased n w eps heps hL hf
  unfold risk FiniteCopy.POVM.statisticalCovTrace
  simp_rw [hu.mean_zero, sub_zero, mul_add]
  rw [integral_add (hu.second_integrable 0) (hu.second_integrable 1),
    family_second n w eps heps hL hf, family_second n w eps heps hL hf]
  ring


end FiniteCopy.GaussianLift

