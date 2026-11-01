import FiniteCopy.IntegratedSpin
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CopyQuantumMetrology
variable {n : ℕ}

lemma seedMass_nonneg (v : Fin (n+1) → ℝ) : 0 ≤ seedMass v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

lemma square_le_seedMass (v : Fin (n+1) → ℝ) (i : Fin (n+1)) : v i ^ 2 ≤ seedMass v := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

lemma seed_adjacent_le_mass (v : Fin (n+1) → ℝ) (r : Fin n) :
    v r.castSucc * v r.succ ≤ seedMass v := by
  have hi := square_le_seedMass v r.castSucc
  have hj := square_le_seedMass v r.succ
  nlinarith [sq_nonneg (v r.castSucc - v r.succ)]

lemma seedMoment_le_mass (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : Fin (n+1) → ℝ) : seedMoment c v ≤ (∑ r, c r) * seedMass v := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (seed_adjacent_le_mass v r) (hc r)

lemma seedMoment_nonneg (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : Fin (n+1) → ℝ) (hv : ∀ i, 0 ≤ v i) : 0 ≤ seedMoment c v := by
  exact Finset.sum_nonneg fun r _ => mul_nonneg (mul_nonneg (hc r) (hv r.castSucc)) (hv r.succ)

lemma seedFisher_nonneg (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) : 0 ≤ seedFisher c v := by
  dsimp [seedFisher]
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by positivity) (seedMass_nonneg v))

-- 粗的全局可积控制足够证明有限 N 的 Fisher 严格正；它不用于渐近常数。
lemma seedFisher_le_mass (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : Fin (n+1) → ℝ) (hv : ∀ i, 0 < v i) :
    seedFisher c v ≤ (2 * (∑ r, c r)^2 / (n+1 : ℝ)) * seedMass v := by
  have hm := seedMass_pos v hv
  have hg := seedMoment_nonneg c hc v (fun i => (hv i).le)
  have hgm := seedMoment_le_mass c hc v
  have hs : seedMoment c v ^ 2 ≤ ((∑ r, c r) * seedMass v)^2 :=
    pow_le_pow_left₀ hg hgm 2
  calc
    seedFisher c v ≤ 2 * ((∑ r, c r) * seedMass v)^2 / ((n+1 : ℝ) * seedMass v) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
        (mul_nonneg (by positivity) hm.le)
    _ = _ := by field_simp <;> ring

lemma continuous_seedMass {X : Type*} [TopologicalSpace X]
    (v : X → Fin (n+1) → ℝ) (hv : ∀ i, Continuous fun t => v t i) :
    Continuous fun t => seedMass (v t) := by
  unfold seedMass
  fun_prop

lemma continuous_seedMoment {X : Type*} [TopologicalSpace X]
    (c : Fin n → ℝ) (v : X → Fin (n+1) → ℝ) (hv : ∀ i, Continuous fun t => v t i) :
    Continuous fun t => seedMoment c (v t) := by
  unfold seedMoment
  fun_prop

lemma continuous_seedFisher {X : Type*} [TopologicalSpace X]
    (c : Fin n → ℝ) (v : X → Fin (n+1) → ℝ) (hv : ∀ i, Continuous fun t => v t i)
    (hm : ∀ t, seedMass (v t) ≠ 0) : Continuous fun t => seedFisher c (v t) := by
  have hm' := continuous_seedMass v hv
  have hg := continuous_seedMoment c v hv
  unfold seedFisher
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact mul_ne_zero (by positivity) (hm t)

lemma integrable_seedFisher (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : ℝ → Fin (n+1) → ℝ) (hv : ∀ t i, 0 < v t i)
    (hcont : ∀ i, Continuous fun t => v t i)
    (hint : ∀ i, Integrable fun t => v t i ^ 2) :
    Integrable fun t => seedFisher c (v t) := by
  have hm : Integrable fun t => seedMass (v t) :=
    integrable_finsetSum _ (fun i _ => hint i)
  apply (hm.const_mul (2 * (∑ r, c r)^2 / (n+1 : ℝ))).mono'
  · exact (continuous_seedFisher c v hcont (fun t => ne_of_gt (seedMass_pos _ (hv t)))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_of_nonneg (seedFisher_nonneg c (v t))]
    exact seedFisher_le_mass c hc (v t) (hv t)

lemma integrated_spinFisher_pos (hn : 0 < n)
    (v : ℝ → Fin (n+1) → ℝ) (hv : ∀ t i, 0 < v t i)
    (hcont : ∀ i, Continuous fun t => v t i)
    (hint : ∀ i, Integrable fun t => v t i ^ 2) :
    0 < integratedSpinFisher volume (spinCoefficient n) v := by
  have hi := integrable_seedFisher (spinCoefficient n) (fun r => (spinCoefficient_pos r).le)
    v hv hcont hint
  apply (integral_pos_iff_support_of_nonneg (fun t => seedFisher_nonneg _ _) hi).2
  have hs : Function.support (fun t => seedFisher (spinCoefficient n) (v t)) = Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (spin_seedFisher_pos hn (v t) (hv t))
  rw [hs]
  simp


lemma phaseDirection_bound {L : ℕ} [NeZero L] (k : ZMod L) (b : Bool) :
    ‖phaseDirection k b‖ ≤ 1 := by
  have h := PhaseMoments.cx_sq_add_cy_sq k
  rw [Real.norm_eq_abs, abs_le]
  cases b <;> simp only [phaseDirection, Bool.false_eq_true, ite_false, ite_true]
  · constructor <;> nlinarith [sq_nonneg (PhaseMoments.cy k)]
  · constructor <;> nlinarith [sq_nonneg (PhaseMoments.cx k)]

lemma phaseScore_bound {L : ℕ} [NeZero L] (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : Fin (n+1) → ℝ) (hv : ∀ i, 0 < v i) (k : ZMod L) (b : Bool) :
    ‖phaseScore c v k b‖ ≤ 2 * ∑ r, c r := by
  have hm := seedMass_pos v hv
  have hg := seedMoment_nonneg c hc v (fun i => (hv i).le)
  have hgm := seedMoment_le_mass c hc v
  have hq : 0 ≤ 2 * seedMoment c v / seedMass v := div_nonneg (by positivity) hm.le
  have hqb : 2 * seedMoment c v / seedMass v ≤ 2 * ∑ r, c r := by
    apply (div_le_iff₀ hm).2
    nlinarith
  rw [phaseScore, norm_mul, Real.norm_of_nonneg hq]
  exact (mul_le_mul_of_nonneg_left (phaseDirection_bound k b) hq).trans (by simpa using hqb)

lemma continuous_phaseScore {X : Type*} [TopologicalSpace X] {L : ℕ} [NeZero L]
    (c : Fin n → ℝ) (v : X → Fin (n+1) → ℝ) (hv : ∀ i, Continuous fun t => v t i)
    (hm : ∀ t, seedMass (v t) ≠ 0) (k : ZMod L) (b : Bool) :
    Continuous fun t => phaseScore c (v t) k b := by
  have hm' := continuous_seedMass v hv
  have hg := continuous_seedMoment c v hv
  unfold phaseScore
  exact ((continuous_const.mul hg).div hm' hm).mul continuous_const

-- 各相位分别可积，有限相位求和没有隐藏正负无穷抵消。
lemma phase_statistics_integrable {L : ℕ} [NeZero L]
    (c : Fin n → ℝ) (hc : ∀ r, 0 ≤ c r)
    (v : ℝ → Fin (n+1) → ℝ) (hv : ∀ t i, 0 < v t i)
    (hcont : ∀ i, Continuous fun t => v t i)
    (hint : ∀ i, Integrable fun t => v t i ^ 2) (k : ZMod L) (a b : Bool) :
    Integrable (fun t => phaseProbability (L := L) (v t)) ∧
    Integrable (fun t => phaseProbability (L := L) (v t) * phaseScore c (v t) k a) ∧
    Integrable (fun t => phaseProbability (L := L) (v t) * phaseScore c (v t) k a *
      phaseScore c (v t) k b) := by
  have hm : Integrable fun t => seedMass (v t) :=
    integrable_finsetSum _ (fun i _ => hint i)
  have hp : Integrable fun t => phaseProbability (L := L) (v t) := hm.div_const _
  have hs (a : Bool) : AEStronglyMeasurable (fun t => phaseScore c (v t) k a) volume := (continuous_phaseScore c v hcont
    (fun t => ne_of_gt (seedMass_pos _ (hv t))) k a).aestronglyMeasurable
  have hb (a : Bool) : ∀ᵐ t, ‖phaseScore c (v t) k a‖ ≤ 2 * ∑ r, c r :=
    Filter.Eventually.of_forall fun t => phaseScore_bound c hc (v t) (hv t) k a
  have hfirst := hp.mul_bdd (hs a) (hb a)
  exact ⟨hp, hfirst, hfirst.mul_bdd (hs b) (hb b)⟩

end CopyQuantumMetrology


