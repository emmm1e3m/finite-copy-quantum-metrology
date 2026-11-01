import FiniteCopy.FiniteSeed
import FiniteCopy.BlockLift

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder Classical
noncomputable section
namespace FiniteCopy.SeedBlocks
open CopyQuantumMetrology FiniteCopy.Risk FiniteCopy.SeedPOVM

variable {ι : Type*} {B : Type} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
variable {n k : B → ℕ} {L : ℕ} [NeZero L]
variable {ρ : Matrix ι ι ℂ} {D : Fin 2 → Matrix ι ι ℂ} {w : B → ℝ}

abbrev Outcome (k : B → ℕ) (L : ℕ) := Σ b : B, Fin (k b) × ZMod L

local instance : MeasurableSpace (Outcome k L) := ⊤
local instance : MeasurableSingletonClass (Outcome k L) := ⟨fun _ => trivial⟩

def totalFisher (w : B → ℝ) (S : ∀ b, Scheme (n b) (k b)) : ℝ :=
  ∑ b, w b * (S b).totalFisher

variable (R : BlockResolution ρ D n w) (S : ∀ b, Scheme (n b) (k b))

-- 各块允许不同种子数，结果空间保留实际块标签。
def effect (z : Outcome k L) : Matrix ι ι ℂ :=
  R.embedding z.1 * (S z.1).outcomeEffect z.2 * (R.embedding z.1)ᴴ

def probability (z : Outcome k L) : ℝ := born ρ (effect R S z)
def tangent (z : Outcome k L) (a : Fin 2) : ℝ := born (D a) (effect R S z)
def outcomeScore : Outcome k L → Fin 2 → ℝ := score (probability R S) (tangent R S)
def simpleScore (z : Outcome k L) (a : Fin 2) : ℝ := (S z.1).simpleScore z.2 a

theorem finite_integrable {E : Type*} [NormedAddCommGroup E]
    (f : Outcome k L → E) : Integrable f Measure.count :=
  integrable_count_iff.mpr (hasSum_fintype (fun z => ‖f z‖)).summable

theorem effect_positive (z : Outcome k L) : (effect R S z).PosSemidef := by
  simpa only [effect, Matrix.conjTranspose_conjTranspose] using
    ((S z.1).outcomeEffect_positive z.2).conjTranspose_mul_mul_same ((R.embedding z.1)ᴴ)

theorem effect_sum (hd : ∀ b, n b+1 ≤ L)
    (hcomplete : (∑ b, R.embedding b * (R.embedding b)ᴴ) = (1 : Matrix ι ι ℂ)) :
    (∑ z : Outcome k L, effect R S z) = 1 := by
  rw [Fintype.sum_sigma]
  have hs (b : B) : (∑ z : Fin (k b) × ZMod L,
      effect R S ⟨b,z⟩) = R.embedding b * (R.embedding b)ᴴ := by
    simp only [effect]
    rw [← Matrix.sum_mul Finset.univ
      (fun z : Fin (k b) × ZMod L => R.embedding b * (S b).outcomeEffect z) (R.embedding b)ᴴ,
      ← Matrix.mul_sum Finset.univ (fun z : Fin (k b) × ZMod L => (S b).outcomeEffect z) (R.embedding b),
      (S b).outcomeEffect_complete (hd b), Matrix.mul_one]
  simp_rw [hs]
  exact hcomplete

def densityPOVM (hd : ∀ b, n b+1 ≤ L)
    (hcomplete : (∑ b, R.embedding b * (R.embedding b)ᴴ) = (1 : Matrix ι ι ℂ)) :
    DensityPOVM ι (Outcome k L) Measure.count where
  effect := effect R S
  positive := effect_positive R S
  integrable _ _ := finite_integrable _
  complete i j := by
    rw [integral_count]
    simpa only [Matrix.sum_apply] using congrFun (congrFun (effect_sum R S hd hcomplete) i) j

theorem compression_same (b : B) (z : Fin (k b) × ZMod L) :
    (R.embedding b)ᴴ * effect R S ⟨b,z⟩ * R.embedding b = (S b).outcomeEffect z := by
  change (R.embedding b)ᴴ * (R.embedding b * (S b).outcomeEffect z * (R.embedding b)ᴴ) * R.embedding b = _
  calc
    _ = ((R.embedding b)ᴴ * R.embedding b) * (S b).outcomeEffect z *
        ((R.embedding b)ᴴ * R.embedding b) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [R.isometry]; simp

theorem compression_other
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (b c : B) (hbc : b ≠ c) (z : Fin (k c) × ZMod L) :
    (R.embedding b)ᴴ * effect R S ⟨c,z⟩ * R.embedding b = 0 := by
  change (R.embedding b)ᴴ * (R.embedding c * (S c).outcomeEffect z * (R.embedding c)ᴴ) * R.embedding b = _
  calc
    _ = ((R.embedding b)ᴴ * R.embedding c) * (S c).outcomeEffect z *
        ((R.embedding c)ᴴ * R.embedding b) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [horth b c hbc]; simp

theorem probability_eq
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) : probability R S z = w z.1 * (S z.1).probability z.2 := by
  rcases z with ⟨b,z⟩
  unfold probability
  rw [resolution_born_reference ρ D n w R, Finset.sum_eq_single b]
  · rw [compression_same R S]
    rw [← spinReference_eq_state]
    rfl
  · intro c hc hcb
    rw [compression_other R S horth c b hcb]
    simp [born]
  · simp

theorem tangent_eq
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) (a : Fin 2) : tangent R S z a = w z.1 * (S z.1).tangent z.2 a := by
  rcases z with ⟨b,z⟩
  unfold tangent
  rw [resolution_born_tangent ρ D n w R, Finset.sum_eq_single b]
  · rw [compression_same R S, ← spinTangent_eq_canonical]
    rfl
  · intro c hc hcb
    rw [compression_other R S horth c b hcb]
    simp [born]
  · simp

theorem probability_nonneg
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) : 0 ≤ probability R S z := by
  rw [probability_eq R S horth]
  exact mul_nonneg (R.weight_nonneg _) ((S z.1).probability_nonneg _)

theorem tangent_eq_probability_score
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) (a : Fin 2) :
    tangent R S z a = probability R S z * simpleScore S z a := by
  rw [tangent_eq R S horth, probability_eq R S horth, (S z.1).tangent_eq]
  simp only [simpleScore, mul_assoc]

-- 用带概率权重的恒等式同时处理零块权与零种子权。
theorem weighted_score
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) (a : Fin 2) :
    probability R S z * outcomeScore R S z a = probability R S z * simpleScore S z a := by
  unfold outcomeScore score
  rw [tangent_eq_probability_score R S horth]
  by_cases hp : probability R S z = 0
  · simp [hp]
  · field_simp

theorem weighted_second
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (z : Outcome k L) (a b : Fin 2) :
    probability R S z * outcomeScore R S z a * outcomeScore R S z b =
      probability R S z * simpleScore S z a * simpleScore S z b := by
  by_cases hp : probability R S z = 0
  · simp [hp]
  · have hs (c : Fin 2) : outcomeScore R S z c = simpleScore S z c := by
      unfold outcomeScore score
      rw [tangent_eq_probability_score R S horth]
      field_simp
    rw [hs a, hs b]

theorem score_mean
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (a : Fin 2) :
    (∫ z : Outcome k L, probability R S z * outcomeScore R S z a ∂Measure.count) = 0 := by
  have he (z : Outcome k L) : probability R S z * outcomeScore R S z a =
      w z.1 * ((S z.1).probability z.2 * (S z.1).outcomeScore z.2 a) := by
    rw [weighted_score R S horth, (S z.1).weighted_score, probability_eq R S horth]
    unfold simpleScore
    ring
  simp_rw [he]
  rw [integral_count, Fintype.sum_sigma]
  simp only [← Finset.mul_sum]
  have hs (b : B) : (∑ z : Fin (k b) × ZMod L,
      (S b).probability z * (S b).outcomeScore z a) = 0 := by
    simpa only [integral_count] using (S b).score_mean hL a
  simp_rw [hs]
  simp

theorem fisher_entry
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (a b : Fin 2) :
    fisherEntry (Measure.count : Measure (Outcome k L)) (probability R S) (outcomeScore R S) a b =
      if a=b then totalFisher w S / 2 else 0 := by
  have he (z : Outcome k L) : probability R S z * outcomeScore R S z a * outcomeScore R S z b =
      w z.1 * ((S z.1).probability z.2 * (S z.1).outcomeScore z.2 a * (S z.1).outcomeScore z.2 b) := by
    rw [weighted_second R S horth, (S z.1).weighted_second, probability_eq R S horth]
    unfold simpleScore
    ring
  unfold fisherEntry
  simp_rw [he]
  rw [integral_count, Fintype.sum_sigma]
  simp only [← Finset.mul_sum]
  have hs (c : B) : (∑ z : Fin (k c) × ZMod L,
      (S c).probability z * (S c).outcomeScore z a * (S c).outcomeScore z b) =
        if a=b then 2*(S c).value else 0 := by
    simpa only [fisherEntry, integral_count] using (S c).fisher_entry hL a b
  simp_rw [hs]
  by_cases hab : a=b
  · simp only [hab, ite_true, totalFisher, Scheme.totalFisher, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  · simp [hab]

theorem fisher_matrix
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) :
    (fun a b : Fin 2 => fisherEntry (Measure.count : Measure (Outcome k L))
      (probability R S) (outcomeScore R S) a b) =
      (totalFisher w S / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  rw [fisher_entry R S horth hL]
  simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite]

theorem fisher_trace
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) :
    FiniteCopy.POVM.statisticalFisherTrace (Measure.count : Measure (Outcome k L))
      (probability R S) (outcomeScore R S) = totalFisher w S := by
  unfold FiniteCopy.POVM.statisticalFisherTrace
  have he (z : Outcome k L) : probability R S z * ((outcomeScore R S z 0)^2 + (outcomeScore R S z 1)^2) =
      probability R S z * outcomeScore R S z 0 * outcomeScore R S z 0 +
        probability R S z * outcomeScore R S z 1 * outcomeScore R S z 1 := by ring
  simp_rw [he]
  rw [integral_add (finite_integrable _) (finite_integrable _)]
  change fisherEntry Measure.count (probability R S) (outcomeScore R S) 0 0 +
    fisherEntry Measure.count (probability R S) (outcomeScore R S) 1 1 = _
  rw [fisher_entry R S horth hL, fisher_entry R S horth hL]
  simp only [ite_true]
  ring

def estimator (z : Outcome k L) (a : Fin 2) : ℝ := outcomeScore R S z a / (totalFisher w S / 2)

theorem estimator_mean
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (a : Fin 2) :
    (∫ z : Outcome k L, probability R S z * estimator R S z a ∂Measure.count) = 0 := by
  simp only [estimator, ← mul_div_assoc, integral_div, score_mean R S horth hL, zero_div]

theorem estimator_cross
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (hT : 0 < totalFisher w S) (a b : Fin 2) :
    (∫ z : Outcome k L, estimator R S z a * tangent R S z b ∂Measure.count) =
      if a=b then 1 else 0 := by
  have hp (z : Outcome k L) : probability R S z * outcomeScore R S z b = tangent R S z b := by
    rw [weighted_score R S horth, tangent_eq_probability_score R S horth]
  have he (z : Outcome k L) : estimator R S z a * tangent R S z b =
      (probability R S z * outcomeScore R S z a * outcomeScore R S z b) / (totalFisher w S / 2) := by
    rw [← hp]
    unfold estimator
    ring
  simp_rw [he]
  rw [integral_div]
  change fisherEntry Measure.count (probability R S) (outcomeScore R S) a b / (totalFisher w S / 2) = _
  rw [fisher_entry R S horth hL]
  split_ifs <;> simp [ne_of_gt hT]

theorem estimator_covariance
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (hT : 0 < totalFisher w S) (a b : Fin 2) :
    (∫ z : Outcome k L, probability R S z * estimator R S z a * estimator R S z b ∂Measure.count) =
      if a=b then (totalFisher w S / 2)⁻¹ else 0 := by
  exact isotropic_score_covariance Measure.count (probability R S) (outcomeScore R S)
    (totalFisher w S / 2) (ne_of_gt (div_pos hT (by norm_num)))
    (fisher_entry R S horth hL) a b

theorem momentUnbiased
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (hT : 0 < totalFisher w S) :
    MomentUnbiased (Measure.count : Measure (Outcome k L))
      (probability R S) (tangent R S) (estimator R S) := by
  exact ⟨fun _ => finite_integrable _, fun _ => finite_integrable _, fun _ _ => finite_integrable _,
    estimator_mean R S horth hL, estimator_cross R S horth hL hT⟩

theorem estimator_risk
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hL : 3 ≤ L) (hT : 0 < totalFisher w S) (N : ℕ) :
    risk (Measure.count : Measure (Outcome k L)) N (probability R S) (estimator R S) =
      4*N / totalFisher w S := by
  have hu := momentUnbiased R S horth hL hT
  have hsec (a : Fin 2) :
      (∫ z : Outcome k L, probability R S z * (estimator R S z a)^2 ∂Measure.count) =
        (totalFisher w S / 2)⁻¹ := by
    simpa only [pow_two, ← mul_assoc, ite_true] using estimator_covariance R S horth hL hT a a
  unfold risk FiniteCopy.POVM.statisticalCovTrace
  simp_rw [hu.mean_zero, sub_zero, mul_add]
  rw [integral_add (hu.second_integrable 0) (hu.second_integrable 1), hsec, hsec]
  ring

-- 真实测量与真实估计器作为风险集合见证，供全N最优达到直接使用。
theorem risk_attainable (hd : ∀ b, n b+1 ≤ L) (hL : 3 ≤ L)
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hcomplete : (∑ b, R.embedding b * (R.embedding b)ᴴ) = (1 : Matrix ι ι ℂ))
    (hT : 0 < totalFisher w S) (N : ℕ) :
    4*N / totalFisher w S ∈ attainableRisks N ρ D := by
  refine ⟨Outcome k L, inferInstance, Measure.count, densityPOVM R S hd hcomplete,
    estimator R S, ?_, ?_⟩
  · exact momentUnbiased R S horth hL hT
  · exact (estimator_risk R S horth hL hT N).symm

end FiniteCopy.SeedBlocks
