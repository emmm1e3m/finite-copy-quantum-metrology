import FiniteCopy.POVMLower
import FiniteCopy.Schur
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix Filter
noncomputable section
namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM

-- 任意结果测度空间上的完整 PSD 密度，不限制结果数或秩。
structure DensityPOVM (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) where
  effect : Ω → Matrix ι ι ℂ
  positive : ∀ z, (effect z).PosSemidef
  integrable : ∀ i j, Integrable (fun z => effect z i j) μ
  complete : ∀ i j, ∫ z, effect z i j ∂μ = (1 : Matrix ι ι ℂ) i j

def score {Ω : Type*} (p : Ω → ℝ) (d : Ω → Fin 2 → ℝ) (z : Ω) (a : Fin 2) : ℝ :=
  d z a / p z

-- 局部无偏性由 Born 切向的真实矩条件刻画，二阶矩有限。
structure MomentUnbiased {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (d u : Ω → Fin 2 → ℝ) : Prop where
  mean_integrable : ∀ a, Integrable (fun z => p z * u z a) μ
  second_integrable : ∀ a, Integrable (fun z => p z * (u z a)^2) μ
  cross_integrable : ∀ a b, Integrable (fun z => u z a * d z b) μ
  mean_zero : ∀ a, ∫ z, p z * u z a ∂μ = 0
  tangent_identity : ∀ a b, ∫ z, u z a * d z b ∂μ = if a=b then 1 else 0

def risk {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (p : Ω → ℝ) (u : Ω → Fin 2 → ℝ) : ℝ :=
  N * statisticalCovTrace μ p u

-- 仿射局部曲线的期望与矩条件一致，并推出真实期望导数。
theorem expectation_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (d u : Ω → Fin 2 → ℝ) (hu : MomentUnbiased μ p d u)
    (a b : Fin 2) :
    HasDerivAt (fun θ : ℝ => ∫ z, u z a * (p z + θ * d z b) ∂μ)
      (if a=b then 1 else 0) 0 := by
  have h (θ : ℝ) : (∫ z, u z a * (p z + θ * d z b) ∂μ) =
      θ * (if a=b then 1 else 0) := by
    have hp (z : Ω) : u z a * (p z + θ * d z b) =
        p z * u z a + θ * (u z a * d z b) := by ring
    simp_rw [hp]
    rw [integral_add (hu.mean_integrable a) ((hu.cross_integrable a b).const_mul θ),
      integral_const_mul, hu.mean_zero, hu.tangent_identity, zero_add]
  simpa only [h, id_eq, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const (if a=b then (1 : ℝ) else 0)

lemma weighted_score_eq {Ω : Type*} (p : Ω → ℝ) (d : Ω → Fin 2 → ℝ)
    (hzero : ∀ z, p z = 0 → ∀ a, d z a = 0) (z : Ω) (a : Fin 2) :
    p z * score p d z a = d z a := by
  by_cases hz : p z = 0
  · simp [score, hz, hzero z hz a]
  · dsimp [score]; field_simp

-- 只需 Fisher 平方密度的可积性；它将在实际模型中由逐块上界得到。
theorem risk_lower_of_fisher_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (p : Ω → ℝ) (d u : Ω → Fin 2 → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hzero : ∀ z, p z = 0 → ∀ a, d z a = 0)
    (hs : ∀ a, Integrable (fun z => p z * (score p d z a)^2) μ)
    (hu : MomentUnbiased μ p d u) (B : ℝ)
    (hB : statisticalFisherTrace μ p (score p d) ≤ B) :
    0 < B ∧ 4 * N / B ≤ risk μ N p u := by
  have hprod (z : Ω) (a b : Fin 2) :
      p z * u z a * score p d z b = u z a * d z b := by
    rw [mul_assoc, mul_comm (u z a), ← mul_assoc, weighted_score_eq p d hzero]
    ring
  have hcr := cramerRao_trace μ p (score p d) u hp hu.second_integrable hs
    (fun a b => by simpa only [hprod] using hu.cross_integrable a b)
    hu.mean_zero (fun a b => by simpa only [hprod] using hu.tangent_identity a b)
  refine ⟨hcr.1.trans_le hB, ?_⟩
  have hdiv : 4 / B ≤ 4 / statisticalFisherTrace μ p (score p d) :=
    div_le_div_of_nonneg_left (by norm_num) hcr.1 hB
  have hm := mul_le_mul_of_nonneg_left (hdiv.trans hcr.2) (Nat.cast_nonneg N)
  calc
    4 * (N : ℝ) / B = (N : ℝ) * (4 / B) := by ring
    _ ≤ risk μ N p u := hm

-- 下确界取遍实际效果密度与估计器，未用封闭标量风险公式代替。
def attainableRisks (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (M : @DensityPOVM ι Ω _ _ mΩ μ) (u : Ω → Fin 2 → ℝ),
    @MomentUnbiased Ω mΩ μ (fun z => born ρ (M.effect z))
      (fun z a => born (D a) (M.effect z)) u ∧
    r = @risk Ω mΩ μ N (fun z => born ρ (M.effect z)) u}

def optimalRisk (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : ℝ :=
  sInf (attainableRisks N ρ D)

-- 下界针对全部合法测量，上界由某个具体合法测量的风险集合成员给出。
theorem optimalRisk_sandwich (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (lo hi : ℝ)
    (hlower : ∀ r ∈ attainableRisks N ρ D, lo ≤ r)
    (hupper : hi ∈ attainableRisks N ρ D) :
    lo ≤ optimalRisk N ρ D ∧ optimalRisk N ρ D ≤ hi := by
  have hb : BddBelow (attainableRisks N ρ D) := ⟨lo, hlower⟩
  exact ⟨le_csInf ⟨hi, hupper⟩ hlower, csInf_le hb hupper⟩

-- 真实风险夹逼的终端逻辑；上下界序列仍须由实际对象实例化。
theorem risk_first_correction_of_sandwich (C lo hi : ℕ → ℝ) (a : ℝ)
    (hlo : ∀ᶠ N in atTop, lo N ≤ C N)
    (hhi : ∀ᶠ N in atTop, C N ≤ hi N)
    (hl : Tendsto (fun N : ℕ => Real.sqrt N * (lo N - 2)) atTop (𝓝 a))
    (hh : Tendsto (fun N : ℕ => Real.sqrt N * (hi N - 2)) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => Real.sqrt N * (C N - 2)) atTop (𝓝 a) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
  · filter_upwards [hlo] with N hN
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hN 2) (Real.sqrt_nonneg _)
  · filter_upwards [hhi] with N hN
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hN 2) (Real.sqrt_nonneg _)

end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM

-- 零概率块允许存在；PSD 忠实参考态保证其切向也为零。
theorem sq_sum_div_le {B : Type*} [Fintype B] (p d : B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hz : ∀ b, p b = 0 → d b = 0) :
    (∑ b, d b)^2 / (∑ b, p b) ≤ ∑ b, (d b)^2 / p b := by
  have hq (b : B) : 0 ≤ (d b)^2 / p b := div_nonneg (sq_nonneg _) (hp b)
  apply div_le_of_le_mul₀ (Finset.sum_nonneg fun b _ => hp b)
    (Finset.sum_nonneg fun b _ => hq b)
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun b _ => hq b) (fun b _ => hp b)
  intro b hb
  by_cases h : p b = 0
  · simp [h, hz b h]
  · rw [div_mul_cancel₀ _ h]

theorem weighted_sq_sum_div_le {B : Type*} [Fintype B]
    (w p d : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hp : ∀ b, 0 ≤ p b)
    (hz : ∀ b, p b = 0 → d b = 0) :
    (∑ b, w b * d b)^2 / (∑ b, w b * p b) ≤ ∑ b, w b * ((d b)^2 / p b) := by
  have h := sq_sum_div_le (fun b => w b * p b) (fun b => w b * d b)
    (fun b => mul_nonneg (hw b) (hp b)) (fun b hb => by
      rcases mul_eq_zero.mp hb with hb | hb
      · simp [hb]
      · simp [hz b hb])
  convert h using 1
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hw0 : w b = 0
  · simp [hw0]
  · by_cases hp0 : p b = 0
    · simp [hp0]
    · field_simp

section Block
variable {B Ω : Type*} [Fintype B] [MeasurableSpace Ω]
variable (μ : Measure Ω) (n : B → ℕ) (w : B → ℝ)
variable (E : ∀ b, Ω → Matrix (Fin (n b+1)) (Fin (n b+1)) ℂ)

def blockProbability (z : Ω) : ℝ :=
  ∑ b, w b * born (state (n b)) (E b z)

def blockDerivative (z : Ω) (a : Fin 2) : ℝ :=
  ∑ b, w b * born (if a = 0 then tangentX (n b) (FiniteCopy.Algebra.spinEdge (n b))
      else tangentY (n b) (FiniteCopy.Algebra.spinEdge (n b))) (E b z)

def blockFisherDensity (z : Ω) : ℝ :=
  ((blockDerivative n w E z 0)^2 + (blockDerivative n w E z 1)^2) /
    blockProbability n w E z

def capFisherBound (n : ℕ) : ℝ :=
  (4 / (n+1 : ℕ)) * ∑ i ∈ Finset.range n,
    FiniteCopy.Algebra.spinEdge n i *
      min (FiniteCopy.Algebra.spinEdge n i) (NHLowerBound.spinTau n)

lemma blockProbability_nonneg (hw : ∀ b, 0 ≤ w b)
    (hE : ∀ b z, (E b z).PosSemidef) (z : Ω) : 0 ≤ blockProbability n w E z :=
  Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (born_state_nonneg _ _ (hE b z))

lemma blockDerivative_zero (hw : ∀ b, 0 ≤ w b)
    (hE : ∀ b z, (E b z).PosSemidef) (z : Ω)
    (hz : blockProbability n w E z = 0) (a : Fin 2) : blockDerivative n w E z a = 0 := by
  have hb (b : B) : w b * born (state (n b)) (E b z) = 0 := by
    have hnon (b : B) := mul_nonneg (hw b) (born_state_nonneg _ _ (hE b z))
    have hle := Finset.single_le_sum (fun b _ => hnon b) (Finset.mem_univ b)
    change w b * born (state (n b)) (E b z) ≤ blockProbability n w E z at hle
    exact le_antisymm (hz ▸ hle) (hnon b)
  apply Finset.sum_eq_zero
  intro b hb'
  rcases mul_eq_zero.mp (hb b) with h | h
  · simp [h]
  · have he := (born_state_zero_iff _ _ (hE b z)).mp h
    simp [he, born]

lemma blockFisherDensity_bound (hw : ∀ b, 0 ≤ w b)
    (hE : ∀ b z, (E b z).PosSemidef) (z : Ω) :
    blockFisherDensity n w E z ≤
      ∑ b, w b * fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z) := by
  have hzero (b : B) (h : born (state (n b)) (E b z) = 0)
      (A : Matrix (Fin (n b+1)) (Fin (n b+1)) ℂ) : born A (E b z) = 0 := by
    rw [(born_state_zero_iff _ _ (hE b z)).mp h]
    simp [born]
  have hx := weighted_sq_sum_div_le w
    (fun b => born (state (n b)) (E b z))
    (fun b => born (tangentX (n b) (FiniteCopy.Algebra.spinEdge (n b))) (E b z))
    hw (fun b => born_state_nonneg _ _ (hE b z)) (fun b h => hzero b h _)
  have hy := weighted_sq_sum_div_le w
    (fun b => born (state (n b)) (E b z))
    (fun b => born (tangentY (n b) (FiniteCopy.Algebra.spinEdge (n b))) (E b z))
    hw (fun b => born_state_nonneg _ _ (hE b z)) (fun b h => hzero b h _)
  simpa only [blockFisherDensity, blockDerivative, blockProbability, if_pos rfl,
    show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false, add_div, fisherDensity,
    mul_add, Finset.sum_add_distrib] using add_le_add hx hy

lemma blockProbability_integrable
    (hint : ∀ b i j, Integrable (fun z => E b z i j) μ) :
    Integrable (blockProbability n w E) μ := by
  apply integrable_finsetSum
  intro b hb
  exact (trace_mul_integrable μ (E b) (state (n b)) (hint b)).re.const_mul _

lemma blockDerivative_integrable
    (hint : ∀ b i j, Integrable (fun z => E b z i j) μ) (a : Fin 2) :
    Integrable (fun z => blockDerivative n w E z a) μ := by
  apply integrable_finsetSum
  intro b hb
  exact (trace_mul_integrable μ (E b) _ (hint b)).re.const_mul _

-- Fisher 密度可积性由逐块证书支配推出，而非加入测量类定义。
theorem block_fisher_bound (hw : ∀ b, 0 ≤ w b)
    (hE : ∀ b z, (E b z).PosSemidef)
    (hint : ∀ b i j, Integrable (fun z => E b z i j) μ)
    (hcomplete : ∀ b i j, ∫ z, E b z i j ∂μ =
      (1 : Matrix (Fin (n b+1)) (Fin (n b+1)) ℂ) i j) :
    Integrable (blockFisherDensity n w E) μ ∧
    (∫ z, blockFisherDensity n w E z ∂μ) ≤ ∑ b, w b * capFisherBound (n b) := by
  have hblock (b : B) := canonical_arbitrary_density_fisher_bound μ (n b) (E b)
    (hE b) (hint b) (hcomplete b)
  have hdom : Integrable (fun z => ∑ b, w b *
      fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z)) μ :=
    integrable_finsetSum _ (fun b _ => (hblock b).1.const_mul _)
  have hfmeas : AEStronglyMeasurable (blockFisherDensity n w E) μ := by
    exact (((blockDerivative_integrable μ n w E hint 0).aemeasurable.pow_const 2).add
      ((blockDerivative_integrable μ n w E hint 1).aemeasurable.pow_const 2)).div
      (blockProbability_integrable μ n w E hint).aemeasurable |>.aestronglyMeasurable
  have hfnon (z : Ω) : 0 ≤ blockFisherDensity n w E z :=
    div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (blockProbability_nonneg n w E hw hE z)
  have hfi : Integrable (blockFisherDensity n w E) μ := by
    apply hdom.mono' hfmeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnon z)]
    exact blockFisherDensity_bound n w E hw hE z
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ z, ∑ b, w b * fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z) ∂μ :=
      integral_mono hfi hdom (blockFisherDensity_bound n w E hw hE)
    _ = ∑ b, w b * ∫ z, fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z) ∂μ := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro b hb; exact (hblock b).1.const_mul _
    _ ≤ _ := Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hblock b).2 (hw b)

end Block
end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM

lemma weighted_score_square {Ω : Type*} (p : Ω → ℝ) (d : Ω → Fin 2 → ℝ)
    (z : Ω) (a : Fin 2) : p z * (score p d z a)^2 = (d z a)^2 / p z := by
  by_cases hz : p z = 0
  · simp [hz, score]
  · dsimp [score]; field_simp

section BlockRisk
variable {B Ω : Type*} [Fintype B] [MeasurableSpace Ω]
variable (μ : Measure Ω) (n : B → ℕ) (w : B → ℝ)
variable (E : ∀ b, Ω → Matrix (Fin (n b+1)) (Fin (n b+1)) ℂ)

lemma blockFisherDensity_score (z : Ω) : blockFisherDensity n w E z =
    blockProbability n w E z * ((score (blockProbability n w E) (blockDerivative n w E) z 0)^2 +
      (score (blockProbability n w E) (blockDerivative n w E) z 1)^2) := by
  rw [mul_add, weighted_score_square, weighted_score_square, ← add_div]
  rfl

lemma block_score_integrable (hw : ∀ b, 0 ≤ w b)
    (hE : ∀ b z, (E b z).PosSemidef)
    (hint : ∀ b i j, Integrable (fun z => E b z i j) μ)
    (hf : Integrable (blockFisherDensity n w E) μ) (a : Fin 2) :
    Integrable (fun z => blockProbability n w E z *
      (score (blockProbability n w E) (blockDerivative n w E) z a)^2) μ := by
  have hp := (blockProbability_integrable μ n w E hint).aemeasurable
  have hd := (blockDerivative_integrable μ n w E hint a).aemeasurable
  apply hf.mono'
  · exact (hp.mul ((hd.div hp).pow_const 2)).aestronglyMeasurable
  · filter_upwards [] with z
    have hp0 := blockProbability_nonneg n w E hw hE z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (sq_nonneg _)), blockFisherDensity_score]
    fin_cases a <;> dsimp
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hp0
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) hp0

-- 任意完整 PSD 块密度与任意矩条件局部无偏估计器的真实风险下界。
theorem arbitrary_block_density_risk_lower (N : ℕ) (hw : ∀ b, 0 ≤ w b)
    (M : ∀ b, DensityPOVM (Fin (n b+1)) Ω μ) (u : Ω → Fin 2 → ℝ)
    (hu : MomentUnbiased μ (blockProbability n w (fun b => (M b).effect))
      (blockDerivative n w (fun b => (M b).effect)) u) :
    0 < (∑ b, w b * capFisherBound (n b)) ∧
    4 * N / (∑ b, w b * capFisherBound (n b)) ≤
      risk μ N (blockProbability n w (fun b => (M b).effect)) u := by
  let E := fun b => (M b).effect
  have hF := block_fisher_bound μ n w E hw (fun b => (M b).positive)
    (fun b => (M b).integrable) (fun b => (M b).complete)
  apply risk_lower_of_fisher_bound μ N _ _ u
    (blockProbability_nonneg n w E hw (fun b => (M b).positive))
    (fun z hz a => blockDerivative_zero n w E hw (fun b => (M b).positive) z hz a)
    (block_score_integrable μ n w E hw (fun b => (M b).positive)
      (fun b => (M b).integrable) hF.1) hu
  simpa only [statisticalFisherTrace, ← blockFisherDensity_score] using hF.2

end BlockRisk

lemma capFisherBound_eq (n : ℕ) : capFisherBound n =
    (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - 4 * NHLowerBound.spinL n := by
  have hs := FiniteCopy.Algebra.spinA_sum n
  rw [FiniteCopy.Algebra.spinA_sum_eq_edge_sq] at hs
  unfold capFisherBound NHLowerBound.spinL NHLowerBound.spinD
  push_cast
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  nlinarith [hs]

lemma schur_capFisherBound (N : ℕ) :
    FiniteCopy.Schur.schurAverage capFisherBound N =
      2*N - 4*FiniteCopy.Schur.schurAverage NHLowerBound.spinL N := by
  rw [show capFisherBound = (fun n : ℕ => (8/3 : ℝ) * ((n : ℝ)/2) *
    ((n : ℝ)/2+1) - 4 * NHLowerBound.spinL n) from funext capFisherBound_eq]
  exact FiniteCopy.Schur.schurAverage_fisher _ N

-- 截顶根的已证逐自旋极限实际接入 Schur 平均。
theorem cap_risk_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N *
      (4*N / FiniteCopy.Schur.schurAverage capFisherBound N - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  simp_rw [schur_capFisherBound]
  apply FiniteCopy.Schur.schurRisk_scaled_limit
  have hratio : Tendsto (fun n : ℕ => NHLowerBound.spinL n / n) atTop (𝓝 (1/4 : ℝ)) := by
    have h := NHLowerBound.canonical_spinL_ratio_limit.div_const 2
    convert h using 1
    · ext n; ring
    · norm_num
  have hz : Tendsto (fun n : ℕ => (NHLowerBound.spinL n - (n : ℝ)/4) / n)
      atTop (𝓝 (0 : ℝ)) := by
    have hsub := hratio.sub_const (1/4)
    norm_num at hsub
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr hz
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro he
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact False.elim (hne he)

end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM
section Compression
variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [MeasurableSpace Ω] (μ : Measure Ω)

lemma sandwich_integrable (U : Matrix ι κ ℂ) (E : Ω → Matrix ι ι ℂ)
    (hE : ∀ i j, Integrable (fun z => E z i j) μ) (i j : κ) :
    Integrable (fun z => (Uᴴ * E z * U) i j) μ := by
  simp only [Matrix.mul_apply]
  apply integrable_finsetSum
  intro k hk
  apply Integrable.mul_const
  apply integrable_finsetSum
  intro l hl
  exact (hE l k).const_mul _

lemma integral_sandwich (U : Matrix ι κ ℂ) (E : Ω → Matrix ι ι ℂ)
    (hE : ∀ i j, Integrable (fun z => E z i j) μ) (i j : κ) :
    (∫ z, (Uᴴ * E z * U) i j ∂μ) =
      (Uᴴ * Matrix.of (fun i j => ∫ z, E z i j ∂μ) * U) i j := by
  simp only [Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const, integral_finsetSum]
    · simp_rw [integral_const_mul]
      rfl
    · intro l hl; exact (hE l k).const_mul _
  · intro k hk
    exact (integrable_finsetSum _ (fun l _ => (hE l k).const_mul _)).mul_const _

-- 压缩到任意等距列框架：PSD、可积性与完整性全部由原测量继承。
def DensityPOVM.compress (M : DensityPOVM ι Ω μ) (U : Matrix ι κ ℂ)
    (hU : Uᴴ * U = 1) : DensityPOVM κ Ω μ where
  effect z := Uᴴ * M.effect z * U
  positive z := (M.positive z).conjTranspose_mul_mul_same U
  integrable := sandwich_integrable μ U M.effect M.integrable
  complete i j := by
    rw [integral_sandwich μ U M.effect M.integrable]
    have hmat : Matrix.of (fun i j => ∫ z, M.effect z i j ∂μ) = (1 : Matrix ι ι ℂ) :=
      funext fun i => funext (M.complete i)
    rw [hmat, Matrix.mul_one, hU]

-- 矩形矩阵的迹循环律给出原实验与压缩实验完全相同的 Born 值。
lemma born_sandwich (U : Matrix ι κ ℂ) (A : Matrix κ κ ℂ) (E : Matrix ι ι ℂ) :
    born (U * A * Uᴴ) E = born A (Uᴴ * E * U) := by
  unfold born
  congr 1
  calc
    Matrix.trace (U * A * Uᴴ * E) = Matrix.trace (U * (A * Uᴴ * E)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (A * Uᴴ * E * U) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * (Uᴴ * E * U)) := by simp only [Matrix.mul_assoc]

end Compression
end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM

-- 待原张量 Schur 定理实例化的精确矩阵接口；不假定 Fisher 或风险公式。
structure BlockResolution {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (n : B → ℕ) (w : B → ℝ) where
  embedding : ∀ b, Matrix ι (Fin (n b+1)) ℂ
  isometry : ∀ b, (embedding b)ᴴ * embedding b = 1
  weight_nonneg : ∀ b, 0 ≤ w b
  reference : ρ = ∑ b, w b • (embedding b * state (n b) * (embedding b)ᴴ)
  tangent : ∀ a, D a = ∑ b, w b • (embedding b *
    (if a = 0 then tangentX (n b) (FiniteCopy.Algebra.spinEdge (n b))
      else tangentY (n b) (FiniteCopy.Algebra.spinEdge (n b))) * (embedding b)ᴴ)

lemma born_sum_left {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    (A : B → Matrix ι ι ℂ) (E : Matrix ι ι ℂ) :
    born (∑ b, A b) E = ∑ b, born (A b) E := by
  simp [born, Finset.sum_mul, Matrix.trace_sum]

lemma born_real_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (A E : Matrix ι ι ℂ) : born (a • A) E = a * born A E := by
  simp only [born, Matrix.smul_mul, Matrix.trace_smul]
  change RCLike.re (a • Matrix.trace (A * E)) = _
  rw [RCLike.smul_re]
  rfl

section Resolution
variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
variable (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (n : B → ℕ) (w : B → ℝ)
variable (R : BlockResolution ρ D n w)
include R

lemma resolution_born_reference (E : Matrix ι ι ℂ) :
    born ρ E = ∑ b, w b * born (state (n b)) ((R.embedding b)ᴴ * E * R.embedding b) := by
  conv_lhs => rw [R.reference]
  rw [born_sum_left]
  simp_rw [born_real_smul_left, born_sandwich]

lemma resolution_born_tangent (E : Matrix ι ι ℂ) (a : Fin 2) :
    born (D a) E = ∑ b, w b * born
      (if a = 0 then tangentX (n b) (FiniteCopy.Algebra.spinEdge (n b))
        else tangentY (n b) (FiniteCopy.Algebra.spinEdge (n b)))
      ((R.embedding b)ᴴ * E * R.embedding b) := by
  rw [R.tangent, born_sum_left]
  simp_rw [born_real_smul_left, born_sandwich]

-- 原 Hilbert 空间上的任意密度 POVM 经压缩后精确保留 p 与切向。
theorem resolution_risk_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (M : DensityPOVM ι Ω μ) (u : Ω → Fin 2 → ℝ)
    (hu : MomentUnbiased μ (fun z => born ρ (M.effect z))
      (fun z a => born (D a) (M.effect z)) u) :
    0 < (∑ b, w b * capFisherBound (n b)) ∧
    4*N / (∑ b, w b * capFisherBound (n b)) ≤
      risk μ N (fun z => born ρ (M.effect z)) u := by
  let M' := fun b => M.compress μ (R.embedding b) (R.isometry b)
  have hp : blockProbability n w (fun b => (M' b).effect) =
      (fun z => born ρ (M.effect z)) := by
    funext z
    exact (resolution_born_reference ρ D n w R (M.effect z)).symm
  have hd : blockDerivative n w (fun b => (M' b).effect) =
      (fun z a => born (D a) (M.effect z)) := by
    funext z a
    exact (resolution_born_tangent ρ D n w R (M.effect z) a).symm
  have h := arbitrary_block_density_risk_lower μ n w N R.weight_nonneg M' u
    (by simpa only [hp, hd] using hu)
  simpa only [hp] using h

theorem attainableRisks_lower (N : ℕ) :
    ∀ r ∈ attainableRisks N ρ D, 4*N / (∑ b, w b * capFisherBound (n b)) ≤ r := by
  rintro r ⟨Ω, mΩ, μ, M, u, hu, rfl⟩
  letI : MeasurableSpace Ω := mΩ
  exact (resolution_risk_lower ρ D n w R μ N M u hu).2

theorem optimalRisk_sandwich_of_resolution (N : ℕ) (hi : ℝ)
    (hhi : hi ∈ attainableRisks N ρ D) :
    4*N / (∑ b, w b * capFisherBound (n b)) ≤ optimalRisk N ρ D ∧
      optimalRisk N ρ D ≤ hi :=
  optimalRisk_sandwich N ρ D _ hi (attainableRisks_lower ρ D n w R N) hhi

end Resolution
end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM
section OperatorMeasure
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable (μ : Measure Ω) (M : DensityPOVM ι Ω μ)

-- 逐矩阵元积分，避免任意矩阵范数约定进入测量定义。
def DensityPOVM.operatorMeasure (s : Set Ω) : Matrix ι ι ℂ :=
  Matrix.of (fun i j => ∫ z in s, M.effect z i j ∂μ)

theorem DensityPOVM.operatorMeasure_positive (s : Set Ω) :
    (M.operatorMeasure μ s).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    change star (∫ z in s, M.effect z j i ∂μ) = ∫ z in s, M.effect z i j ∂μ
    calc
      star (∫ z in s, M.effect z j i ∂μ) = ∫ z in s, star (M.effect z j i) ∂μ :=
        (integral_conj (f := fun z => M.effect z j i) (μ := μ.restrict s)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact congrFun (congrFun (M.positive z).isHermitian i) j
  · intro x
    have hint (i j : ι) : Integrable (fun z => star (x i) * (M.effect z i j * x j)) (μ.restrict s) :=
      ((M.integrable i j).integrableOn.mul_const _).const_mul _
    have heq : star x ⬝ᵥ (M.operatorMeasure μ s *ᵥ x) =
        ∫ z in s, star x ⬝ᵥ (M.effect z *ᵥ x) ∂μ := by
      simp only [DensityPOVM.operatorMeasure, dotProduct, mulVec, Matrix.of_apply,
        Pi.star_apply, Finset.mul_sum]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        · simp_rw [integral_const_mul, integral_mul_const]
        · intro j hj; exact hint i j
      · intro i hi; exact integrable_finsetSum _ (fun j _ => hint i j)
    rw [heq]
    exact integral_nonneg (fun z => (M.positive z).dotProduct_mulVec_nonneg x)

theorem DensityPOVM.operatorMeasure_empty : M.operatorMeasure μ ∅ = 0 := by
  ext i j
  simp [DensityPOVM.operatorMeasure]

theorem DensityPOVM.operatorMeasure_univ : M.operatorMeasure μ Set.univ = 1 := by
  ext i j
  simp only [DensityPOVM.operatorMeasure, Matrix.of_apply, Measure.restrict_univ]
  exact M.complete i j

theorem DensityPOVM.operatorMeasure_countably_additive (s : ℕ → Set Ω)
    (hs : ∀ k, MeasurableSet (s k)) (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum (fun k => M.operatorMeasure μ (s k)) (M.operatorMeasure μ (⋃ k, s k)) := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  exact hasSum_integral_iUnion hs hdisj (M.integrable i j).integrableOn
end OperatorMeasure
end FiniteCopy.Risk

namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM

-- 终端接线定理：精确模型分解、真实可达成员和真实逐 spin 渐近均显式列出。
-- 这些参数必须由上游实例化后，才得到原 qubit 模型的无条件结论。
theorem optimalRisk_first_correction_of_resolved_model
    (ι B : ℕ → Type) [∀ N, Fintype (ι N)] [∀ N, DecidableEq (ι N)]
    [∀ N, Fintype (B N)]
    (ρ : ∀ N, Matrix (ι N) (ι N) ℂ)
    (D : ∀ N, Fin 2 → Matrix (ι N) (ι N) ℂ)
    (n : ∀ N, B N → ℕ) (w : ∀ N, B N → ℝ)
    (R : ∀ N, BlockResolution (ρ N) (D N) (n N) (w N))
    (hcap : ∀ N, (∑ b, w N b * capFisherBound (n N b)) =
      FiniteCopy.Schur.schurAverage capFisherBound N)
    (v : ℕ → ℝ)
    (hv : (fun n => v n - (n : ℝ)/4) =o[atTop] (fun n : ℕ => (n : ℝ)))
    (hGaussian : ∀ N, 0 < N →
      4*N / (2*N - 4*FiniteCopy.Schur.schurAverage v N) ∈ attainableRisks N (ρ N) (D N)) :
    Tendsto (fun N : ℕ => Real.sqrt N * (optimalRisk N (ρ N) (D N) - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply risk_first_correction_of_sandwich
    (fun N => optimalRisk N (ρ N) (D N))
    (fun N => 4*N / FiniteCopy.Schur.schurAverage capFisherBound N)
    (fun N => 4*N / (2*N - 4*FiniteCopy.Schur.schurAverage v N))
    (Real.sqrt (8/Real.pi))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h := (optimalRisk_sandwich_of_resolution (ρ N) (D N) (n N) (w N) (R N)
      N _ (hGaussian N (by omega))).1
    rwa [hcap N] at h
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (optimalRisk_sandwich_of_resolution (ρ N) (D N) (n N) (w N) (R N)
      N _ (hGaussian N (by omega))).2
  · exact cap_risk_first_correction
  · exact FiniteCopy.Schur.schurRisk_scaled_limit hv

end FiniteCopy.Risk


namespace FiniteCopy.Risk
open CopyQuantumMetrology FiniteCopy.POVM
section Unitary
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (U : Matrix ι κ ℂ) (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1)
include hright

lemma sandwich_inverse (A : Matrix ι ι ℂ) : U * (Uᴴ * A * U) * Uᴴ = A := by
  calc
    U * (Uᴴ * A * U) * Uᴴ = (U * Uᴴ) * A * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hright, Matrix.one_mul, Matrix.mul_one]

lemma born_unitary_conjugation (A E : Matrix ι ι ℂ) :
    born (Uᴴ * A * U) (Uᴴ * E * U) = born A E := by
  rw [← born_sandwich, sandwich_inverse U hright]

-- 真实可达风险集合在酉换基下不变。
include hleft
theorem attainableRisks_conjugation_subset (N : ℕ) (ρ : Matrix ι ι ℂ)
    (D : Fin 2 → Matrix ι ι ℂ) :
    attainableRisks N ρ D ⊆
      attainableRisks N (Uᴴ * ρ * U) (fun a => Uᴴ * D a * U) := by
  rintro r ⟨Ω, mΩ, μ, M, u, hu, hr⟩
  letI : MeasurableSpace Ω := mΩ
  let M' := M.compress μ U hleft
  refine ⟨Ω, mΩ, μ, M', u, ?_, ?_⟩
  · simpa only [M', DensityPOVM.compress, born_unitary_conjugation U hright] using hu
  · simpa only [M', DensityPOVM.compress, born_unitary_conjugation U hright] using hr

theorem attainableRisks_unitary_invariant (N : ℕ) (ρ : Matrix ι ι ℂ)
    (D : Fin 2 → Matrix ι ι ℂ) :
    attainableRisks N (Uᴴ * ρ * U) (fun a => Uᴴ * D a * U) = attainableRisks N ρ D := by
  apply Set.Subset.antisymm
  · have h := attainableRisks_conjugation_subset Uᴴ
      (by simpa using hright) (by simpa using hleft) N (Uᴴ * ρ * U) (fun a => Uᴴ * D a * U)
    simpa only [Matrix.conjTranspose_conjTranspose, sandwich_inverse U hright] using h
  · exact attainableRisks_conjugation_subset U hleft hright N ρ D

theorem optimalRisk_unitary_invariant (N : ℕ) (ρ : Matrix ι ι ℂ)
    (D : Fin 2 → Matrix ι ι ℂ) :
    optimalRisk N (Uᴴ * ρ * U) (fun a => Uᴴ * D a * U) = optimalRisk N ρ D := by
  unfold optimalRisk
  rw [attainableRisks_unitary_invariant U hleft hright]

end Unitary
end FiniteCopy.Risk

