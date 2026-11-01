import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

open scoped BigOperators ComplexOrder
open MeasureTheory Matrix Complex

noncomputable section
namespace CopyQuantumMetrology

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable {L : ℕ} [NeZero L]

-- 有限相位来自单位圆上的标准加性特征。
def phase (k i : ZMod L) : ℂ := ZMod.stdAddChar (i * k)

lemma phase_conj (k i : ZMod L) : star (phase k i) = phase k (-i) := by
  simp only [phase, ZMod.stdAddChar_apply, neg_mul, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

lemma phase_product (k i j : ZMod L) :
    phase k i * star (phase k j) = phase k (i - j) := by
  rw [phase_conj]
  simp only [phase, ← AddChar.map_add_eq_mul]
  congr 1
  ring

lemma phase_sum (i : ZMod L) :
    ∑ k : ZMod L, phase k i = if i = 0 then (L : ℂ) else 0 := by
  classical
  by_cases hi : i = 0
  · simp [hi, phase, ZMod.card L]
  · rw [if_neg hi]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L hi)

lemma phase_orthogonality (i j : ZMod L) :
    ∑ k : ZMod L, phase k i * star (phase k j) =
      if i = j then (L : ℂ) else 0 := by
  simp_rw [phase_product]
  simpa only [sub_eq_zero] using phase_sum (i - j)

-- 种子可以按任意测度空间连续编号。
def rotatedSeed (v : ι → ℂ) (e : ι → ZMod L) (k : ZMod L) : ι → ℂ :=
  fun i => phase k (e i) * v i

def effect (v : ι → ℂ) (e : ι → ZMod L) (k : ZMod L) : Matrix ι ι ℂ :=
  (L : ℝ)⁻¹ • Matrix.vecMulVec (rotatedSeed v e k) (star (rotatedSeed v e k))

lemma effect_positive (v : ι → ℂ) (e : ι → ZMod L) (k : ZMod L) :
    (effect v e k).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity : 0 ≤ (L : ℝ)⁻¹)

lemma phase_average_effect (v : ι → ℂ) (e : ι → ZMod L)
    (he : Function.Injective e) (i j : ι) :
    (∑ k : ZMod L, effect v e k i j) =
      if i = j then v i * star (v i) else 0 := by
  classical
  have hf : (∑ k : ZMod L, effect v e k i j) =
      ∑ k : ZMod L, ((L : ℝ)⁻¹ : ℂ) * (v i * star (v j)) *
        (phase k (e i) * star (phase k (e j))) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [effect, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      rotatedSeed, star_mul, RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  rw [hf]
  rw [← Finset.mul_sum, phase_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
    push_cast
    field_simp
  · simp [hij, he.ne hij]

variable [MeasurableSpace X] (μ : Measure X)

-- 逐列的积分归一化直接推出完整性，未把完整性作为前提。
theorem continuous_phase_complete (v : X → ι → ℂ) (e : ι → ZMod L)
    (he : Function.Injective e)
    (hnorm : ∀ i, ∫ t, v t i * star (v t i) ∂μ = 1) :
    (fun i j => ∫ t, ∑ k : ZMod L, effect (v t) e k i j ∂μ) =
      (1 : Matrix ι ι ℂ) := by
  ext i j
  simp_rw [phase_average_effect _ e he]
  by_cases hij : i = j
  · subst j
    simpa using hnorm i
  · simp [hij, Matrix.one_apply]

-- 分别积分各相位的写法，正是连续标签与有限结果标签的混合测量。
theorem continuous_phase_complete_separated (v : X → ι → ℂ) (e : ι → ZMod L)
    (he : Function.Injective e)
    (hnorm : ∀ i, ∫ t, v t i * star (v t i) ∂μ = 1)
    (hint : ∀ k i j, Integrable (fun t => effect (v t) e k i j) μ) :
    (fun i j => ∑ k : ZMod L, ∫ t, effect (v t) e k i j ∂μ) =
      (1 : Matrix ι ι ℂ) := by
  have hc := continuous_phase_complete μ v e he hnorm
  ext i j
  rw [← integral_finsetSum _ (fun k _ => hint k i j)]
  exact congrFun (congrFun hc i) j

-- 标量 Born 规则和未归一化向量的二次型。
def rankOne (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)
def vectorMass (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)
def quadratic (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * A i j * v j

def born (ρ E : Matrix ι ι ℂ) : ℝ := (Matrix.trace (ρ * E)).re

lemma trace_rankOne (v : ι → ℂ) :
    Matrix.trace (rankOne v) = (vectorMass v : ℂ) := by
  simp [rankOne, Matrix.trace_vecMulVec, dotProduct, vectorMass,
    Complex.mul_conj, Complex.star_def]

lemma trace_mul_rankOne (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    Matrix.trace (A * rankOne v) = quadratic A v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, rankOne,
    Matrix.vecMulVec_apply, Pi.star_apply, quadratic]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma vectorMass_nonneg (v : ι → ℂ) : 0 ≤ vectorMass v := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))

lemma born_maximallyMixed_rankOne (d : ℝ) (v : ι → ℂ) :
    born ((d⁻¹ : ℝ) • (1 : Matrix ι ι ℂ)) (rankOne v) = vectorMass v / d := by
  simp only [born, smul_mul, one_mul, Matrix.trace_smul, trace_rankOne]
  change RCLike.re (d⁻¹ • (vectorMass v : ℂ)) = vectorMass v / d
  rw [RCLike.smul_re]
  change d⁻¹ * vectorMass v = vectorMass v / d
  ring

lemma born_tangent_rankOne (d : ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    born ((2 / d : ℝ) • A) (rankOne v) = 2 * (quadratic A v).re / d := by
  simp [born, Matrix.smul_mul, Matrix.trace_smul, trace_mul_rankOne,
    RCLike.real_smul_eq_coe_mul]
  ring

-- 参考态为 I/d、切向为 2A/d 时，score 恰为两倍归一化自旋期望。
theorem rankOne_score (d : ℝ) (hd : d ≠ 0) (A : Matrix ι ι ℂ)
    (v : ι → ℂ) (hv : vectorMass v ≠ 0) :
    born ((2 / d : ℝ) • A) (rankOne v) /
      born ((d⁻¹ : ℝ) • (1 : Matrix ι ι ℂ)) (rankOne v) =
        2 * (quadratic A v).re / vectorMass v := by
  rw [born_tangent_rankOne, born_maximallyMixed_rankOne]
  field_simp

-- 可积性只要求种子的交叉乘积可积；有限相位因子不改变这一性质。
lemma effect_integrable (v : X → ι → ℂ) (e : ι → ZMod L)
    (hc : ∀ i j, Integrable (fun t => v t i * star (v t j)) μ)
    (k : ZMod L) (i j : ι) : Integrable (fun t => effect (v t) e k i j) μ := by
  convert (hc i j).const_mul
    (((L : ℝ)⁻¹ : ℂ) * (phase k (e i) * star (phase k (e j)))) using 1
  ext t
  simp only [effect, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    rotatedSeed, star_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

-- 高斯构造使用实列；这个接口正好接受实积分归一化。
theorem real_continuous_phase_complete (v : X → ι → ℝ) (e : ι → ZMod L)
    (he : Function.Injective e)
    (hnorm : ∀ i, ∫ t, (v t i) ^ 2 ∂μ = 1) :
    (fun i j => ∫ t, ∑ k : ZMod L,
      effect (fun i => (v t i : ℂ)) e k i j ∂μ) = (1 : Matrix ι ι ℂ) := by
  apply continuous_phase_complete μ _ e he
  intro i
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq]
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal, hnorm, Complex.ofReal_one]

-- 完整性固定任何可观测量的平均二次型；以下引理完成该积分步骤。
lemma trace_mul_integrable (M : X → Matrix ι ι ℂ) (A : Matrix ι ι ℂ)
    (hint : ∀ i j, Integrable (fun t => M t i j) μ) :
    Integrable (fun t => Matrix.trace (A * M t)) μ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (hint j i).const_mul (A i j)

lemma integral_trace_mul (M : X → Matrix ι ι ℂ) (A : Matrix ι ι ℂ)
    (hint : ∀ i j, Integrable (fun t => M t i j) μ)
    (hcomplete : ∀ i j, ∫ t, M t i j ∂μ = (1 : Matrix ι ι ℂ) i j) :
    (∫ t, Matrix.trace (A * M t) ∂μ) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [integral_finsetSum]
  · have hi (i : ι) :
        (∫ t, ∑ j, A i j * M t j i ∂μ) = A i i := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul, hcomplete]
        exact congrFun (congrFun (Matrix.mul_one A) i) i
      · intro j hj
        exact (hint j i).const_mul (A i j)
    simp_rw [hi]
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => (hint j i).const_mul (A i j))

lemma integral_quadratic_re (v : X → ι → ℂ) (A : Matrix ι ι ℂ)
    (hint : ∀ i j, Integrable (fun t => rankOne (v t) i j) μ)
    (hcomplete : ∀ i j, ∫ t, rankOne (v t) i j ∂μ = (1 : Matrix ι ι ℂ) i j) :
    (∫ t, (quadratic A (v t)).re ∂μ) = (Matrix.trace A).re := by
  simp_rw [← trace_mul_rankOne]
  have hre := integral_re (trace_mul_integrable μ (fun t => rankOne (v t)) A hint)
  simp only [RCLike.re_eq_complex_re] at hre
  rw [hre, integral_trace_mul μ _ A hint hcomplete]

-- 两个自旋可观测量共享同一个分解，方差没有被分别优化。
def normalizedMoment (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (quadratic A v).re / vectorMass v

def pureVariance (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  normalizedMoment (A * A) v - normalizedMoment A v ^ 2

def fisherTraceDensity (d : ℝ) (A B : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (vectorMass v / d) * ((2 * normalizedMoment A v)^2 + (2 * normalizedMoment B v)^2)

def varianceDensity (d : ℝ) (A B : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (vectorMass v / d) * (pureVariance A v + pureVariance B v)

lemma fisher_variance_pointwise (d : ℝ) (A B : Matrix ι ι ℂ)
    (v : ι → ℂ) (hv : vectorMass v ≠ 0) :
    fisherTraceDensity d A B v + 4 * varianceDensity d A B v =
      (4 / d) * ((quadratic (A*A) v).re + (quadratic (B*B) v).re) := by
  dsimp [fisherTraceDensity, varianceDensity, pureVariance, normalizedMoment]
  field_simp
  <;> ring

-- 这是由实际矩阵完整性推出的 Fisher/共同方差恒等式。
theorem fisher_variance_identity (d : ℝ) (A B : Matrix ι ι ℂ)
    (v : X → ι → ℂ) (hv : ∀ t, vectorMass (v t) ≠ 0)
    (hint : ∀ i j, Integrable (fun t => rankOne (v t) i j) μ)
    (hcomplete : ∀ i j, ∫ t, rankOne (v t) i j ∂μ = (1 : Matrix ι ι ℂ) i j)
    (hf : Integrable (fun t => fisherTraceDensity d A B (v t)) μ)
    (hvar : Integrable (fun t => varianceDensity d A B (v t)) μ) :
    (∫ t, fisherTraceDensity d A B (v t) ∂μ) =
      (4 / d) * ((Matrix.trace (A*A)).re + (Matrix.trace (B*B)).re) -
      4 * ∫ t, varianceDensity d A B (v t) ∂μ := by
  have hq (C : Matrix ι ι ℂ) : Integrable (fun t => (quadratic C (v t)).re) μ := by
    simp_rw [← trace_mul_rankOne]
    exact (trace_mul_integrable μ _ C hint).re
  have hid := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall
    (fun t => fisher_variance_pointwise d A B (v t) (hv t)))
  rw [integral_add hf (hvar.const_mul 4), integral_const_mul,
    integral_const_mul, integral_add (hq (A*A)) (hq (B*B)),
    integral_quadratic_re μ v (A*A) hint hcomplete,
    integral_quadratic_re μ v (B*B) hint hcomplete] at hid
  linarith

section Statistics
variable {Ω κ : Type*} [MeasurableSpace Ω] (ν : Measure Ω)

-- Fisher 的定义以及各向同性情况下的逆 Fisher score 估计器。
def fisherEntry (p : Ω → ℝ) (s : Ω → κ → ℝ) (a b : κ) : ℝ :=
  ∫ z, p z * s z a * s z b ∂ν

def isotropicEstimator (f : ℝ) (s : Ω → κ → ℝ) (z : Ω) (a : κ) : ℝ :=
  s z a / f

-- 对一个参数方向的线性局部密度，积分给出的期望是实际函数。
def localExpectation (p : Ω → ℝ) (s : Ω → κ → ℝ) (f : ℝ)
    (a b : κ) (θ : ℝ) : ℝ :=
  ∫ z, isotropicEstimator f s z a * (p z * (1 + θ * s z b)) ∂ν

lemma localExpectation_formula (p : Ω → ℝ) (s : Ω → κ → ℝ) (f : ℝ)
    (a b : κ)
    (hmean : Integrable (fun z => p z * s z a) ν)
    (hsecond : Integrable (fun z => p z * s z a * s z b) ν) (θ : ℝ) :
    localExpectation ν p s f a b θ =
      (∫ z, p z * s z a ∂ν) / f + θ * fisherEntry ν p s a b / f := by
  have hpoint (z : Ω) :
      isotropicEstimator f s z a * (p z * (1 + θ * s z b)) =
      (p z * s z a) / f + (θ / f) * (p z * s z a * s z b) := by
    dsimp [isotropicEstimator]
    ring
  simp_rw [localExpectation, hpoint]
  rw [integral_add (hmean.div_const f) (hsecond.const_mul (θ / f)),
    integral_div, integral_const_mul]
  dsimp [fisherEntry]
  ring

-- 前提是 score 的零均值和 Fisher 值，不是待证的无偏性。
theorem isotropic_score_locally_unbiased [DecidableEq κ]
    (p : Ω → ℝ) (s : Ω → κ → ℝ) (f : ℝ) (hf : f ≠ 0)
    (hmean : ∀ a, Integrable (fun z => p z * s z a) ν)
    (hsecond : ∀ a b, Integrable (fun z => p z * s z a * s z b) ν)
    (hzero : ∀ a, ∫ z, p z * s z a ∂ν = 0)
    (hfisher : ∀ a b, fisherEntry ν p s a b = if a = b then f else 0)
    (a b : κ) :
    localExpectation ν p s f a b 0 = 0 ∧
    HasDerivAt (localExpectation ν p s f a b) (if a = b then 1 else 0) 0 := by
  have hform (θ : ℝ) : localExpectation ν p s f a b θ =
      θ * (if a = b then 1 else 0) := by
    rw [localExpectation_formula ν p s f a b (hmean a) (hsecond a b), hzero,
      hfisher]
    split_ifs <;> simp [hf]
  constructor
  · rw [hform]; simp
  · have heq : localExpectation ν p s f a b =
        fun θ => θ * (if a = b then 1 else 0) := funext hform
    rw [heq]
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (if a = b then (1 : ℝ) else 0)

lemma isotropic_score_covariance [DecidableEq κ]
    (p : Ω → ℝ) (s : Ω → κ → ℝ) (f : ℝ) (hf : f ≠ 0)
    (hfisher : ∀ a b, fisherEntry ν p s a b = if a = b then f else 0)
    (a b : κ) :
    (∫ z, p z * isotropicEstimator f s z a * isotropicEstimator f s z b ∂ν) =
      if a = b then f⁻¹ else 0 := by
  have hpoint (z : Ω) :
      p z * isotropicEstimator f s z a * isotropicEstimator f s z b =
        (f * f)⁻¹ * (p z * s z a * s z b) := by
    dsimp [isotropicEstimator]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  change (f * f)⁻¹ * fisherEntry ν p s a b = _
  rw [hfisher]
  split_ifs <;> simp [hf]

end Statistics
end CopyQuantumMetrology






