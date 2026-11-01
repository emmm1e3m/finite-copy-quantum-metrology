import FiniteCopy.GaussianAsymptotic
import FiniteCopy.StrictRisk
import FiniteCopy.OrdinaryRisk
import FiniteCopy.Resolution
import FiniteCopy.PathSchur
import FiniteCopy.GaussianLift
import FiniteCopy.ExpectationIntegrability

open scoped BigOperators Topology
open MeasureTheory Matrix Filter
noncomputable section
namespace FiniteCopy.MainTheorem
open CopyQuantumMetrology TensorModel SpinPaths
open FiniteCopy.Risk FiniteCopy.GaussianLift FiniteCopy.EndpointCounting

-- 原N-qubit模型上的真实全测量局部无偏风险下确界。
def C (N : ℕ) : ℝ := optimalRisk N (rhoTensor N 0 0) (tangentAxes N)

def topPath : (N : ℕ) → B N
  | 0 => PUnit.unit
  | N+1 => Sum.inl (topPath N)

@[simp] theorem spin_topPath (N : ℕ) : spin N (topPath N) = N := by
  induction N with
  | zero => rfl
  | succ N ih => simpa only [topPath, spin_up, ih]

lemma actual_weight_pos (N : ℕ) (b : B N) : 0 < weight N b := by
  unfold weight
  positivity

lemma actual_cap_average (N : ℕ) :
    (∑ b : B N, weight N b * capFisherBound (spin N b)) =
      Schur.schurAverage capFisherBound N :=
  path_schur_average N capFisherBound

def gaussianWidth (N : ℕ) (b : B N) : ℝ := epsilon (spinJ (spin N b))

lemma gaussianWidth_pos (N : ℕ) (b : B N) : 0 < gaussianWidth N b :=
  epsilon_pos (spinJ_pos _).le

lemma phaseCount_sufficient (N : ℕ) (b : B N) : spin N b+1 ≤ N+3 := by
  have h := path_spin_le N b
  omega

lemma actual_familyFisher (N : ℕ) :
    familyFisher (spin N) (weight N) (gaussianWidth N) = globalGaussianFisher N := by
  simpa only [familyFisher, weight, gaussianWidth, logarithmicFisher,
    globalGaussianFisher, Schur.schurAverage] using path_schur_average N logarithmicFisher

local instance (N : ℕ) : MeasurableSpace (B N) := ⊤
local instance (N : ℕ) : MeasurableSingletonClass (B N) := ⟨fun _ => trivial⟩
local instance (N : ℕ) : MeasurableSpace (ZMod (N+3)) := ⊤
local instance (N : ℕ) : MeasurableSingletonClass (ZMod (N+3)) := ⟨fun _ => trivial⟩

abbrev Outcome (N : ℕ) := B N × (ℝ × ZMod (N+3))
abbrev outcomeMeasure (N : ℕ) : Measure (Outcome N) := familyMeasure (B := B N) (L := N+3)

-- 全部矩阵效果由真实CG嵌入抬升，结果包括路径、连续Gaussian标签和有限相位。
def gaussianMeasurement (N : ℕ) : DensityPOVM (Bits N) (Outcome N) (outcomeMeasure N) :=
  gaussianFamilyPOVM (spin N) (weight N) (gaussianWidth N) (rhoTensor N 0 0) (tangentAxes N)
    (blockResolution N) (gaussianWidth_pos N) (phaseCount_sufficient N) (U_complete N)

def gaussianEstimator (N : ℕ) : Outcome N → Fin 2 → ℝ :=
  familyEstimator (spin N) (weight N) (gaussianWidth N)

theorem gaussianMeasurement_isPOVM (N : ℕ) :
    IsOrdinaryPOVM ((gaussianMeasurement N).operatorMeasure (outcomeMeasure N)) :=
  ⟨(gaussianMeasurement N).operatorMeasure_empty _,
    fun A _ => (gaussianMeasurement N).operatorMeasure_positive _ A,
    (gaussianMeasurement N).operatorMeasure_univ _,
    (gaussianMeasurement N).operatorMeasure_countably_additive _⟩

def gaussianRisk (N : ℕ) : ℝ :=
  risk (outcomeMeasure N) N (fun z => born (rhoTensor N 0 0) ((gaussianMeasurement N).effect z))
    (gaussianEstimator N)

lemma gaussian_born_probability (N : ℕ) :
    (fun z => born (rhoTensor N 0 0) ((gaussianMeasurement N).effect z)) =
      familyProbability (L := N+3) (spin N) (weight N) (gaussianWidth N) :=
  funext (gaussianFamily_born_reference (spin N) (weight N) (gaussianWidth N)
    (rhoTensor N 0 0) (tangentAxes N) (blockResolution N) (gaussianWidth_pos N)
    (phaseCount_sufficient N) (U_orthogonal N) (U_complete N))

lemma gaussian_born_tangent (N : ℕ) :
    (fun z a => born (tangentAxes N a) ((gaussianMeasurement N).effect z)) =
      familyTangent (L := N+3) (spin N) (weight N) (gaussianWidth N) :=
  funext fun z => funext (gaussianFamily_born_tangent (spin N) (weight N) (gaussianWidth N)
    (rhoTensor N 0 0) (tangentAxes N) (blockResolution N) (gaussianWidth_pos N)
    (phaseCount_sufficient N) (U_orthogonal N) (U_complete N) z)

theorem gaussian_moment_unbiased (N : ℕ) (hN : 0 < N) :
    MomentUnbiased (outcomeMeasure N)
      (fun z => born (rhoTensor N 0 0) ((gaussianMeasurement N).effect z))
      (fun z a => born (tangentAxes N a) ((gaussianMeasurement N).effect z))
      (gaussianEstimator N) := by
  rw [gaussian_born_probability, gaussian_born_tangent]
  exact familyMomentUnbiased (spin N) (weight N) (gaussianWidth N) (gaussianWidth_pos N)
    (by omega : 3 ≤ N+3) (by rw [actual_familyFisher]; exact ne_of_gt (globalGaussianFisher_pos N hN))

theorem gaussianRisk_eq (N : ℕ) (hN : 0 < N) : gaussianRisk N = 2*N/globalGaussianFisher N := by
  unfold gaussianRisk
  rw [gaussian_born_probability]
  have h := family_risk (L := N+3) (spin N) (weight N) (gaussianWidth N) N
    (gaussianWidth_pos N) (by omega : 3 ≤ N+3)
    (by rw [actual_familyFisher]; exact ne_of_gt (globalGaussianFisher_pos N hN))
  simpa only [gaussianEstimator, actual_familyFisher] using h

theorem gaussian_risk_member (N : ℕ) (hN : 0 < N) :
    2*N/globalGaussianFisher N ∈ attainableRisks N (rhoTensor N 0 0) (tangentAxes N) := by
  refine ⟨Outcome N, inferInstance, outcomeMeasure N, gaussianMeasurement N, gaussianEstimator N,
    gaussian_moment_unbiased N hN, ?_⟩
  exact (gaussianRisk_eq N hN).symm

-- 局部矩条件在原始张量模型上推出真实期望偏导，不使用仿射替代模型。
def rhoAxis (N : ℕ) (b : Fin 2) (θ : ℝ) : NMatrix N :=
  if b=0 then rhoTensor N θ 0 else rhoTensor N 0 θ

structure TensorLocallyUnbiased {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (M : DensityPOVM (Bits N) Ω μ) (u : Ω → Fin 2 → ℝ) : Prop where
  mean_integrable : ∀ a, Integrable (fun z => born (rhoTensor N 0 0) (M.effect z) * u z a) μ
  second_integrable : ∀ a, Integrable (fun z => born (rhoTensor N 0 0) (M.effect z) * (u z a)^2) μ
  mean_zero : ∀ a, ∫ z, born (rhoTensor N 0 0) (M.effect z) * u z a ∂μ = 0
  derivative : ∀ a b, HasDerivAt
    (fun θ => ∫ z, u z a * born (rhoAxis N b θ) (M.effect z) ∂μ)
    (if a=b then 1 else 0) 0

theorem moment_unbiased_true_tensor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (M : DensityPOVM (Bits N) Ω μ) (u : Ω → Fin 2 → ℝ)
    (hu : MomentUnbiased μ (fun z => born (rhoTensor N 0 0) (M.effect z))
      (fun z a => born (tangentAxes N a) (M.effect z)) u) (a b : Fin 2) :
    (∫ z, born (rhoTensor N 0 0) (M.effect z) * u z a ∂μ) = 0 ∧
      HasDerivAt (fun θ => ∫ z, u z a * born (rhoAxis N b θ) (M.effect z) ∂μ)
        (if a=b then 1 else 0) 0 := by
  refine ⟨hu.mean_zero a, ?_⟩
  fin_cases b
  · have h := rhoTensor_expectation_hasDerivAt_x_of_firstMoment μ N M.effect
      M.positive M.integrable (fun z => u z a) (hu.mean_integrable a)
    have ht := hu.tangent_identity a 0
    simp only [tangentAxes, collectiveAxes, ite_true] at ht
    rw [ht] at h
    simpa [rhoAxis] using h
  · have h := rhoTensor_expectation_hasDerivAt_y_of_firstMoment μ N M.effect
      M.positive M.integrable (fun z => u z a) (hu.mean_integrable a)
    have ht := hu.tangent_identity a 1
    simp only [tangentAxes, collectiveAxes, show (1 : Fin 2) ≠ 0 by decide, ite_false] at ht
    rw [ht] at h
    simpa [rhoAxis] using h

-- 反向亦成立：真实期望偏导恢复切向矩，交叉矩可积性由满秩参考态推出。
theorem tensor_locally_unbiased_iff_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (M : DensityPOVM (Bits N) Ω μ) (u : Ω → Fin 2 → ℝ) :
    TensorLocallyUnbiased μ N M u ↔
      MomentUnbiased μ (fun z => born (rhoTensor N 0 0) (M.effect z))
        (fun z a => born (tangentAxes N a) (M.effect z)) u := by
  constructor
  · intro hu
    refine ⟨hu.mean_integrable, hu.second_integrable, ?_, hu.mean_zero, ?_⟩
    · intro a b
      have hi (i j : Bits N) : Integrable (fun z => u z a • M.effect z i j) μ := by
        apply weighted_entries_integrable μ M.effect M.positive M.integrable ((2 : ℝ)^N)
          (by positivity) (fun z => u z a)
        simpa only [born_rhoTensor_zero, FiniteCopy.POVM.traceReal] using hu.mean_integrable a
      have h := (trace_mul_integrable μ (fun z => u z a • M.effect z) (tangentAxes N b) hi).re
      change Integrable (fun z => born (tangentAxes N b) (u z a • M.effect z)) μ at h
      simpa only [born_smul_right] using h
    · intro a b
      fin_cases b
      · have h := rhoTensor_expectation_hasDerivAt_x_of_firstMoment μ N M.effect
          M.positive M.integrable (fun z => u z a) (hu.mean_integrable a)
        have hh := hu.derivative a 0
        simp only [rhoAxis, ite_true] at hh
        simpa [tangentAxes, collectiveAxes] using h.unique hh
      · have h := rhoTensor_expectation_hasDerivAt_y_of_firstMoment μ N M.effect
          M.positive M.integrable (fun z => u z a) (hu.mean_integrable a)
        have hh := hu.derivative a 1
        simp only [rhoAxis, show (1 : Fin 2) ≠ 0 by decide, ite_false] at hh
        simpa [tangentAxes, collectiveAxes] using h.unique hh
  · intro hu
    exact ⟨hu.mean_integrable, hu.second_integrable, hu.mean_zero,
      fun a b => (moment_unbiased_true_tensor μ N M u hu a b).2⟩

-- 普通POVM与原张量模型的真实期望导数定义的风险集合。
def tensorAttainableRisks (N : ℕ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Set Ω → NMatrix N),
    @IsOrdinaryPOVM (Bits N) Ω _ _ mΩ F ∧ ∃ (μ : @Measure Ω mΩ)
      (P : @DensityPOVM (Bits N) Ω _ _ mΩ μ) (u : Ω → Fin 2 → ℝ),
      (∀ A, @MeasurableSet Ω mΩ A → P.operatorMeasure μ A = F A) ∧
      @TensorLocallyUnbiased Ω mΩ μ N P u ∧
      r = @risk Ω mΩ μ N (fun z => born (rhoTensor N 0 0) (P.effect z)) u}

theorem tensorAttainableRisks_eq (N : ℕ) :
    tensorAttainableRisks N = attainableRisks N (rhoTensor N 0 0) (tangentAxes N) := by
  ext r
  constructor
  · rintro ⟨Ω, mΩ, F, hF, μ, P, u, hrepr, hu, hr⟩
    letI : MeasurableSpace Ω := mΩ
    exact ⟨Ω, mΩ, μ, P, u, (tensor_locally_unbiased_iff_moments μ N P u).mp hu, hr⟩
  · rintro ⟨Ω, mΩ, μ, P, u, hu, hr⟩
    letI : MeasurableSpace Ω := mΩ
    refine ⟨Ω, mΩ, P.operatorMeasure μ, ?_, μ, P, u, ?_,
      (tensor_locally_unbiased_iff_moments μ N P u).mpr hu, hr⟩
    · exact ⟨P.operatorMeasure_empty μ, fun A _ => P.operatorMeasure_positive μ A,
        P.operatorMeasure_univ μ, P.operatorMeasure_countably_additive μ⟩
    · intro A hA; rfl

theorem C_eq_true_unbiased_inf (N : ℕ) : C N = sInf (tensorAttainableRisks N) := by
  rw [tensorAttainableRisks_eq]
  rfl

theorem finite_N_gaussian_locally_unbiased (N : ℕ) (hN : 0 < N) (a b : Fin 2) :
    (∫ z, born (rhoTensor N 0 0) ((gaussianMeasurement N).effect z) * gaussianEstimator N z a
      ∂outcomeMeasure N) = 0 ∧
    HasDerivAt (fun θ => ∫ z, gaussianEstimator N z a *
      born (rhoAxis N b θ) ((gaussianMeasurement N).effect z) ∂outcomeMeasure N)
      (if a=b then 1 else 0) 0 :=
  moment_unbiased_true_tensor (outcomeMeasure N) N (gaussianMeasurement N) (gaussianEstimator N)
    (gaussian_moment_unbiased N hN) a b

theorem C_finite_sandwich (N : ℕ) (hN : 0 < N) :
    4*N / Schur.schurAverage capFisherBound N ≤ C N ∧ C N ≤ 2*N/globalGaussianFisher N := by
  have h := optimalRisk_sandwich_of_resolution (rhoTensor N 0 0) (tangentAxes N)
    (spin N) (weight N) (blockResolution N) N _ (gaussian_risk_member N hN)
  simpa only [actual_cap_average, C] using h

-- 无研究结论假设的原模型主定理。
theorem optimal_risk_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (C N - 2)) atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply risk_first_correction_of_sandwich C
    (fun N => 4*N/Schur.schurAverage capFisherBound N)
    (fun N => 2*N/globalGaussianFisher N) (Real.sqrt (8/Real.pi))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (C_finite_sandwich N (by omega)).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (C_finite_sandwich N (by omega)).2
  · exact cap_risk_first_correction
  · exact gaussianFisher_risk_first_correction

theorem gaussian_risk_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (gaussianRisk N - 2))
      atTop (𝓝 (Real.sqrt (8/Real.pi))) := by
  apply gaussianFisher_risk_first_correction.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [gaussianRisk_eq N (by omega)]

theorem C_eq_ordinary_povm_inf (N : ℕ) :
    C N = sInf (ordinaryAttainableRisks N (rhoTensor N 0 0) (tangentAxes N)) :=
  optimalRisk_eq_ordinary_inf N (rhoTensor N 0 0) (tangentAxes N)

-- 原模型的严格有限N截顶界：正缺口保留到真实风险下确界。
theorem strict_cap_gap (N : ℕ) (hN : 10 ≤ N) :
    4*N/Schur.schurAverage capFisherBound N < C N := by
  have h := optimalRisk_strict_cap_of_resolution (rhoTensor N 0 0) (tangentAxes N)
    (spin N) (weight N) (blockResolution N) (topPath N) (by simpa using hN)
    (actual_weight_pos N _) N (by omega) ⟨_, gaussian_risk_member N (by omega)⟩
  simpa only [actual_cap_average, C] using h

theorem cap_gap_smaller_than_first_correction :
    Tendsto (fun N : ℕ => Real.sqrt N * (C N - 4*N/Schur.schurAverage capFisherBound N))
      atTop (𝓝 (0 : ℝ)) := by
  have h := optimal_risk_first_correction.sub cap_risk_first_correction
  convert h using 1
  · ext N; ring
  · ring

theorem cap_gap_littleO :
    (fun N => C N - 4*N/Schur.schurAverage capFisherBound N) =o[atTop]
      (fun N : ℕ => 1 / Real.sqrt N) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · convert cap_gap_smaller_than_first_correction using 1
    ext N
    simp only [one_div, div_inv_eq_mul, mul_comm]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    intro hz
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    have hh : (1 : ℝ)/Real.sqrt N ≠ 0 := ne_of_gt (one_div_pos.mpr hs)
    exact False.elim (hh hz)

end FiniteCopy.MainTheorem

