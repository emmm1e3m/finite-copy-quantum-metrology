import FiniteCopy.POVMDensity
import FiniteCopy.BornExpectation

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.MainTheorem
open CopyQuantumMetrology FiniteCopy.Risk

-- 普通矩阵值POVM的标准集合条件，不先假定密度存在。
structure IsOrdinaryPOVM {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (F : Set Ω → Matrix ι ι ℂ) : Prop where
  empty : F ∅ = 0
  positive : ∀ A, MeasurableSet A → (F A).PosSemidef
  complete : F Set.univ = 1
  additive : ∀ A : ℕ → Set Ω, (∀ k, MeasurableSet (A k)) →
    Pairwise (fun i j => Disjoint (A i) (A j)) → HasSum (fun k => F (A k)) (F (⋃ k, A k))

theorem ordinaryPOVM_has_density {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (F : Set Ω → Matrix ι ι ℂ) (hF : IsOrdinaryPOVM F) :
    ∃ (μ : Measure Ω), IsFiniteMeasure μ ∧ ∃ P : DensityPOVM ι Ω μ,
      ∀ A, MeasurableSet A → P.operatorMeasure μ A = F A :=
  exists_density_of_operator_povm F hF.empty hF.positive hF.complete hF.additive

-- 表示同时恢复每一个参考态或真实参数态的全部事件Born概率。
theorem represented_born_setIntegral {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (P : DensityPOVM ι Ω μ)
    (F : Set Ω → Matrix ι ι ℂ)
    (hrepr : ∀ A, MeasurableSet A → P.operatorMeasure μ A = F A)
    (ρ : Matrix ι ι ℂ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ z in A, born ρ (P.effect z) ∂μ) = born ρ (F A) := by
  have h := TensorModel.integral_born (μ.restrict A) ρ P.effect
    (fun i j => (P.integrable i j).integrableOn)
  change (∫ z in A, born ρ (P.effect z) ∂μ) = born ρ (P.operatorMeasure μ A) at h
  rwa [hrepr A hA] at h

-- 普通POVM及其RN统计表示的真实风险集合。
def ordinaryAttainableRisks (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Set Ω → Matrix ι ι ℂ),
    @IsOrdinaryPOVM ι Ω _ _ mΩ F ∧ ∃ (μ : @Measure Ω mΩ)
      (P : @DensityPOVM ι Ω _ _ mΩ μ) (u : Ω → Fin 2 → ℝ),
      (∀ A, @MeasurableSet Ω mΩ A → P.operatorMeasure μ A = F A) ∧
      @MomentUnbiased Ω mΩ μ (fun z => born ρ (P.effect z))
        (fun z a => born (D a) (P.effect z)) u ∧
      r = @risk Ω mΩ μ N (fun z => born ρ (P.effect z)) u}

-- 每一个普通POVM都有表示，反向每个密度确实给普通POVM；优化集合完全相同。
theorem ordinaryAttainableRisks_eq (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) :
    ordinaryAttainableRisks N ρ D = attainableRisks N ρ D := by
  ext r
  constructor
  · rintro ⟨Ω, mΩ, F, hF, μ, P, u, hrepr, hu, hr⟩
    exact ⟨Ω, mΩ, μ, P, u, hu, hr⟩
  · rintro ⟨Ω, mΩ, μ, P, u, hu, hr⟩
    letI : MeasurableSpace Ω := mΩ
    refine ⟨Ω, mΩ, P.operatorMeasure μ, ?_, μ, P, u, ?_, hu, hr⟩
    · exact ⟨P.operatorMeasure_empty μ, fun A _ => P.operatorMeasure_positive μ A,
        P.operatorMeasure_univ μ, P.operatorMeasure_countably_additive μ⟩
    · intro A hA; rfl

theorem optimalRisk_eq_ordinary_inf (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) :
    optimalRisk N ρ D = sInf (ordinaryAttainableRisks N ρ D) := by
  rw [ordinaryAttainableRisks_eq]
  rfl

end FiniteCopy.MainTheorem
