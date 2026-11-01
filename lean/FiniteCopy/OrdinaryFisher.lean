import FiniteCopy.ModelFisher
import FiniteCopy.OrdinaryRisk

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.MainTheorem

-- 普通可数可加矩阵值 POVM 的 RN Fisher 值；每个普通 POVM 的表示存在已另证。
def ordinaryFisherValues {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (F : Set Ω → Matrix ι ι ℂ),
    @IsOrdinaryPOVM ι Ω _ _ mΩ F ∧ ∃ (μ : @Measure Ω mΩ)
      (P : @DensityPOVM ι Ω _ _ mΩ μ),
      (∀ A, @MeasurableSet Ω mΩ A → P.operatorMeasure μ A = F A) ∧
      r = ∫ z, modelFisherDensity ρ D (P.effect z) ∂μ}

theorem ordinaryFisherValues_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) :
    ordinaryFisherValues ρ D = modelFisherValues ρ D := by
  ext r
  constructor
  · rintro ⟨Ω, mΩ, F, hF, μ, P, hrepr, hr⟩
    exact ⟨Ω, mΩ, μ, P, hr⟩
  · rintro ⟨Ω, mΩ, μ, P, hr⟩
    letI : MeasurableSpace Ω := mΩ
    refine ⟨Ω, mΩ, P.operatorMeasure μ, ?_, μ, P, ?_, hr⟩
    · exact ⟨P.operatorMeasure_empty μ, fun A _ => P.operatorMeasure_positive μ A,
        P.operatorMeasure_univ μ, P.operatorMeasure_countably_additive μ⟩
    · intro A hA
      rfl

def sectorTangent (n : ℕ) (a : Fin 2) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  if a=0 then tangentX n (Algebra.spinEdge n) else tangentY n (Algebra.spinEdge n)

theorem sectorFisherValues_eq_model (n : ℕ) :
    fisherValues n = modelFisherValues (state n) (sectorTangent n) := by
  have hd (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
      fisherDensity n (Algebra.spinEdge n) E = modelFisherDensity (state n) (sectorTangent n) E := by
    simp [fisherDensity, modelFisherDensity, sectorTangent]
  simp only [fisherValues, modelFisherValues, hd]

theorem ordinary_sectorFisherValues_eq (n : ℕ) :
    ordinaryFisherValues (state n) (sectorTangent n) = fisherValues n := by
  rw [ordinaryFisherValues_eq, sectorFisherValues_eq_model]

end FiniteCopy.Optimization
