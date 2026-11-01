import FiniteCopy.GaussianFisherMember
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

theorem density_fisher_le_sector {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (M : DensityPOVM (Fin (n+1)) Ω μ) :
    (∫ z, fisherDensity n (Algebra.spinEdge n) (M.effect z) ∂μ) ≤ sectorFisher n := by
  apply le_csSup (fisherValues_bddAbove n)
  exact ⟨Ω, inferInstance, μ, M, rfl⟩

section Block
variable {B Ω : Type} [Fintype B] [MeasurableSpace Ω]
variable (μ : Measure Ω) (n : B → ℕ) (w : B → ℝ)

theorem exact_block_fisher_bound (hw : ∀ b, 0 ≤ w b)
    (M : ∀ b, DensityPOVM (Fin (n b+1)) Ω μ) :
    (∫ z, blockFisherDensity n w (fun b => (M b).effect) z ∂μ) ≤
      ∑ b, w b * sectorFisher (n b) := by
  let E := fun b => (M b).effect
  have hlocal (b : B) := canonical_arbitrary_density_fisher_bound μ (n b) (E b)
    (M b).positive (M b).integrable (M b).complete
  have hf := (block_fisher_bound μ n w E hw (fun b => (M b).positive)
    (fun b => (M b).integrable) (fun b => (M b).complete)).1
  have hg : Integrable (fun z => ∑ b, w b *
      fisherDensity (n b) (Algebra.spinEdge (n b)) (E b z)) μ :=
    integrable_finsetSum _ (fun b _ => (hlocal b).1.const_mul _)
  calc
    _ ≤ ∫ z, ∑ b, w b * fisherDensity (n b) (Algebra.spinEdge (n b)) (E b z) ∂μ :=
      integral_mono hf hg (blockFisherDensity_bound n w E hw (fun b => (M b).positive))
    _ = ∑ b, w b * ∫ z, fisherDensity (n b) (Algebra.spinEdge (n b)) (E b z) ∂μ := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro b hb
        exact (hlocal b).1.const_mul _
    _ ≤ _ := Finset.sum_le_sum fun b hb =>
      mul_le_mul_of_nonneg_left (density_fisher_le_sector μ (n b) (M b)) (hw b)

theorem exact_block_risk_lower (N : ℕ) (hw : ∀ b, 0 ≤ w b)
    (M : ∀ b, DensityPOVM (Fin (n b+1)) Ω μ) (u : Ω → Fin 2 → ℝ)
    (hu : MomentUnbiased μ (blockProbability n w (fun b => (M b).effect))
      (blockDerivative n w (fun b => (M b).effect)) u) :
    0 < (∑ b, w b * sectorFisher (n b)) ∧
    4*N / (∑ b, w b * sectorFisher (n b)) ≤
      risk μ N (blockProbability n w (fun b => (M b).effect)) u := by
  let E := fun b => (M b).effect
  have hF := (block_fisher_bound μ n w E hw (fun b => (M b).positive)
    (fun b => (M b).integrable) (fun b => (M b).complete)).1
  apply risk_lower_of_fisher_bound μ N _ _ u
    (blockProbability_nonneg n w E hw (fun b => (M b).positive))
    (fun z hz a => blockDerivative_zero n w E hw (fun b => (M b).positive) z hz a)
    (block_score_integrable μ n w E hw (fun b => (M b).positive)
      (fun b => (M b).integrable) hF) hu
  simpa only [statisticalFisherTrace, ← blockFisherDensity_score] using
    exact_block_fisher_bound μ n w hw M

end Block

section Resolution
variable {ι B : Type} [Fintype ι] [DecidableEq ι] [Fintype B]
variable (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (n : B → ℕ) (w : B → ℝ)
variable (R : BlockResolution ρ D n w)
include R

theorem exact_resolution_risk_lower {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (M : DensityPOVM ι Ω μ) (u : Ω → Fin 2 → ℝ)
    (hu : MomentUnbiased μ (fun z => born ρ (M.effect z))
      (fun z a => born (D a) (M.effect z)) u) :
    0 < (∑ b, w b * sectorFisher (n b)) ∧
    4*N / (∑ b, w b * sectorFisher (n b)) ≤
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
  have h := exact_block_risk_lower μ n w N R.weight_nonneg M' u
    (by simpa only [hp, hd] using hu)
  simpa only [hp] using h

theorem exact_attainableRisks_lower (N : ℕ) :
    ∀ r ∈ attainableRisks N ρ D, 4*N / (∑ b, w b * sectorFisher (n b)) ≤ r := by
  rintro r ⟨Ω, mΩ, μ, M, u, hu, rfl⟩
  letI : MeasurableSpace Ω := mΩ
  exact (exact_resolution_risk_lower ρ D n w R μ N M u hu).2

end Resolution
end FiniteCopy.Optimization
