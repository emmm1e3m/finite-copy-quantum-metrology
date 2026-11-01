import FiniteCopy.ExactBlockLower
import FiniteCopy.Resolution
import FiniteCopy.PathSchur

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

def modelFisherDensity {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (E : Matrix ι ι ℂ) : ℝ :=
  ((born (D 0) E)^2 + (born (D 1) E)^2) / born ρ E

def modelFisherValues {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (M : @DensityPOVM ι Ω _ _ mΩ μ), r = ∫ z, modelFisherDensity ρ D (M.effect z) ∂μ}

def modelFisher {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) : ℝ := sSup (modelFisherValues ρ D)

lemma modelFisherDensity_score {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (E : Matrix ι ι ℂ) :
    modelFisherDensity ρ D E = born ρ E *
      ((born (D 0) E / born ρ E)^2 + (born (D 1) E / born ρ E)^2) := by
  unfold modelFisherDensity
  by_cases hp : born ρ E = 0
  · simp [hp]
  · field_simp

theorem resolution_modelFisher_le {ι B : Type} [Fintype ι] [DecidableEq ι] [Fintype B]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (n : B → ℕ) (w : B → ℝ)
    (R : BlockResolution ρ D n w) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : DensityPOVM ι Ω μ) :
    (∫ z, modelFisherDensity ρ D (M.effect z) ∂μ) ≤ ∑ b, w b * sectorFisher (n b) := by
  let M' := fun b => M.compress μ (R.embedding b) (R.isometry b)
  have he (z : Ω) : modelFisherDensity ρ D (M.effect z) =
      blockFisherDensity n w (fun b => (M' b).effect) z := by
    unfold modelFisherDensity blockFisherDensity blockProbability blockDerivative
    rw [resolution_born_reference ρ D n w R,
      resolution_born_tangent ρ D n w R, resolution_born_tangent ρ D n w R]
    rfl
  simp_rw [he]
  exact exact_block_fisher_bound μ n w R.weight_nonneg M'

theorem modelFisherValue_le_resolution {ι B : Type} [Fintype ι] [DecidableEq ι] [Fintype B]
    (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (n : B → ℕ) (w : B → ℝ)
    (R : BlockResolution ρ D n w) (r : ℝ) (hr : r ∈ modelFisherValues ρ D) :
    r ≤ ∑ b, w b * sectorFisher (n b) := by
  obtain ⟨Ω, mΩ, μ, M, rfl⟩ := hr
  exact resolution_modelFisher_le ρ D n w R μ M

open SpinPaths TensorModel

-- 这里的权重与嵌入均为实际 tensor-CG 构造的对象。
def tensorFisherDenominator (N : ℕ) : ℝ :=
  ∑ b : B N, weight N b * sectorFisher (spin N b)

theorem tensorFisherDenominator_schur (N : ℕ) :
    tensorFisherDenominator N = Schur.schurAverage sectorFisher N := by
  simpa only [tensorFisherDenominator, weight, Nat.cast_add, Nat.cast_one] using
    EndpointCounting.path_schur_average N sectorFisher

theorem tensorFisherDenominator_pos (N : ℕ) (hN : 0 < N) :
    0 < tensorFisherDenominator N := by
  have hb : 2 * globalGaussianFisher N ≤ tensorFisherDenominator N := by
    rw [tensorFisherDenominator_schur]
    unfold globalGaussianFisher Schur.schurAverage
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hw := Schur.weight_nonneg (N := N) (k := k) (by
      have h := Finset.mem_range.mp hk
      omega)
    have h := gaussianFisher_le_sectorFisher (N-2*k)
      (epsilon_pos (spinJ_pos (N-2*k)).le)
    exact (by simpa only [logarithmicFisher, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left h hw)
  exact (mul_pos (by norm_num) (globalGaussianFisher_pos N hN)).trans_le hb

theorem tensor_attainableRisks_lower (N : ℕ) :
    ∀ r ∈ attainableRisks N (rhoTensor N 0 0) (tangentAxes N),
      4*N / tensorFisherDenominator N ≤ r :=
  exact_attainableRisks_lower (rhoTensor N 0 0) (tangentAxes N) (spin N) (weight N)
    (blockResolution N) N

end FiniteCopy.Optimization
