import FiniteCopy.OptimizationObjects
import FiniteCopy.GaussianAsymptotic

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk
variable {L : ℕ} [NeZero L]
local instance gaussianMemberPhaseMeasurableSpace : MeasurableSpace (ZMod L) := ⊤
local instance gaussianMemberPhaseMeasurableSingleton : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

lemma gaussian_fisherDensity (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (z : ℝ × ZMod L) :
    fisherDensity n (Algebra.spinEdge n) (gaussianOutcomeEffect n eps z) =
      phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate 0) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate 0) +
      phaseProbability (L := L) (spinColumn n eps z.1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate 1) *
        phaseScore (spinCoefficient n) (spinColumn n eps z.1) z.2 (phaseCoordinate 1) := by
  have hx : tangentX n (Algebra.spinEdge n) =
      spinTangent (spinCoefficient n) (phaseCoordinate 0) := by
    simpa using (spinTangent_eq_canonical n 0).symm
  have hy : tangentY n (Algebra.spinEdge n) =
      spinTangent (spinCoefficient n) (phaseCoordinate 1) := by
    simpa using (spinTangent_eq_canonical n 1).symm
  rw [fisherDensity, hx, hy, ← spinReference_eq_state]
  change ((gaussianOutcomeTangent n eps z 0)^2 + (gaussianOutcomeTangent n eps z 1)^2) /
    gaussianOutcomeProbability n eps z = _
  rw [gaussianOutcomeProbability_eq, gaussianOutcomeTangent_eq n heps,
    gaussianOutcomeTangent_eq n heps]
  by_cases hp : phaseProbability (L := L) (spinColumn n eps z.1) = 0
  · simp [hp]
  · field_simp
    <;> ring

theorem gaussian_fisherIntegral (n : ℕ) {eps : ℝ} (heps : 0 < eps) (hL : 3 ≤ L) :
    (∫ z, fisherDensity n (Algebra.spinEdge n) (gaussianOutcomeEffect n eps z)
      ∂gaussianOutcomeMeasure L) = 2 * gaussianFisher n eps := by
  simp_rw [gaussian_fisherDensity n heps]
  rw [integral_add (gaussianProduct_second_integrable n heps 0 0)
    (gaussianProduct_second_integrable n heps 1 1),
    gaussianProduct_second n heps hL 0 0, gaussianProduct_second n heps hL 1 1]
  simp
  ring

theorem gaussian_fisher_mem (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    2 * gaussianFisher n eps ∈ fisherValues n := by
  letI : NeZero (n+3) := ⟨by omega⟩
  letI : MeasurableSpace (ZMod (n+3)) := ⊤
  letI : MeasurableSingletonClass (ZMod (n+3)) := ⟨fun _ => trivial⟩
  exact ⟨ℝ × ZMod (n+3), inferInstance, gaussianOutcomeMeasure (n+3),
    gaussianDensityPOVM n eps heps (by omega),
    (gaussian_fisherIntegral (L := n+3) n heps (by omega)).symm⟩

theorem fisherValues_nonempty (n : ℕ) : (fisherValues n).Nonempty :=
  ⟨2 * gaussianFisher n 1, gaussian_fisher_mem n (by norm_num)⟩

theorem fisherValues_bddAbove (n : ℕ) : BddAbove (fisherValues n) := by
  refine ⟨capFisherBound n, ?_⟩
  rintro r ⟨Ω, mΩ, μ, M, rfl⟩
  exact (canonical_arbitrary_density_fisher_bound μ n M.effect
    M.positive M.integrable M.complete).2

theorem gaussianFisher_le_sectorFisher (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    2 * gaussianFisher n eps ≤ sectorFisher n :=
  le_csSup (fisherValues_bddAbove n) (gaussian_fisher_mem n heps)

theorem sectorFisher_pos {n : ℕ} (hn : 0 < n) : 0 < sectorFisher n :=
  (mul_pos (by norm_num) (gaussianFisher_pos hn (by norm_num : (0 : ℝ)<1))).trans_le
    (gaussianFisher_le_sectorFisher n (by norm_num : (0 : ℝ)<1))

theorem sectorFisher_le_cap (n : ℕ) : sectorFisher n ≤ capFisherBound n :=
  csSup_le (fisherValues_nonempty n) (by
    rintro r ⟨Ω, mΩ, μ, M, rfl⟩
    exact (canonical_arbitrary_density_fisher_bound μ n M.effect
      M.positive M.integrable M.complete).2)

end FiniteCopy.Optimization
