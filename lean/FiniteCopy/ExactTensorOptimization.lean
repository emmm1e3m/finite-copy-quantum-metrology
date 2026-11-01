import FiniteCopy.ExactOptimization
import FiniteCopy.SchemeBlockBridge
import FiniteCopy.RawSeeds
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.SeedPOVM
open SpinPaths TensorModel

def tensorOptimalScheme (N : ℕ) (b : B N) : Scheme (spin N b) (spin N b+1) :=
  optimalScheme (spin N b)

theorem tensorOptimalScheme_total (N : ℕ) :
    SeedBlocks.totalFisher (weight N) (tensorOptimalScheme N) = tensorFisherDenominator N := by
  unfold SeedBlocks.totalFisher tensorOptimalScheme tensorFisherDenominator
  simp only [optimalScheme_totalFisher]

theorem tensorFisherDenominator_mem (N : ℕ) :
    tensorFisherDenominator N ∈ modelFisherValues (rhoTensor N 0 0) (tangentAxes N) := by
  rw [← tensorOptimalScheme_total]
  apply seedBlocks_modelFisher_mem (L := N+3) (blockResolution N) (tensorOptimalScheme N)
  · intro b
    have h := EndpointCounting.path_spin_le N b
    omega
  · omega
  · exact U_orthogonal N
  · exact U_complete N

-- 所有实际 joint POVM 的最大 Fisher，有限结果测量达到这个最大值。
theorem tensorFisher_isGreatest (N : ℕ) :
    IsGreatest (modelFisherValues (rhoTensor N 0 0) (tangentAxes N)) (tensorFisherDenominator N) := by
  refine ⟨tensorFisherDenominator_mem N, ?_⟩
  intro r hr
  exact modelFisherValue_le_resolution (rhoTensor N 0 0) (tangentAxes N) (spin N) (weight N)
    (blockResolution N) r hr

theorem tensorFisher_eq (N : ℕ) :
    modelFisher (rhoTensor N 0 0) (tangentAxes N) = Schur.schurAverage sectorFisher N := by
  rw [modelFisher, (tensorFisher_isGreatest N).csSup_eq, tensorFisherDenominator_schur]

theorem tensor_risk_attainable (N : ℕ) (hN : 0 < N) :
    4*N / tensorFisherDenominator N ∈ attainableRisks N (rhoTensor N 0 0) (tangentAxes N) := by
  rw [← tensorOptimalScheme_total]
  apply SeedBlocks.risk_attainable (L := N+3) (blockResolution N) (tensorOptimalScheme N)
  · intro b
    have h := EndpointCounting.path_spin_le N b
    omega
  · omega
  · exact U_orthogonal N
  · exact U_complete N
  · rw [tensorOptimalScheme_total]
    exact tensorFisherDenominator_pos N hN

theorem tensorOptimalRisk_eq (N : ℕ) (hN : 0 < N) :
    optimalRisk N (rhoTensor N 0 0) (tangentAxes N) =
      4*N / Schur.schurAverage sectorFisher N := by
  have h := optimalRisk_sandwich N (rhoTensor N 0 0) (tangentAxes N)
    (4*N / tensorFisherDenominator N) (4*N / tensorFisherDenominator N)
    (tensor_attainableRisks_lower N) (tensor_risk_attainable N hN)
  rw [← tensorFisherDenominator_schur]
  exact le_antisymm h.2 h.1

theorem tensorOptimalRisk_attained (N : ℕ) (hN : 0 < N) :
    optimalRisk N (rhoTensor N 0 0) (tangentAxes N) ∈
      attainableRisks N (rhoTensor N 0 0) (tangentAxes N) := by
  rw [tensorOptimalRisk_eq N hN, ← tensorFisherDenominator_schur]
  exact tensor_risk_attainable N hN

theorem tensor_denominator_roof (N : ℕ) :
    Schur.schurAverage sectorFisher N =
      2*N - 4*Schur.schurAverage commonVarianceRoof N := by
  rw [← Schur.schurAverage_fisher commonVarianceRoof N]
  unfold Schur.schurAverage
  apply Finset.sum_congr rfl
  intro k hk
  rw [exact_sector_reduction]

theorem tensorOptimalRisk_roof (N : ℕ) (hN : 0 < N) :
    optimalRisk N (rhoTensor N 0 0) (tangentAxes N) =
      4*N / (2*N - 4*Schur.schurAverage commonVarianceRoof N) := by
  rw [tensorOptimalRisk_eq N hN, tensor_denominator_roof]

-- 原始非负幅度列的最大值由至多 d 列达到。
theorem rawSeed_isGreatest (n : ℕ) : IsGreatest (rawSeedValues n) (sectorFisher n) := by
  refine ⟨?_, ?_⟩
  · refine ⟨n+1, rawSeed (optimalScheme n), rawSeed_nonneg _, rawSeed_complete _, ?_⟩
    rw [rawSeedFisher_eq, optimalScheme_totalFisher]
  · intro r hr
    let C := optimalCertificate n
    have h := rawSeedValue_le_dual n C.coefficient C.majorant r hr
    rw [← C.attained] at h
    exact h.trans_eq (optimalScheme_totalFisher n)

end FiniteCopy.Optimization
