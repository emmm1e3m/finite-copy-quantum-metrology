import FiniteCopy.EnsembleIdentity
import FiniteCopy.SimplexDual
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

theorem PureEnsemble.variance_ge_dual {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : PureEnsemble n Ω μ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) :
    (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - dualValue n lam / 4 ≤ E.variance := by
  have h := density_fisher_le_dual μ n lam hlam E.toPOVM
  rw [E.fisher_variance] at h
  linarith

theorem greatest_fisher_of_certificate (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) (hattain : dualValue n lam ∈ fisherValues n) :
    IsGreatest (fisherValues n) (dualValue n lam) := by
  exact ⟨hattain, fun r hr => fisherValue_le_dual n lam hlam r hr⟩

theorem sectorFisher_eq_of_certificate (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) (hattain : dualValue n lam ∈ fisherValues n) :
    sectorFisher n = dualValue n lam :=
  (greatest_fisher_of_certificate n lam hlam hattain).csSup_eq

theorem least_variance_of_certificate (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam)
    (hattain : (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      dualValue n lam / 4 ∈ varianceValues n) :
    IsLeast (varianceValues n)
      ((2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - dualValue n lam / 4) := by
  refine ⟨hattain, ?_⟩
  rintro r ⟨Ω, mΩ, μ, E, rfl⟩
  exact E.variance_ge_dual lam hlam

theorem commonVarianceRoof_eq_of_certificate (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam)
    (hattain : (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      dualValue n lam / 4 ∈ varianceValues n) :
    commonVarianceRoof n =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - dualValue n lam / 4 :=
  (least_variance_of_certificate n lam hlam hattain).csInf_eq

-- 同一个对偶证书同时控制任意测量与任意共同纯态分解。
theorem exact_reduction_of_certificate (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam)
    (hF : dualValue n lam ∈ fisherValues n)
    (hV : (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      dualValue n lam / 4 ∈ varianceValues n) :
    sectorFisher n = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * commonVarianceRoof n := by
  rw [sectorFisher_eq_of_certificate n lam hlam hF,
    commonVarianceRoof_eq_of_certificate n lam hlam hV]
  ring

theorem ensemble_variance_ge_spinL {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (E : PureEnsemble n Ω μ) : NHLowerBound.spinL n ≤ E.variance := by
  have h := (canonical_arbitrary_density_fisher_bound μ n E.toPOVM.effect
    E.toPOVM.positive E.integrable E.complete).2
  change (∫ z, fisherDensity n (Algebra.spinEdge n) (E.toPOVM.effect z) ∂μ) ≤
    capFisherBound n at h
  rw [E.fisher_variance, capFisherBound_eq] at h
  linarith

theorem commonVarianceRoof_ge_spinL (n : ℕ) (hne : (varianceValues n).Nonempty) :
    NHLowerBound.spinL n ≤ commonVarianceRoof n := by
  apply le_csInf hne
  rintro r ⟨Ω, mΩ, μ, E, rfl⟩
  exact ensemble_variance_ge_spinL E

end FiniteCopy.Optimization
