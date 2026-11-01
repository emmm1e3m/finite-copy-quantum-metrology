import FiniteCopy.CertificateReduction
import FiniteCopy.FiniteSeed

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.SeedPOVM

variable {n k L : ℕ} [NeZero L]
local instance schemeBridgePhaseMeasurableSpace : MeasurableSpace (ZMod L) := ⊤
local instance schemeBridgePhaseMeasurableSingleton : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩

def schemeEnsemble (S : Scheme n k) (hd : n+1 ≤ L) :
    PureEnsemble n (Fin k × ZMod L) Measure.count where
  probability := S.ensembleWeight
  state := S.ensembleState
  nonneg := S.ensembleWeight_nonneg
  normalized := S.ensembleState_mass
  integrable _ _ := Scheme.finite_integrable _
  complete i j := by
    have h := congrFun (congrFun (S.outcomeEffect_complete hd) i) j
    rw [integral_count]
    simpa only [S.outcomeEffect_rankOne, Matrix.sum_apply, Matrix.smul_apply] using h

lemma schemeEnsemble_variance (S : Scheme n k) (hd : n+1 ≤ L) :
    (schemeEnsemble S hd).variance =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - S.value := by
  unfold PureEnsemble.variance
  simp only [schemeEnsemble]
  rw [integral_count]
  exact S.ensemble_variance hd

lemma schemeEnsemble_fisher (S : Scheme n k) (hd : n+1 ≤ L) :
    (∫ z, fisherDensity n (Algebra.spinEdge n)
      ((schemeEnsemble S hd).toPOVM.effect z) ∂Measure.count) = S.totalFisher := by
  rw [(schemeEnsemble S hd).fisher_variance, schemeEnsemble_variance]
  unfold Scheme.totalFisher
  ring

theorem scheme_fisher_mem (S : Scheme n k) : S.totalFisher ∈ fisherValues n := by
  letI : NeZero (n+3) := ⟨by omega⟩
  letI : MeasurableSpace (ZMod (n+3)) := ⊤
  letI : MeasurableSingletonClass (ZMod (n+3)) := ⟨fun _ => trivial⟩
  let E := schemeEnsemble (L := n+3) S (by omega)
  exact ⟨Fin k × ZMod (n+3), inferInstance, Measure.count, E.toPOVM,
    (schemeEnsemble_fisher (L := n+3) S (by omega)).symm⟩

theorem scheme_variance_mem (S : Scheme n k) :
    (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - S.value ∈ varianceValues n := by
  letI : NeZero (n+3) := ⟨by omega⟩
  letI : MeasurableSpace (ZMod (n+3)) := ⊤
  letI : MeasurableSingletonClass (ZMod (n+3)) := ⟨fun _ => trivial⟩
  exact ⟨Fin k × ZMod (n+3), inferInstance, Measure.count,
    schemeEnsemble (L := n+3) S (by omega),
    (schemeEnsemble_variance (L := n+3) S (by omega)).symm⟩

lemma scheme_objective (S : Scheme n k) :
    (∑ a, S.q a * simplexObjective n (S.p a)) = S.totalFisher := by
  unfold simplexObjective simplexGamma Scheme.totalFisher Scheme.value Scheme.gamma Scheme.amplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem scheme_le_dual (S : Scheme n k) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) : S.totalFisher ≤ dualValue n lam :=
  fisherValue_le_dual n lam hlam _ (scheme_fisher_mem S)

-- 此对象的见证是至多 d 种种子和逐点对偶证书；取得定理由紧凸几何构造。
structure OptimalScheme (n : ℕ) where
  scheme : Scheme n (n+1)
  coefficient : Fin (n+1) → ℝ
  majorant : IsDualCertificate n coefficient
  attained : scheme.totalFisher = dualValue n coefficient

end FiniteCopy.Optimization
