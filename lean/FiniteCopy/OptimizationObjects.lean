import FiniteCopy.GaussianRisk
import FiniteCopy.StrictPOVMGap
import FiniteCopy.SpinTrace
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section

namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

-- 结果空间与测度均不作有限性限制；目标取实际 Born Fisher 密度积分。
def fisherValues (n : ℕ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (M : @DensityPOVM (Fin (n+1)) Ω _ _ mΩ μ),
      r = ∫ z, fisherDensity n (Algebra.spinEdge n) (M.effect z) ∂μ}

def sectorFisher (n : ℕ) : ℝ := sSup (fisherValues n)

-- 同一组复纯态同时计算 x、y 方差。矩阵完整性正是平均态 I/d。
structure PureEnsemble (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  probability : Ω → ℝ
  state : Ω → Fin (n+1) → ℂ
  nonneg : ∀ z, 0 ≤ probability z
  normalized : ∀ z, vectorMass (state z) = 1
  integrable : ∀ i j, Integrable
    (fun z => ((n+1 : ℝ) * probability z) • rankOne (state z) i j) μ
  complete : ∀ i j, (∫ z, ((n+1 : ℝ) * probability z) • rankOne (state z) i j ∂μ) =
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j

def PureEnsemble.variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (E : PureEnsemble n Ω μ) : ℝ :=
  ∫ z, E.probability z * (pureVariance (spinX (spinCoefficient n)) (E.state z) +
    pureVariance (spinY (spinCoefficient n)) (E.state z)) ∂μ

def varianceValues (n : ℕ) : Set ℝ :=
  {r | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (E : @PureEnsemble n Ω mΩ μ), r = E.variance}

def commonVarianceRoof (n : ℕ) : ℝ := sInf (varianceValues n)

def simplexGamma (n : ℕ) (p : Fin (n+1) → ℝ) : ℝ :=
  seedMoment (spinCoefficient n) (fun i => Real.sqrt (p i))

def simplexObjective (n : ℕ) (p : Fin (n+1) → ℝ) : ℝ := 4 * simplexGamma n p ^ 2

lemma simplexGamma_continuous (n : ℕ) : Continuous (simplexGamma n) := by
  unfold simplexGamma seedMoment
  fun_prop

lemma simplexObjective_continuous (n : ℕ) : Continuous (simplexObjective n) := by
  exact continuous_const.mul ((simplexGamma_continuous n).pow 2)

def dualValue (n : ℕ) (lam : Fin (n+1) → ℝ) : ℝ := (∑ i, lam i) / (n+1)

def IsDualCertificate (n : ℕ) (lam : Fin (n+1) → ℝ) : Prop :=
  ∀ p ∈ stdSimplex ℝ (Fin (n+1)), simplexObjective n p ≤ ∑ i, lam i * p i

-- 对偶证书是逐点上界，不含最优化结论；后续由紧凸几何构造证书。
lemma dualCertificate_nonneg (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) (i : Fin (n+1)) : 0 ≤ lam i := by
  classical
  let p : Fin (n+1) → ℝ := fun j => if j = i then 1 else 0
  have hp : p ∈ stdSimplex ℝ (Fin (n+1)) := by
    constructor
    · intro j; dsimp [p]; split_ifs <;> norm_num
    · simp [p]
  have h := hlam p hp
  have h0 : 0 ≤ simplexObjective n p := by unfold simplexObjective; positivity
  have hs : (∑ j, lam j * p j) = lam i := by simp [p]
  rw [hs] at h
  exact h0.trans h

end FiniteCopy.Optimization

