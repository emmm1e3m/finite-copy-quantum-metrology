import FiniteCopy.GaussianRisk
import FiniteCopy.FamilyStatistics
import FiniteCopy.BlockLift
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.GaussianLift
open FiniteCopy.Risk CopyQuantumMetrology

variable {B : Type} [Fintype B] [DecidableEq B] {L : ℕ} [NeZero L]
local instance : MeasurableSpace B := ⊤
local instance : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (ZMod L) := ⊤
local instance : MeasurableSingletonClass (ZMod L) := ⟨fun _ => trivial⟩
variable (n : B → ℕ) (w eps : B → ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ)
variable (R : BlockResolution ρ D n w)
variable (heps : ∀ b, 0 < eps b) (hd : ∀ b, n b+1 ≤ L)
variable (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
variable (hcomplete : (∑ b, R.embedding b * (R.embedding b)ᴴ) = (1 : Matrix ι ι ℂ))

def gaussianFamilyPOVM : DensityPOVM ι (B × (ℝ × ZMod L)) (familyMeasure (B := B) (L := L)) :=
  liftDensityPOVM (gaussianOutcomeMeasure L) n R.embedding
    (fun b => gaussianDensityPOVM (n b) (eps b) (heps b) (hd b)) hcomplete

include horth in
lemma gaussianFamily_born_reference (z : B × (ℝ × ZMod L)) :
    born ρ ((gaussianFamilyPOVM n w eps ρ D R heps hd hcomplete).effect z) =
      familyProbability n w eps z := by
  obtain ⟨b,z⟩ := z
  have h := lifted_born_reference (gaussianOutcomeMeasure L) n
    (fun b => gaussianDensityPOVM (n b) (eps b) (heps b) (hd b)) ρ D w R horth b z
  simpa only [gaussianFamilyPOVM, liftDensityPOVM, ← spinReference_eq_state,
    gaussianDensityPOVM, gaussianOutcomeProbability, familyProbability] using h

include horth in
lemma gaussianFamily_born_tangent (z : B × (ℝ × ZMod L)) (a : Fin 2) :
    born (D a) ((gaussianFamilyPOVM n w eps ρ D R heps hd hcomplete).effect z) =
      familyTangent n w eps z a := by
  obtain ⟨b,z⟩ := z
  have h := lifted_born_tangent (gaussianOutcomeMeasure L) n
    (fun b => gaussianDensityPOVM (n b) (eps b) (heps b) (hd b)) ρ D w R horth b z a
  simpa only [gaussianFamilyPOVM, liftDensityPOVM, ← spinTangent_eq_canonical,
    gaussianDensityPOVM, gaussianOutcomeTangent, familyTangent] using h

-- 结果直接属于035定义的真实风险集合；不是用标量风险公式替换测量。
include R heps hd horth hcomplete in
theorem gaussian_family_risk_attainable (N : ℕ) (hL : 3 ≤ L)
    (hactive : ∃ b, 0 < w b ∧ 0 < n b) :
    2 * N / familyFisher n w eps ∈ attainableRisks N ρ D := by
  have hf := ne_of_gt (familyFisher_pos n w eps R.weight_nonneg heps hactive)
  let M := gaussianFamilyPOVM n w eps ρ D R heps hd hcomplete
  have hp : (fun z => born ρ (M.effect z)) = familyProbability (L := L) n w eps :=
    funext (gaussianFamily_born_reference n w eps ρ D R heps hd horth hcomplete)
  have ht : (fun z a => born (D a) (M.effect z)) = familyTangent (L := L) n w eps :=
    funext fun z => funext (gaussianFamily_born_tangent n w eps ρ D R heps hd horth hcomplete z)
  refine ⟨B × (ℝ × ZMod L), inferInstance, familyMeasure, M, familyEstimator n w eps, ?_, ?_⟩
  · rw [hp, ht]
    exact familyMomentUnbiased n w eps heps hL hf
  · rw [hp]
    exact (family_risk n w eps N heps hL hf).symm

end FiniteCopy.GaussianLift

