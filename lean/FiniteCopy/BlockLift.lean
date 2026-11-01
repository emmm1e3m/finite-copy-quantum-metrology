import FiniteCopy.RiskTerminal
import FiniteCopy.FiniteBlocks
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.GaussianLift
open FiniteCopy.Risk CopyQuantumMetrology

variable {ι B Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
variable [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace Ω]
variable (μ : Measure Ω) [SFinite μ] (n : B → ℕ)
variable (U : ∀ b, Matrix ι (Fin (n b+1)) ℂ)
variable (M : ∀ b, DensityPOVM (Fin (n b+1)) Ω μ)

def liftedEffect (z : B × Ω) : Matrix ι ι ℂ := U z.1 * (M z.1).effect z.2 * (U z.1)ᴴ

lemma liftedEffect_integrable_slice (b : B) (i j : ι) :
    Integrable (fun z => liftedEffect μ n U M (b,z) i j) μ := by
  simpa only [liftedEffect, Matrix.conjTranspose_conjTranspose] using
    sandwich_integrable μ ((U b)ᴴ) (M b).effect (M b).integrable i j

lemma liftedEffect_integral_slice (b : B) (i j : ι) :
    (∫ z, liftedEffect μ n U M (b,z) i j ∂μ) = (U b * (U b)ᴴ) i j := by
  have h := integral_sandwich μ ((U b)ᴴ) (M b).effect (M b).integrable i j
  have hm : Matrix.of (fun i j => ∫ z, (M b).effect z i j ∂μ) =
      (1 : Matrix (Fin (n b+1)) (Fin (n b+1)) ℂ) := funext fun i => funext ((M b).complete i)
  simpa only [liftedEffect, Matrix.conjTranspose_conjTranspose, hm, Matrix.mul_one] using h

-- 块标签效果是局部 POVM 的正交嵌入，标签测度是真正的计数乘积测度。
def liftDensityPOVM (hcomplete : (∑ b, U b * (U b)ᴴ) = (1 : Matrix ι ι ℂ)) :
    DensityPOVM ι (B × Ω) ((Measure.count : Measure B).prod μ) where
  effect := liftedEffect μ n U M
  positive z := by
    simpa only [liftedEffect, Matrix.conjTranspose_conjTranspose] using
      ((M z.1).positive z.2).conjTranspose_mul_mul_same ((U z.1)ᴴ)
  integrable i j := count_prod_integrable μ _ (fun b => liftedEffect_integrable_slice μ n U M b i j)
  complete i j := by
    rw [count_prod_integral μ _ (fun b => liftedEffect_integrable_slice μ n U M b i j)]
    simp_rw [liftedEffect_integral_slice]
    simpa only [Matrix.sum_apply] using congrFun (congrFun hcomplete i) j

lemma compression_lift_same (hiso : ∀ b, (U b)ᴴ * U b = 1)
    (b : B) (z : Ω) :
    (U b)ᴴ * liftedEffect μ n U M (b,z) * U b = (M b).effect z := by
  change (U b)ᴴ * (U b * (M b).effect z * (U b)ᴴ) * U b = _
  calc
    _ = ((U b)ᴴ * U b) * (M b).effect z * ((U b)ᴴ * U b) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hiso]; simp

lemma compression_lift_other
    (horth : ∀ b c, b ≠ c → (U b)ᴴ * U c = 0)
    (b c : B) (hbc : b ≠ c) (z : Ω) :
    (U b)ᴴ * liftedEffect μ n U M (c,z) * U b = 0 := by
  change (U b)ᴴ * (U c * (M c).effect z * (U c)ᴴ) * U b = _
  calc
    _ = ((U b)ᴴ * U c) * (M c).effect z * ((U c)ᴴ * U b) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [horth b c hbc]; simp

variable (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ) (w : B → ℝ)
variable (R : BlockResolution ρ D n w)

lemma lifted_born_reference
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (b : B) (z : Ω) :
    born ρ (liftedEffect μ n R.embedding M (b,z)) =
      w b * born (FiniteCopy.POVM.state (n b)) ((M b).effect z) := by
  rw [resolution_born_reference ρ D n w R]
  rw [Finset.sum_eq_single b]
  · rw [compression_lift_same μ n R.embedding M R.isometry]
  · intro c hc hcb
    rw [compression_lift_other μ n R.embedding M horth c b hcb]
    simp [born]
  · simp

lemma lifted_born_tangent
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (b : B) (z : Ω) (a : Fin 2) :
    born (D a) (liftedEffect μ n R.embedding M (b,z)) =
      w b * born (if a = 0 then FiniteCopy.POVM.tangentX (n b) (FiniteCopy.Algebra.spinEdge (n b))
        else FiniteCopy.POVM.tangentY (n b) (FiniteCopy.Algebra.spinEdge (n b))) ((M b).effect z) := by
  rw [resolution_born_tangent ρ D n w R]
  rw [Finset.sum_eq_single b]
  · rw [compression_lift_same μ n R.embedding M R.isometry]
  · intro c hc hcb
    rw [compression_lift_other μ n R.embedding M horth c b hcb]
    simp [born]
  · simp

end FiniteCopy.GaussianLift

