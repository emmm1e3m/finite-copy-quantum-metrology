import FiniteCopy.ModelFisher
import FiniteCopy.SchemeBridge
import FiniteCopy.SeedBlocks

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.SeedPOVM

variable {ι B : Type} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
variable {n k : B → ℕ} {L : ℕ} [NeZero L]
variable {ρ : Matrix ι ι ℂ} {D : Fin 2 → Matrix ι ι ℂ} {w : B → ℝ}
local instance : MeasurableSpace (SeedBlocks.Outcome k L) := ⊤
local instance : MeasurableSingletonClass (SeedBlocks.Outcome k L) := ⟨fun _ => trivial⟩

theorem seedBlocks_modelFisher_mem (R : BlockResolution ρ D n w)
    (S : ∀ b, Scheme (n b) (k b)) (hd : ∀ b, n b+1 ≤ L) (hL : 3 ≤ L)
    (horth : ∀ b c, b ≠ c → (R.embedding b)ᴴ * R.embedding c = 0)
    (hcomplete : (∑ b, R.embedding b * (R.embedding b)ᴴ) = (1 : Matrix ι ι ℂ)) :
    SeedBlocks.totalFisher w S ∈ modelFisherValues ρ D := by
  refine ⟨SeedBlocks.Outcome k L, inferInstance, Measure.count,
    SeedBlocks.densityPOVM R S hd hcomplete, ?_⟩
  rw [← SeedBlocks.fisher_trace R S horth hL]
  unfold statisticalFisherTrace
  apply integral_congr_ae
  filter_upwards [] with z
  exact (modelFisherDensity_score ρ D (SeedBlocks.effect R S z)).symm

end FiniteCopy.Optimization
