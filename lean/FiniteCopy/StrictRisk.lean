import FiniteCopy.RiskTerminal
import FiniteCopy.StrictPOVMGap

open scoped BigOperators Topology
open MeasureTheory Matrix Filter
noncomputable section
namespace FiniteCopy.MainTheorem
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk

-- 一个正权重块的统一 Fisher 缺口在任意全局测量下仍保留。
theorem block_fisher_bound_with_one_gap {B Ω : Type*} [Fintype B] [DecidableEq B]
    [MeasurableSpace Ω] (μ : Measure Ω) (n : B → ℕ) (w : B → ℝ)
    (M : ∀ b, DensityPOVM (Fin (n b+1)) Ω μ) (hw : ∀ b, 0 ≤ w b)
    (b₀ : B) (Δ : ℝ)
    (hgap : (∫ z, fisherDensity (n b₀) (FiniteCopy.Algebra.spinEdge (n b₀))
      ((M b₀).effect z) ∂μ) ≤ capFisherBound (n b₀) - Δ) :
    (∫ z, blockFisherDensity n w (fun b => (M b).effect) z ∂μ) ≤
      (∑ b, w b * capFisherBound (n b)) - w b₀ * Δ := by
  let E := fun b => (M b).effect
  have hf := block_fisher_bound μ n w E hw (fun b => (M b).positive)
    (fun b => (M b).integrable) (fun b => (M b).complete)
  have hb (b : B) := canonical_arbitrary_density_fisher_bound μ (n b) (E b)
    (M b).positive (M b).integrable (M b).complete
  have hs : Integrable (fun z => ∑ b, w b *
      fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z)) μ :=
    integrable_finsetSum _ (fun b _ => (hb b).1.const_mul _)
  calc
    _ ≤ ∫ z, ∑ b, w b * fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z) ∂μ :=
      integral_mono hf.1 hs (blockFisherDensity_bound n w E hw (fun b => (M b).positive))
    _ = ∑ b, w b * ∫ z, fisherDensity (n b) (FiniteCopy.Algebra.spinEdge (n b)) (E b z) ∂μ := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro b _; exact (hb b).1.const_mul _
    _ ≤ ∑ b, (w b * capFisherBound (n b) - if b=b₀ then w b₀ * Δ else 0) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases h : b = b₀
      · subst b
        simp only [ite_true]
        have h := mul_le_mul_of_nonneg_left hgap (hw b₀)
        dsimp [E] at *
        nlinarith
      · simpa only [h, ite_false, sub_zero, capFisherBound] using
          mul_le_mul_of_nonneg_left (hb b).2 (hw b)
    _ = _ := by simp [Finset.sum_sub_distrib]

-- 原Hilbert空间测量先作实际等距压缩；缺口不要求估计器或测量达到最优。
theorem resolution_uniform_risk_gap {ι B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype B] [DecidableEq B] (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ)
    (n : B → ℕ) (w : B → ℝ) (R : BlockResolution ρ D n w)
    (b₀ : B) (hn : 10 ≤ n b₀) (hw₀ : 0 < w b₀) :
    ∃ η > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
      (M : DensityPOVM ι Ω μ) (u : Ω → Fin 2 → ℝ),
      MomentUnbiased μ (fun z => born ρ (M.effect z)) (fun z a => born (D a) (M.effect z)) u →
      0 < (∑ b, w b * capFisherBound (n b)) - η ∧
      4*N / ((∑ b, w b * capFisherBound (n b)) - η) ≤
        risk μ N (fun z => born ρ (M.effect z)) u := by
  obtain ⟨Δ, hΔ, hgap⟩ := canonical_arbitrary_density_fisher_strict_gap (n b₀) hn
  refine ⟨w b₀ * Δ, mul_pos hw₀ hΔ, ?_⟩
  intro Ω _ μ N M u hu
  let M' := fun b => M.compress μ (R.embedding b) (R.isometry b)
  let E := fun b => (M' b).effect
  have hp : blockProbability n w E = (fun z => born ρ (M.effect z)) := by
    funext z
    exact (resolution_born_reference ρ D n w R (M.effect z)).symm
  have hd : blockDerivative n w E = (fun z a => born (D a) (M.effect z)) := by
    funext z a
    exact (resolution_born_tangent ρ D n w R (M.effect z) a).symm
  have hf := block_fisher_bound μ n w E R.weight_nonneg
    (fun b => (M' b).positive) (fun b => (M' b).integrable) (fun b => (M' b).complete)
  have hbound := block_fisher_bound_with_one_gap μ n w M' R.weight_nonneg b₀ Δ
    (hgap μ (M' b₀).effect (M' b₀).positive (M' b₀).integrable (M' b₀).complete)
  have hr := risk_lower_of_fisher_bound μ N (blockProbability n w E) (blockDerivative n w E) u
    (blockProbability_nonneg n w E R.weight_nonneg (fun b => (M' b).positive))
    (fun z hz a => blockDerivative_zero n w E R.weight_nonneg (fun b => (M' b).positive) z hz a)
    (block_score_integrable μ n w E R.weight_nonneg (fun b => (M' b).positive)
      (fun b => (M' b).integrable) hf.1) (by simpa only [hp, hd] using hu)
    ((∑ b, w b * capFisherBound (n b)) - w b₀*Δ)
    (by simpa only [statisticalFisherTrace, ← blockFisherDensity_score] using hbound)
  simpa only [hp] using hr

theorem optimalRisk_strict_cap_of_resolution {ι B : Type} [Fintype ι] [DecidableEq ι]
    [Fintype B] [DecidableEq B] (ρ : Matrix ι ι ℂ) (D : Fin 2 → Matrix ι ι ℂ)
    (n : B → ℕ) (w : B → ℝ) (R : BlockResolution ρ D n w)
    (b₀ : B) (hn : 10 ≤ n b₀) (hw₀ : 0 < w b₀) (N : ℕ) (hN : 0 < N)
    (hne : (attainableRisks N ρ D).Nonempty) :
    4*N / (∑ b, w b * capFisherBound (n b)) < optimalRisk N ρ D := by
  obtain ⟨η, hη, hbound⟩ := resolution_uniform_risk_gap ρ D n w R b₀ hn hw₀
  have hstrength : ∀ r ∈ attainableRisks N ρ D,
      0 < (∑ b, w b * capFisherBound (n b)) - η ∧
      4*N / ((∑ b, w b * capFisherBound (n b)) - η) ≤ r := by
    rintro r ⟨Ω, mΩ, μ, M, u, hu, rfl⟩
    letI : MeasurableSpace Ω := mΩ
    exact hbound μ N M u hu
  obtain ⟨r, hr⟩ := hne
  have hpos := (hstrength r hr).1
  have hlow : 4*N / ((∑ b, w b * capFisherBound (n b)) - η) ≤ optimalRisk N ρ D :=
    le_csInf ⟨r, hr⟩ (fun r hr => (hstrength r hr).2)
  apply lt_of_lt_of_le _ hlow
  apply div_lt_div_of_pos_left
  · positivity
  · exact hpos
  · linarith

end FiniteCopy.MainTheorem
