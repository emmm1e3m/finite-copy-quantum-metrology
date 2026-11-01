import FiniteCopy.FixedLimit
import FiniteCopy.FixedGradient
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CopyQuantumMetrology.FixedWidth

/-- 任意固定正C²轮廓的实际U/J极限；终端只保留论文原始函数假设。 -/
theorem fixed_positive_C2_scale_limit {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ 2 b (Icc (-1:ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 < b x) :
    Tendsto (fun n : ℕ => U b n/GlobalBounds.spinJ n) atTop
      (𝓝 ((∫ x in (-1:ℝ)..1, (x^2*b x+1/(4*b x)))/2)) := by
  obtain ⟨L,M,hL,hM,hbounds⟩ := GeneralWidth.exists_uniform_bounds hb hpos
  obtain ⟨CG,hCG,hGglobal⟩ := G_global_exists hb hpos
  have hbLM : ∀ x ∈ Icc (-1:ℝ) 1, L ≤ b x ∧ b x ≤ M := by
    intro x hx
    exact ⟨(hbounds x hx).1,(le_abs_self (b x)).trans (hbounds x hx).2.1⟩
  apply U_limit_of_gradient_bounds hb.continuousOn hL hM hbLM hCG hGglobal
  intro delta hd hd1
  obtain ⟨KG,hKG,hGbulk⟩ := G_bulk_exists hb hpos hd hd1
  exact ⟨KG,hKG,fun J hJ m _hm _hm1 hmb hm1b => hGbulk J hJ m hmb hm1b⟩

/-- n=2j，因而同时覆盖全部整数与半整数自旋；没有能量或局部渐近假设。 -/
theorem fixed_positive_C2_energy_limit {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ 2 b (Icc (-1:ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 < b x) :
    Tendsto (fun n : ℕ => U b n/((n:ℝ)/2)) atTop
      (𝓝 ((∫ x in (-1:ℝ)..1, (x^2*b x+1/(4*b x)))/2)) :=
  U_spin_limit_of_scale_limit (fixed_positive_C2_scale_limit hb hpos)

end CopyQuantumMetrology.FixedWidth
