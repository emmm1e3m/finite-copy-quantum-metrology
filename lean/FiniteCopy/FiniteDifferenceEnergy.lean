import FiniteCopy.GradientBounds
open MeasureTheory Set

namespace CopyQuantumMetrology.GradientBounds

-- 二阶导数路径能量直接控制有限差分与起点一阶导数的双边能量误差。
theorem weighted_finite_difference_energy_error_le
    {v D₁ D₂ : ℝ → ℝ → ℝ} {q : ℝ → ℝ} {η A B : ℝ} (a : ℝ)
    (hη : 0 < η) (hq : ∀ t, 0 ≤ q t)
    (hv : ∀ t s, s ∈ Icc a (a+1) → HasDerivAt (fun s => v s t) (D₁ s t) s)
    (hD₁ : ∀ t s, s ∈ Icc a (a+1) → HasDerivAt (fun s => D₁ s t) (D₂ s t) s)
    (hD₂ : ∀ t, ContinuousOn (fun s => D₂ s t) (Icc a (a+1)))
    (hf : Integrable (fun t => q t*(v (a+1) t-v a t)^2))
    (hg : Integrable (fun t => q t*D₁ a t^2))
    (hr : Integrable (fun t => q t*(v (a+1) t-v a t-D₁ a t)^2))
    (hprod : Integrable (fun p : ℝ × ℝ => q p.2*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc a (a+1))).prod volume))
    (hA : (∫ t, q t*D₁ a t^2) ≤ A)
    (hB : (∫ s in Ioc a (a+1), ∫ t, q t*D₂ s t^2) ≤ B) :
    |(∫ t, q t*(v (a+1) t-v a t)^2)-(∫ t, q t*D₁ a t^2)| ≤
      η*A+(1+1/η)*B := by
  have hR := (weighted_remainder_le a hq hv hD₁ hD₂ hr hprod).trans hB
  have he := abs_energy_difference_le hη hq hf hg hr
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hA hη.le)
    (mul_le_mul_of_nonneg_left hR (by positivity)))

end CopyQuantumMetrology.GradientBounds

