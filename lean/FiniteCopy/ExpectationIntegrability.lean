import FiniteCopy.BornExpectation
import FiniteCopy.POVMLower

open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
open Matrix MeasureTheory
open FiniteCopy.POVM
noncomputable section
namespace CopyQuantumMetrology.TensorModel

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

lemma psd_norm_entry_le_traceReal (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (i j : ι) :
    ‖E i j‖ ≤ traceReal E := by
  have hd (i : ι) : (E i i).re ≤ traceReal E := by
    change (E i i).re ≤ (Matrix.trace E).re
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => psd_diag_nonneg hE j) (Finset.mem_univ i)
  have ht : 0 ≤ traceReal E := (psd_diag_nonneg hE i).trans (hd i)
  calc
    ‖E i j‖ ≤ Real.sqrt (E i i).re * Real.sqrt (E j j).re := psd_entry_bound hE i j
    _ ≤ Real.sqrt (traceReal E) * Real.sqrt (traceReal E) :=
      mul_le_mul (Real.sqrt_le_sqrt (hd i)) (Real.sqrt_le_sqrt (hd j))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = traceReal E := Real.mul_self_sqrt ht

-- 满秩参考态下的绝对一阶矩足以保证全部估计器加权矩阵元可积。
-- 不额外假设估计器在零概率集合上的可测性：PSD在那里迫使所有矩阵元为零。
theorem weighted_entries_integrable [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → Matrix ι ι ℂ) (hE : ∀ z, (E z).PosSemidef)
    (hEi : ∀ i j, Integrable (fun z => E z i j) μ) (d : ℝ) (hd : 0 < d)
    (u : Ω → ℝ) (hu : Integrable (fun z => (traceReal (E z) / d) * u z) μ)
    (i j : ι) : Integrable (fun z => u z • E z i j) μ := by
  let p : Ω → ℝ := fun z => traceReal (E z) / d
  have htr : Integrable (fun z => traceReal (E z)) μ := by
    simpa [traceReal, Matrix.trace, Matrix.diag] using
      integrable_finsetSum Finset.univ (fun k _ => (hEi k k).re)
  have hp : Integrable p μ := htr.div_const d
  have hp0 (z : Ω) : 0 ≤ p z := by
    apply div_nonneg _ hd.le
    exact (norm_nonneg (E z i i)).trans (psd_norm_entry_le_traceReal (E z) (hE z) i i)
  have hz (z : Ω) (hz : p z = 0) : E z = 0 := by
    apply psd_traceReal_zero (E z) (hE z)
    exact (div_eq_zero_iff.mp hz).resolve_right hd.ne'
  have he (z : Ω) : u z • E z i j = (p z * u z) • ((p z)⁻¹ • E z i j) := by
    by_cases hpz : p z = 0
    · simp [hz z hpz, hpz]
    · rw [smul_smul]
      congr 1
      field_simp
  have hm : AEStronglyMeasurable (fun z => u z • E z i j) μ := by
    simp_rw [he]
    exact hu.aestronglyMeasurable.smul (hp.aestronglyMeasurable.aemeasurable.inv.aestronglyMeasurable.smul (hEi i j).aestronglyMeasurable)
  apply (hu.norm.const_mul d).mono' hm
  filter_upwards [] with z
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |u z| * ‖E z i j‖ ≤ |u z| * traceReal (E z) :=
      mul_le_mul_of_nonneg_left (psd_norm_entry_le_traceReal (E z) (hE z) i j) (abs_nonneg _)
    _ = d * |p z * u z| := by
      rw [abs_mul, abs_of_nonneg (hp0 z)]
      dsimp [p]
      field_simp
      <;> ring


theorem rhoTensor_expectation_hasDerivAt_x_of_firstMoment [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (E : Ω → NMatrix N)
    (hE : ∀ z, (E z).PosSemidef) (hEi : ∀ i j, Integrable (fun z => E z i j) μ)
    (u : Ω → ℝ) (hu : Integrable (fun z => born (rhoTensor N 0 0) (E z) * u z) μ) :
    HasDerivAt (fun x => ∫ z, u z * born (rhoTensor N x 0) (E z) ∂μ)
      (∫ z, u z * born ((2 / (2 : ℂ)^N) • collectiveX N) (E z) ∂μ) 0 := by
  apply rhoTensor_expectation_hasDerivAt_x μ N E u
  intro i j
  apply weighted_entries_integrable μ E hE hEi ((2 : ℝ)^N) (by positivity) u _ i j
  simpa only [born_rhoTensor_zero, traceReal] using hu

theorem rhoTensor_expectation_hasDerivAt_y_of_firstMoment [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (E : Ω → NMatrix N)
    (hE : ∀ z, (E z).PosSemidef) (hEi : ∀ i j, Integrable (fun z => E z i j) μ)
    (u : Ω → ℝ) (hu : Integrable (fun z => born (rhoTensor N 0 0) (E z) * u z) μ) :
    HasDerivAt (fun y => ∫ z, u z * born (rhoTensor N 0 y) (E z) ∂μ)
      (∫ z, u z * born ((2 / (2 : ℂ)^N) • collectiveY N) (E z) ∂μ) 0 := by
  apply rhoTensor_expectation_hasDerivAt_y μ N E u
  intro i j
  apply weighted_entries_integrable μ E hE hEi ((2 : ℝ)^N) (by positivity) u _ i j
  simpa only [born_rhoTensor_zero, traceReal] using hu

end CopyQuantumMetrology.TensorModel




