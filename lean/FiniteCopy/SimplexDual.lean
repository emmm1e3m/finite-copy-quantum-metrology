import FiniteCopy.OptimizationObjects
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.Algebra

lemma simplexGamma_of_seed (n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ i ≤ n, 0 ≤ v i) :
    simplexGamma n (fun i => v i.val ^ 2) = moment n (spinEdge n) v := by
  unfold simplexGamma seedMoment moment
  simp_rw [Real.sqrt_sq (hv _ (Nat.le_of_lt_succ (Fin.castSucc _).isLt)),
    Real.sqrt_sq (hv _ (Nat.le_of_lt_succ (Fin.succ _).isLt))]
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

lemma simplex_of_unit_seed (n : ℕ) (v : ℕ → ℝ) (hm : mass n v = 1) :
    (fun i : Fin (n+1) => v i.val ^ 2) ∈ stdSimplex ℝ (Fin (n+1)) := by
  refine ⟨fun _ => sq_nonneg _, ?_⟩
  change (∑ i : Fin (n+1), v i.val ^ 2) = 1
  rw [Fin.sum_univ_eq_sum_range (fun i => v i ^ 2)]
  exact hm

-- 齐次化后，对偶线性式直接作用于原 PSD 效应的对角元。
theorem psd_fisher_le_dual (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef) :
    fisherDensity n (spinEdge n) E ≤ (∑ i, lam i * (E i i).re) / (n+1) := by
  have htr : 0 ≤ traceReal E := by
    rw [← root_mass n E hE]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hz : traceReal E = 0
  · have hzero := psd_traceReal_zero E hE hz
    subst E
    simp [fisherDensity, born]
  have hm : 0 < mass n (diagonalRoot n E) := by
    rw [root_mass n E hE]
    exact lt_of_le_of_ne htr (Ne.symm hz)
  let v := Gap.normalizeSeed n (diagonalRoot n E)
  have hv : ∀ i ≤ n, 0 ≤ v i := by
    intro i hi
    exact ((Gap.normalizeSeed_mem n _ hm (fun _ _ => Real.sqrt_nonneg _)).1 i).1
  have hunit : mass n v = 1 := Gap.normalizeSeed_mass n _ hm
  have hp := hlam (fun i => v i.val ^ 2) (simplex_of_unit_seed n v hunit)
  rw [simplexObjective, simplexGamma_of_seed n v hv] at hp
  have hmobj := Gap.normalizeSeed_objective n (spinEdge n) (diagonalRoot n E) hm
  have hpop (i : Fin (n+1)) :
      mass n (diagonalRoot n E) * v i.val ^ 2 = (E i i).re := by
    rw [Gap.normalizeSeed_population n _ hm _ (Nat.le_of_lt_succ i.isLt),
      root_sq n E hE, vertex_coe]
  have hscaled := mul_le_mul_of_nonneg_left hp hm.le
  have hleft : mass n (diagonalRoot n E) *
      (4 * moment n (spinEdge n) v ^ 2) =
      4 * (moment n (spinEdge n) (diagonalRoot n E)^2 / mass n (diagonalRoot n E)) := by
    calc
      _ = 4 * (mass n (diagonalRoot n E) * moment n (spinEdge n) v ^ 2) := by ring
      _ = _ := by rw [hmobj]
  have hright : mass n (diagonalRoot n E) * (∑ i, lam i * v i.val ^ 2) =
      ∑ i, lam i * (E i i).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hpop i]
    ring
  rw [hleft, hright] at hscaled
  have hroot := psd_quotient_le_root_seed n (spinEdge n) E hE
    (fun i hi => Real.sqrt_nonneg _)
  rw [fisherDensity_formula n (spinEdge n) E hE.isHermitian]
  have hd : (0 : ℝ) < n+1 := by positivity
  calc
    _ = (4 * (‖coherence n (spinEdge n) E‖^2 / traceReal E)) / (n+1) := by
      push_cast; ring
    _ ≤ (4 * (moment n (spinEdge n) (diagonalRoot n E)^2 /
        mass n (diagonalRoot n E))) / (n+1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num)) hd.le
    _ ≤ _ := div_le_div_of_nonneg_right hscaled hd.le

theorem density_fisher_le_dual {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (lam : Fin (n+1) → ℝ) (hlam : IsDualCertificate n lam)
    (M : DensityPOVM (Fin (n+1)) Ω μ) :
    (∫ z, fisherDensity n (spinEdge n) (M.effect z) ∂μ) ≤ dualValue n lam := by
  have hf := (canonical_arbitrary_density_fisher_bound μ n M.effect
    M.positive M.integrable M.complete).1
  have hg : Integrable (fun z => (∑ i, lam i * (M.effect z i i).re) / (n+1)) μ :=
    (integrable_finsetSum _ (fun i _ => (M.integrable i i).re.const_mul (lam i))).div_const _
  calc
    _ ≤ ∫ z, (∑ i, lam i * (M.effect z i i).re) / (n+1) ∂μ :=
      integral_mono hf hg (fun z => psd_fisher_le_dual n lam hlam _ (M.positive z))
    _ = dualValue n lam := by
      rw [integral_div, integral_finsetSum]
      · unfold dualValue
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
        have hre := integral_re (M.integrable i i)
        simp only [RCLike.re_eq_complex_re] at hre
        rw [hre, M.complete]
        simp
      · intro i hi
        exact (M.integrable i i).re.const_mul _

theorem fisherValue_le_dual (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) (r : ℝ) (hr : r ∈ fisherValues n) :
    r ≤ dualValue n lam := by
  obtain ⟨Ω, mΩ, μ, M, rfl⟩ := hr
  exact density_fisher_le_dual μ n lam hlam M

end FiniteCopy.Optimization

