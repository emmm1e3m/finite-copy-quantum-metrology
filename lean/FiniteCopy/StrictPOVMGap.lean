import FiniteCopy.POVMLower
import FiniteCopy.SeedNormalization

open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
open FiniteCopy.Algebra

noncomputable section
namespace FiniteCopy.POVM

-- 任意 PSD 效应的 coherence 商被对角平方根种子商支配。
lemma psd_quotient_le_root_seed (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef)
    (hc : ∀ i < n, 0 ≤ c i) :
    ‖coherence n c E‖^2 / traceReal E ≤
      moment n c (diagonalRoot n E)^2 / mass n (diagonalRoot n E) := by
  rw [root_mass n E hE]
  have htr : 0 ≤ traceReal E := by
    rw [← root_mass n E hE]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb := coherence_bound n c E hE hc
  have hs : ‖coherence n c E‖^2 ≤ moment n c (diagonalRoot n E)^2 := by
    nlinarith [norm_nonneg (coherence n c E)]
  exact div_le_div_of_nonneg_right hs htr

def diagonalWeight (n : ℕ) (w : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), w i * (E (vertex n i) (vertex n i)).re

lemma diagonalWeight_one (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    diagonalWeight n (fun _ => 1) E = traceReal E := by
  simp only [diagonalWeight, one_mul]
  rw [sum_vertex n (fun i => (E i i).re)]
  simp [traceReal, Matrix.trace, Matrix.diag]

-- 该接口只做积分传递；物理 spin 的统一逐点余量在下方实际实例化。
lemma psd_refined_quotient_bound (n : ℕ) (a r c : ℕ → ℝ) (q ε δ : ℝ)
    (hc : ∀ i < n, 0 ≤ c i) (ha : a n = 0)
    (hmargin : ∀ v : ℕ → ℝ, (∀ i ≤ n, 0 ≤ v i) →
      δ * (v 1^2-q^2*v 2^2-ε*mass n v) ≤
        diagonalEnergy n a r v - moment n c v^2 / mass n v)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef) :
    ‖coherence n c E‖^2 / traceReal E ≤ diagonalWeight n (lambda a r) E -
      δ * ((E (vertex n 1) (vertex n 1)).re -
        q^2*(E (vertex n 2) (vertex n 2)).re - ε*traceReal E) := by
  have hm := hmargin (diagonalRoot n E) (fun i _ => Real.sqrt_nonneg _)
  rw [diagonalEnergy_eq n a r _ ha] at hm
  simp_rw [root_sq n E hE, root_mass n E hE] at hm
  have hs := psd_quotient_le_root_seed n c E hE hc
  rw [root_mass n E hE] at hs
  dsimp [diagonalWeight]
  linarith

section Integration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma diagonalWeight_integrable (n : ℕ) (w : ℕ → ℝ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ) :
    Integrable (fun z => diagonalWeight n w (E z)) μ := by
  exact integrable_finsetSum _ (fun i _ => (hint (vertex n i) (vertex n i)).re.const_mul _)

lemma integral_diagonalWeight (n : ℕ) (w : ℕ → ℝ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ)
    (hcomplete : ∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j) :
    (∫ z, diagonalWeight n w (E z) ∂μ) = ∑ i ∈ Finset.range (n+1), w i := by
  unfold diagonalWeight
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    have hre := integral_re (hint (vertex n i) (vertex n i))
    simp only [RCLike.re_eq_complex_re] at hre
    rw [hre, hcomplete]
    simp
  · intro i hi
    exact (hint (vertex n i) (vertex n i)).re.const_mul _

-- 结果空间任意，统一余量只依赖 n，不依赖测量及其结果基数。
theorem arbitrary_density_refined_fisher_bound (n : ℕ) (a r c : ℕ → ℝ)
    (q ε δ : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i*(1-r i+r (i+1)) = c i)
    (hc0 : ∀ i < n, 0 ≤ c i) (ha : a n = 0)
    (hmargin : ∀ v : ℕ → ℝ, (∀ i ≤ n, 0 ≤ v i) →
      δ * (v 1^2-q^2*v 2^2-ε*mass n v) ≤
        diagonalEnergy n a r v - moment n c v^2 / mass n v)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : ∀ z, (E z).PosSemidef)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ)
    (hcomplete : ∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j) :
    (∫ z, fisherDensity n c (E z) ∂μ) ≤
      (4/(n+1 : ℕ)) * ((∑ i ∈ Finset.range n, c i*a i) -
        δ*(1-q^2-ε*(n+1 : ℕ))) := by
  have hf := (arbitrary_density_fisher_bound μ n a r c E hE hint hcomplete hr hc hc0 ha).1
  have hd := diagonalWeight_integrable μ n (lambda a r) E hint
  have ht : Integrable (fun z => traceReal (E z)) μ := by
    simpa only [diagonalWeight_one] using diagonalWeight_integrable μ n (fun _ => 1) E hint
  have h1 : Integrable (fun z => (E z (vertex n 1) (vertex n 1)).re) μ := (hint (vertex n 1) (vertex n 1)).re
  have h2 : Integrable (fun z => (E z (vertex n 2) (vertex n 2)).re) μ := (hint (vertex n 2) (vertex n 2)).re
  have h12 : Integrable (fun z => (E z (vertex n 1) (vertex n 1)).re-q^2*(E z (vertex n 2) (vertex n 2)).re) μ := h1.sub (h2.const_mul _)
  have hpop : Integrable (fun z => (E z (vertex n 1) (vertex n 1)).re-q^2*(E z (vertex n 2) (vertex n 2)).re-ε*traceReal (E z)) μ := h12.sub (ht.const_mul _)
  let g : Ω → ℝ := fun z => (4/(n+1 : ℕ)) * (diagonalWeight n (lambda a r) (E z) -
    δ*((E z (vertex n 1) (vertex n 1)).re-q^2*(E z (vertex n 2) (vertex n 2)).re-ε*traceReal (E z)))
  have hg : Integrable g μ := (hd.sub (hpop.const_mul δ)).const_mul _
  have hb (z : Ω) : fisherDensity n c (E z) ≤ g z := by
    rw [fisherDensity_formula n c (E z) (hE z).isHermitian, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (psd_refined_quotient_bound n a r c q ε δ hc0 ha hmargin (E z) (hE z))
      (by positivity)
  have hdiag (i : ℕ) : (∫ z, (E z (vertex n i) (vertex n i)).re ∂μ) = 1 := by
    have hre := integral_re (hint (vertex n i) (vertex n i))
    simp only [RCLike.re_eq_complex_re] at hre
    rw [hre, hcomplete]
    simp
  have htrace : (∫ z, traceReal (E z) ∂μ) = (n+1 : ℕ) := by
    have h := integral_diagonalWeight μ n (fun _ => 1) E hint hcomplete
    simpa only [diagonalWeight_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using h
  calc
    _ ≤ ∫ z, g z ∂μ := integral_mono hf hg hb
    _ = _ := by
      dsimp [g]
      rw [integral_const_mul,
        integral_sub hd (hpop.const_mul δ),
        integral_const_mul,
        integral_sub h12 (ht.const_mul ε),
        integral_sub h1 (h2.const_mul (q^2)), integral_const_mul, integral_const_mul,
        hdiag, hdiag, htrace, integral_diagonalWeight μ n (lambda a r) E hint hcomplete,
        lambda_sum n a r c ha hc]
      ring

end Integration




-- 将026紧集上的统一余量齐次化，包含零质量种子。
lemma normalized_diagonal_scaled (n : ℕ) (a r v : ℕ → ℝ) (hm : 0 < mass n v) :
    mass n v * diagonalEnergy n a r (FiniteCopy.Gap.normalizeSeed n v) = diagonalEnergy n a r v := by
  unfold diagonalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hi1 : i+1 ≤ n := by have := Finset.mem_range.mp hi; omega
  have hp0 := FiniteCopy.Gap.normalizeSeed_population n v hm i hi0
  have hp1 := FiniteCopy.Gap.normalizeSeed_population n v hm (i+1) hi1
  calc
    _ = r (i+1)*a i^2*(mass n v*FiniteCopy.Gap.normalizeSeed n v i^2) +
      (1-r i)*a i^2*(mass n v*FiniteCopy.Gap.normalizeSeed n v (i+1)^2) := by ring
    _ = _ := by rw [hp0, hp1]

theorem spin_unnormalized_uniform_defect (n : ℕ) (hn : 10 ≤ n) (τ ε : ℝ) (hε : 0 < ε)
    (hroot : (∑ i ∈ Finset.range n, FiniteCopy.Gap.cap (FiniteCopy.Gap.coeff n i) τ) = τ) :
    ∃ δ > 0, ∀ v : ℕ → ℝ, (∀ i ≤ n, 0 ≤ v i) →
      δ * (v 1^2-(FiniteCopy.Gap.coeff n 1/τ)^2*v 2^2-ε*mass n v) ≤
        diagonalEnergy n (capA (FiniteCopy.Gap.coeff n) τ) (capR (FiniteCopy.Gap.coeff n) τ) v -
          moment n (FiniteCopy.Gap.coeff n) v^2 / mass n v := by
  obtain ⟨δ, hδ, hbound⟩ := FiniteCopy.Gap.spin_uniform_defect n hn τ ε hε hroot
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  have hm0 : 0 ≤ mass n v := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hz : mass n v = 0
  · have hvzero (i : ℕ) (hi : i ≤ n) : v i = 0 := by
      have hs : v i^2 ≤ mass n v := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      rw [hz] at hs
      nlinarith [sq_nonneg (v i)]
    have hd : diagonalEnergy n (capA (FiniteCopy.Gap.coeff n) τ) (capR (FiniteCopy.Gap.coeff n) τ) v = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hin := Finset.mem_range.mp hi
      rw [hvzero i (by omega), hvzero (i+1) (by omega)]
      ring
    rw [hz, hd, hvzero 1 (by omega), hvzero 2 (by omega)]
    simp
  · have hm : 0 < mass n v := lt_of_le_of_ne hm0 (Ne.symm hz)
    have hb := hbound (FiniteCopy.Gap.normalizeSeed n v) (FiniteCopy.Gap.normalizeSeed_mem n v hm hv)
    have hmul := mul_le_mul_of_nonneg_left hb hm.le
    have hp1 := FiniteCopy.Gap.normalizeSeed_population n v hm 1 (by omega)
    have hp2 := FiniteCopy.Gap.normalizeSeed_population n v hm 2 (by omega)
    have hd := normalized_diagonal_scaled n (capA (FiniteCopy.Gap.coeff n) τ) (capR (FiniteCopy.Gap.coeff n) τ) v hm
    have ho := FiniteCopy.Gap.normalizeSeed_objective n (FiniteCopy.Gap.coeff n) v hm
    dsimp [FiniteCopy.Gap.tailPopulation, FiniteCopy.Gap.spinDefect] at hmul
    have hleft : mass n v * (δ * (FiniteCopy.Gap.normalizeSeed n v 1^2 -
        (FiniteCopy.Gap.coeff n 1/τ)^2*FiniteCopy.Gap.normalizeSeed n v 2^2 - ε)) =
        δ*(v 1^2-(FiniteCopy.Gap.coeff n 1/τ)^2*v 2^2-ε*mass n v) := by
      calc
        _ = δ*(mass n v*FiniteCopy.Gap.normalizeSeed n v 1^2 -
          (FiniteCopy.Gap.coeff n 1/τ)^2*(mass n v*FiniteCopy.Gap.normalizeSeed n v 2^2) - ε*mass n v) := by ring
        _ = _ := by rw [hp1, hp2]
    rw [hleft] at hmul
    rw [mul_sub (mass n v) _ _, hd, ho] at hmul
    exact hmul

-- 对每个 n≥10，实际截顶证书与所有完整PSD密度之间存在统一正 Fisher 缺口。
theorem canonical_arbitrary_density_fisher_strict_gap (n : ℕ) (hn : 10 ≤ n) :
    ∃ Δ > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
      (∀ z, (E z).PosSemidef) →
      (∀ i j, Integrable (fun z => E z i j) μ) →
      (∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j) →
      (∫ z, fisherDensity n (spinEdge n) (E z) ∂μ) ≤
        (4/(n+1 : ℕ)) * (∑ i ∈ Finset.range n,
          spinEdge n i * min (spinEdge n i) (NHLowerBound.spinTau n)) - Δ := by
  let τ := NHLowerBound.spinTau n
  let q := FiniteCopy.Gap.coeff n 1 / τ
  let g := 1-q^2
  let d : ℝ := (n+1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hτ : 0 < τ := NHLowerBound.spinTau_pos n (by omega)
  have hroot : (∑ i ∈ Finset.range n, FiniteCopy.Gap.cap (FiniteCopy.Gap.coeff n i) τ) = τ :=
    NHLowerBound.spinTau_spec n
  have hq0 : 0 ≤ q := div_nonneg (FiniteCopy.Gap.coeff_nonneg n 1) hτ.le
  have hq1 : q < 1 := (div_lt_one hτ).2 (FiniteCopy.Gap.cap_root_gt_first_inner_edge n hn τ hroot)
  have hg : 0 < g := by dsimp [g]; nlinarith
  obtain ⟨δ, hδ, hmargin⟩ := spin_unnormalized_uniform_defect n hn τ (g/(2*d)) (by positivity) hroot
  refine ⟨(4/d)*(δ*g/2), by positivity, ?_⟩
  intro Ω _ μ E hE hint hcomplete
  have ha : capA (spinEdge n) τ n = 0 := by simp [capA, spinEdge_last, min_eq_left hτ.le]
  have hb := arbitrary_density_refined_fisher_bound μ n (capA (spinEdge n) τ)
    (capR (spinEdge n) τ) (spinEdge n) q (g/(2*d)) δ
    (capR_bounds n _ _ hτ (NHLowerBound.spinTau_spec n))
    (fun i _ => cap_coefficient _ _ hτ i) (fun i _ => spinEdge_nonneg n i) ha
    hmargin E hE hint hcomplete
  have he : (4/d)*((∑ i ∈ Finset.range n, spinEdge n i*capA (spinEdge n) τ i) -
      δ*(1-q^2-g/(2*d)*d)) = (4/d)*(∑ i ∈ Finset.range n, spinEdge n i*capA (spinEdge n) τ i) -
      (4/d)*(δ*g/2) := by
    dsimp [g]
    field_simp
    ring
  exact hb.trans_eq he

end FiniteCopy.POVM


