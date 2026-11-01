import FiniteCopy.Algebra
import FiniteCopy.QuantumModel
import FiniteCopy.SpinInterface
import Mathlib.Analysis.Matrix.Order
open scoped BigOperators ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.POVM

lemma psd_diag_nonneg {ι : Type*} [Fintype ι] {E : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (i : ι) : 0 ≤ (E i i).re :=
  (Complex.nonneg_iff.mp hE.diag_nonneg).1

lemma psd_entry_bound {ι : Type*} [Fintype ι] {E : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (i j : ι) :
    ‖E i j‖ ≤ Real.sqrt (E i i).re * Real.sqrt (E j j).re := by
  classical
  let f : Fin 2 → ι := ![i, j]
  have hd := (hE.submatrix f).det_nonneg
  have hre := (Complex.nonneg_iff.mp hd).1
  rw [Matrix.det_fin_two] at hre
  simp only [Matrix.submatrix_apply, f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hre
  have hji : E j i = star (E i j) := by
    have h := congrFun (congrFun hE.isHermitian j) i
    simpa only [Matrix.conjTranspose_apply] using h.symm
  have hii : (E i i).im = 0 := (Complex.nonneg_iff.mp hE.diag_nonneg).2.symm
  have hjj : (E j j).im = 0 := (Complex.nonneg_iff.mp hE.diag_nonneg).2.symm
  rw [hji] at hre
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, hii, hjj, mul_zero, sub_zero] at hre
  have hn : ‖E i j‖ ^ 2 = (E i j).re ^ 2 + (E i j).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 := Real.sq_sqrt (psd_diag_nonneg hE i)
  have hs2 := Real.sq_sqrt (psd_diag_nonneg hE j)
  have hsprod : (Real.sqrt (E i i).re * Real.sqrt (E j j).re)^2 =
      (E i i).re * (E j j).re := by rw [mul_pow, hs1, hs2]
  nlinarith [norm_nonneg (E i j), Real.sqrt_nonneg (E i i).re,
    Real.sqrt_nonneg (E j j).re,
    mul_nonneg (Real.sqrt_nonneg (E i i).re) (Real.sqrt_nonneg (E j j).re)]




open FiniteCopy.Algebra

-- 对越界自然数采用末端延拓；实际有限和只读取 0,…,n。
def vertex (n i : ℕ) : Fin (n+1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma vertex_coe (n : ℕ) (i : Fin (n+1)) : vertex n i.val = i := by
  apply Fin.ext
  simp [vertex, Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)]

lemma sum_vertex (n : ℕ) (f : Fin (n+1) → ℝ) :
    (∑ i ∈ Finset.range (n+1), f (vertex n i)) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [vertex_coe]

def diagonalRoot (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i : ℕ) : ℝ :=
  Real.sqrt (E (vertex n i) (vertex n i)).re

def traceReal {ι : Type*} [Fintype ι] (E : Matrix ι ι ℂ) : ℝ := (Matrix.trace E).re

lemma root_sq (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : E.PosSemidef) (i : ℕ) :
    diagonalRoot n E i ^ 2 = (E (vertex n i) (vertex n i)).re := by
  exact Real.sq_sqrt (psd_diag_nonneg hE _)

lemma root_mass (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : E.PosSemidef) : mass n (diagonalRoot n E) = traceReal E := by
  simp_rw [mass, root_sq n E hE]
  rw [sum_vertex n (fun i => (E i i).re)]
  simp [traceReal, Matrix.trace, Matrix.diag]

def coherence (n : ℕ) (c : ℕ → ℝ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : ℂ :=
  ∑ i ∈ Finset.range n, (c i : ℂ) * E (vertex n i) (vertex n (i+1))

lemma coherence_bound (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef)
    (hc : ∀ i < n, 0 ≤ c i) :
    ‖coherence n c E‖ ≤ moment n c (diagonalRoot n E) := by
  unfold coherence moment
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖(c i : ℂ) * E (vertex n i) (vertex n (i+1))‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc i (Finset.mem_range.mp hi))]
      simpa [diagonalRoot, mul_assoc] using
        mul_le_mul_of_nonneg_left (psd_entry_bound hE (vertex n i) (vertex n (i+1)))
          (hc i (Finset.mem_range.mp hi))

lemma lambda_nonneg (n : ℕ) (a r : ℕ → ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1) (ha : a n = 0) (i : ℕ) (hi : i ≤ n) :
    0 ≤ lambda a r i := by
  have hn : 0 ≤ r (i+1) * a i ^ 2 := by
    by_cases h : i < n
    · exact mul_nonneg (hr (i+1) (by omega)).1 (sq_nonneg _)
    · have he : i = n := by omega
      simp [he, ha]
  cases i with
  | zero => simpa [lambda, previous] using hn
  | succ i =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hr i (by omega)).2) (sq_nonneg _)) hn

-- 对每一个 PSD 效应成立，包含零效应；不作秩或结果数限制。
theorem psd_sos_quotient_bound (n : ℕ) (a r c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1-r i+r (i+1)) = c i)
    (hc0 : ∀ i < n, 0 ≤ c i) (ha : a n = 0) :
    ‖coherence n c E‖ ^ 2 / traceReal E ≤
      ∑ i ∈ Finset.range (n+1), lambda a r i * (E (vertex n i) (vertex n i)).re := by
  have htr : 0 ≤ traceReal E := by
    rw [← root_mass n E hE]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hz : traceReal E = 0
  · rw [hz, div_zero]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (lambda_nonneg n a r hr ha i (by have := Finset.mem_range.mp hi; omega))
      (psd_diag_nonneg hE _)
  · have hp : 0 < traceReal E := lt_of_le_of_ne htr (Ne.symm hz)
    have hm := coherence_bound n c E hE hc0
    have hs := seed_sos_bound n a r c (diagonalRoot n E) hr hc
      (by rw [root_mass n E hE]; exact hp)
    rw [root_mass n E hE, diagonalEnergy_eq n a r _ ha] at hs
    simp_rw [root_sq n E hE] at hs
    have hsq : ‖coherence n c E‖ ^ 2 ≤ moment n c (diagonalRoot n E) ^ 2 := by
      nlinarith [norm_nonneg (coherence n c E)]
    exact (div_le_div_of_nonneg_right hsq (le_of_lt hp)).trans hs





-- 显式复矩阵：自旋跃迁，Jx=(J++J-)/2，Jy=(J+-J-)/(2i)。
def raising (n : ℕ) (c : ℕ → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ∑ i ∈ Finset.range n, Matrix.single (vertex n (i+1)) (vertex n i) (c i : ℂ)

def lowering (n : ℕ) (c : ℕ → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ∑ i ∈ Finset.range n, Matrix.single (vertex n i) (vertex n (i+1)) (c i : ℂ)

def state (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)

def tangentX (n : ℕ) (c : ℕ → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • (raising n c + lowering n c)

def tangentY (n : ℕ) (c : ℕ → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • ((-Complex.I) • (raising n c - lowering n c))

lemma trace_raising (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix.trace (raising n c * E) = coherence n c E := by
  simp [raising, coherence, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul]

lemma trace_lowering (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.IsHermitian) :
    Matrix.trace (lowering n c * E) = star (coherence n c E) := by
  simp only [lowering, coherence, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul,
    star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrFun (congrFun hE (vertex n (i+1))) (vertex n i)
  simpa only [Matrix.conjTranspose_apply, smul_eq_mul, Complex.star_def, mul_comm] using
    congrArg (fun z : ℂ => (c i : ℂ) * z) h.symm

lemma born_state (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    CopyQuantumMetrology.born (state n) E = traceReal E / (n+1 : ℕ) := by
  simp only [CopyQuantumMetrology.born, state, smul_mul, one_mul, Matrix.trace_smul]
  change RCLike.re (((n+1 : ℕ) : ℝ)⁻¹ • Matrix.trace E) = traceReal E / (n+1 : ℕ)
  rw [RCLike.smul_re]
  change ((n+1 : ℕ) : ℝ)⁻¹ * traceReal E = traceReal E / (n+1 : ℕ)
  ring

lemma born_tangentX (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.IsHermitian) :
    CopyQuantumMetrology.born (tangentX n c) E = 2 * (coherence n c E).re / (n+1 : ℕ) := by
  simp only [CopyQuantumMetrology.born, tangentX, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, trace_raising, trace_lowering n c E hE]
  change RCLike.re (((n+1 : ℕ) : ℝ)⁻¹ • (coherence n c E + star (coherence n c E))) = _
  rw [RCLike.smul_re]
  change ((n+1 : ℕ) : ℝ)⁻¹ * (coherence n c E + star (coherence n c E)).re = _
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

lemma born_tangentY (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.IsHermitian) :
    CopyQuantumMetrology.born (tangentY n c) E = 2 * (coherence n c E).im / (n+1 : ℕ) := by
  simp only [CopyQuantumMetrology.born, tangentY, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.trace_smul, Matrix.trace_sub, trace_raising, trace_lowering n c E hE]
  change RCLike.re (((n+1 : ℕ) : ℝ)⁻¹ • ((-Complex.I) * (coherence n c E - star (coherence n c E)))) = _
  rw [RCLike.smul_re]
  change ((n+1 : ℕ) : ℝ)⁻¹ * ((-Complex.I) * (coherence n c E - star (coherence n c E))).re = _
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.sub_im, Complex.star_def, Complex.conj_im, neg_zero, zero_mul, zero_sub]
  ring
-- Fisher trace 密度采用 Born 概率及真实切向的平方商。
def fisherDensity (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : ℝ :=
  ((CopyQuantumMetrology.born (tangentX n c) E)^2 +
    (CopyQuantumMetrology.born (tangentY n c) E)^2) /
      CopyQuantumMetrology.born (state n) E

lemma fisherDensity_formula (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.IsHermitian) :
    fisherDensity n c E = (4 / (n+1 : ℕ)) * ‖coherence n c E‖^2 / traceReal E := by
  rw [fisherDensity, born_state, born_tangentX n c E hE, born_tangentY n c E hE]
  rw [Complex.sq_norm, Complex.normSq_apply]
  by_cases hz : traceReal E = 0
  · simp [hz]
  · have hd : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem psd_fisherDensity_bound (n : ℕ) (a r c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1-r i+r (i+1)) = c i)
    (hc0 : ∀ i < n, 0 ≤ c i) (ha : a n = 0) :
    fisherDensity n c E ≤ (4 / (n+1 : ℕ)) *
      ∑ i ∈ Finset.range (n+1), lambda a r i * (E (vertex n i) (vertex n i)).re := by
  rw [fisherDensity_formula n c E hE.isHermitian, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (psd_sos_quotient_bound n a r c E hE hr hc hc0 ha)
    (by positivity)





lemma psd_traceReal_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : E.PosSemidef) (hz : traceReal E = 0) : E = 0 := by
  have hsum : (∑ i, (E i i).re) = 0 := by
    simpa [traceReal, Matrix.trace, Matrix.diag] using hz
  have hd (i : ι) : (E i i).re = 0 := by
    apply le_antisymm
    · have hh : (E i i).re ≤ ∑ j, (E j j).re :=
        Finset.single_le_sum (fun j _ => psd_diag_nonneg hE j) (Finset.mem_univ i)
      rwa [hsum] at hh
    · exact psd_diag_nonneg hE i
  ext i j
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa [hd i, hd j] using psd_entry_bound hE i j
  · exact norm_nonneg _

lemma born_state_nonneg (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : E.PosSemidef) : 0 ≤ CopyQuantumMetrology.born (state n) E := by
  rw [born_state, ← root_mass n E hE]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by positivity)

lemma born_state_zero_iff (n : ℕ) (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : E.PosSemidef) : CopyQuantumMetrology.born (state n) E = 0 ↔ E = 0 := by
  rw [born_state]
  constructor
  · intro h
    apply psd_traceReal_zero E hE
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · intro h
    simp [h, traceReal]

def bornScore (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : Fin 2 → ℝ :=
  ![CopyQuantumMetrology.born (tangentX n c) E / CopyQuantumMetrology.born (state n) E,
    CopyQuantumMetrology.born (tangentY n c) E / CopyQuantumMetrology.born (state n) E]

lemma fisherDensity_score (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    fisherDensity n c E = CopyQuantumMetrology.born (state n) E *
      ((bornScore n c E 0)^2 + (bornScore n c E 1)^2) := by
  simp only [fisherDensity, bornScore, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  by_cases hp : CopyQuantumMetrology.born (state n) E = 0
  · simp [hp]
  · field_simp
section Integration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma fisherDensity_nonneg (n : ℕ) (c : ℕ → ℝ)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hE : E.PosSemidef) :
    0 ≤ fisherDensity n c E := by
  rw [fisherDensity_formula n c E hE.isHermitian]
  have htr : 0 ≤ traceReal E := by
    rw [← root_mass n E hE]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  positivity

lemma fisherDensity_aestronglyMeasurable (n : ℕ) (c : ℕ → ℝ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ) :
    AEStronglyMeasurable (fun z => fisherDensity n c (E z)) μ := by
  have hb (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
      AEStronglyMeasurable (fun z => CopyQuantumMetrology.born A (E z)) μ :=
    (CopyQuantumMetrology.trace_mul_integrable μ E A hint).re.aestronglyMeasurable
  have hn := ((hb (tangentX n c)).pow 2).add ((hb (tangentY n c)).pow 2)
  exact (hn.aemeasurable.div (hb (state n)).aemeasurable).aestronglyMeasurable
-- 任意测度空间上的完整 PSD 密度；Fisher 可积性由证书推得。
theorem arbitrary_density_fisher_bound (n : ℕ) (a r c : ℕ → ℝ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : ∀ z, (E z).PosSemidef)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ)
    (hcomplete : ∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1-r i+r (i+1)) = c i)
    (hc0 : ∀ i < n, 0 ≤ c i) (ha : a n = 0) :
    Integrable (fun z => fisherDensity n c (E z)) μ ∧
    (∫ z, fisherDensity n c (E z) ∂μ) ≤
      (4 / (n+1 : ℕ)) * ∑ i ∈ Finset.range n, c i * a i := by
  let g : Ω → ℝ := fun z => (4 / (n+1 : ℕ)) *
    ∑ i ∈ Finset.range (n+1), lambda a r i * (E z (vertex n i) (vertex n i)).re
  have hg : Integrable g μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => ((hint (vertex n i) (vertex n i)).re).const_mul _)
  have hbound (z : Ω) : fisherDensity n c (E z) ≤ g z :=
    psd_fisherDensity_bound n a r c (E z) (hE z) hr hc hc0 ha
  have hf : Integrable (fun z => fisherDensity n c (E z)) μ := by
    apply hg.mono' (fisherDensity_aestronglyMeasurable μ n c E hint)
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fisherDensity_nonneg n c (E z) (hE z))]
      exact hbound z)
  constructor
  · exact hf
  · calc
      _ ≤ ∫ z, g z ∂μ := integral_mono hf hg hbound
      _ = _ := by
        dsimp [g]
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_const_mul]
          have hd (i : ℕ) : (∫ z, (E z (vertex n i) (vertex n i)).re ∂μ) = 1 := by
            have hre := integral_re (hint (vertex n i) (vertex n i))
            simp only [RCLike.re_eq_complex_re] at hre
            rw [hre, hcomplete]
            simp
          simp_rw [hd, mul_one]
          rw [lambda_sum n a r c ha hc]
        · intro i hi
          exact ((hint (vertex n i) (vertex n i)).re).const_mul _

-- 真实截顶根的实例；n=0 使用零切向。
theorem canonical_arbitrary_density_fisher_bound (n : ℕ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hE : ∀ z, (E z).PosSemidef)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ)
    (hcomplete : ∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j) :
    Integrable (fun z => fisherDensity n (spinEdge n) (E z)) μ ∧
    (∫ z, fisherDensity n (spinEdge n) (E z) ∂μ) ≤
      (4 / (n+1 : ℕ)) * ∑ i ∈ Finset.range n,
        spinEdge n i * min (spinEdge n i) (NHLowerBound.spinTau n) := by
  by_cases hn : n = 0
  · subst n
    simp [fisherDensity, tangentX, tangentY, raising, lowering, CopyQuantumMetrology.born]
  · have ht := NHLowerBound.spinTau_pos n (Nat.pos_of_ne_zero hn)
    exact arbitrary_density_fisher_bound μ n
      (capA (spinEdge n) (NHLowerBound.spinTau n))
      (capR (spinEdge n) (NHLowerBound.spinTau n)) (spinEdge n) E hE hint hcomplete
      (capR_bounds n _ _ ht (NHLowerBound.spinTau_spec n))
      (fun i _ => cap_coefficient _ _ ht i)
      (fun i _ => spinEdge_nonneg n i)
      (by simp [capA, spinEdge_last, min_eq_left (le_of_lt ht)])

lemma born_density_normalized (n : ℕ)
    (E : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hint : ∀ i j, Integrable (fun z => E z i j) μ)
    (hcomplete : ∀ i j, ∫ z, E z i j ∂μ = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j) :
    (∫ z, CopyQuantumMetrology.born (state n) (E z) ∂μ) = 1 := by
  change (∫ z, (Matrix.trace (state n * E z)).re ∂μ) = 1
  have hre := integral_re (CopyQuantumMetrology.trace_mul_integrable μ E (state n) hint)
  simp only [RCLike.re_eq_complex_re] at hre
  rw [hre, CopyQuantumMetrology.integral_trace_mul μ E (state n) hint hcomplete]
  simp only [state, Matrix.trace_smul, Matrix.trace_one]
  change RCLike.re (((n+1 : ℕ) : ℝ)⁻¹ • (Fintype.card (Fin (n+1)) : ℂ)) = 1
  rw [RCLike.smul_re]
  simp [show (n : ℝ) + 1 ≠ 0 by positivity]
end Integration

section CramerRao
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

-- 二参数 Fisher trace 与协方差 trace 均来自真实概率密度积分。
def statisticalFisherTrace (p : Ω → ℝ) (s : Ω → Fin 2 → ℝ) : ℝ :=
  ∫ z, p z * ((s z 0)^2 + (s z 1)^2) ∂μ

def statisticalCovTrace (p : Ω → ℝ) (u : Ω → Fin 2 → ℝ) : ℝ :=
  ∫ z, p z * ((u z 0 - ∫ w, p w * u w 0 ∂μ)^2 +
    (u z 1 - ∫ w, p w * u w 1 ∂μ)^2) ∂μ

-- 局部无偏矩条件 ∫p u_a s_b=δ_ab；以平方积分直接证明，无需可逆性假设。
theorem cramerRao_trace (p : Ω → ℝ) (s u : Ω → Fin 2 → ℝ)
    (hp : ∀ z, 0 ≤ p z)
    (hu : ∀ a, Integrable (fun z => p z * (u z a)^2) μ)
    (hs : ∀ a, Integrable (fun z => p z * (s z a)^2) μ)
    (hus : ∀ a b, Integrable (fun z => p z * u z a * s z b) μ)
    (hmean : ∀ a, ∫ z, p z * u z a ∂μ = 0)
    (hunbiased : ∀ a b, ∫ z, p z * u z a * s z b ∂μ = if a=b then 1 else 0) :
    0 < statisticalFisherTrace μ p s ∧
      4 / statisticalFisherTrace μ p s ≤ statisticalCovTrace μ p u := by
  let V : ℝ := ∫ z, p z * ((u z 0)^2 + (u z 1)^2) ∂μ
  let F : ℝ := statisticalFisherTrace μ p s
  have hV : 0 ≤ V := integral_nonneg (fun z => mul_nonneg (hp z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hF : 0 ≤ F := integral_nonneg (fun z => mul_nonneg (hp z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hquadratic (t : ℝ) : 0 ≤ V - 4*t + F*t^2 := by
    have hnon : 0 ≤ ∫ z, p z * ((u z 0-t*s z 0)^2 + (u z 1-t*s z 1)^2) ∂μ :=
      integral_nonneg (fun z => mul_nonneg (hp z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hpoint (z : Ω) : p z * ((u z 0-t*s z 0)^2 + (u z 1-t*s z 1)^2) =
        p z * ((u z 0)^2+(u z 1)^2) -
        (2*t) * (p z*u z 0*s z 0+p z*u z 1*s z 1) +
        t^2 * (p z*((s z 0)^2+(s z 1)^2)) := by ring
    have hvint : Integrable (fun z => p z * ((u z 0)^2+(u z 1)^2)) μ := by
      refine ((hu 0).add (hu 1)).congr (Filter.Eventually.of_forall ?_)
      intro z
      dsimp
      ring
    have hfint : Integrable (fun z => p z * ((s z 0)^2+(s z 1)^2)) μ := by
      refine ((hs 0).add (hs 1)).congr (Filter.Eventually.of_forall ?_)
      intro z
      dsimp
      ring
    have hcross : Integrable (fun z => p z*u z 0*s z 0+p z*u z 1*s z 1) μ := by
      refine ((hus 0 0).add (hus 1 1)).congr (Filter.Eventually.of_forall ?_)
      intro z
      rfl
    simp_rw [hpoint] at hnon
    have hsub : Integrable (fun z => p z * ((u z 0)^2+(u z 1)^2) - (2*t)*(p z*u z 0*s z 0+p z*u z 1*s z 1)) μ := by
      exact hvint.sub (hcross.const_mul (2*t))
    rw [integral_add hsub (hfint.const_mul (t^2)),
      integral_sub hvint (hcross.const_mul (2*t)),
      integral_const_mul, integral_add (hus 0 0) (hus 1 1), hunbiased 0 0, hunbiased 1 1,
      integral_const_mul] at hnon
    dsimp [V, F, statisticalFisherTrace] at *
    norm_num at hnon
    nlinarith
  have hFpos : 0 < F := by
    by_contra h
    have hzero : F = 0 := le_antisymm (le_of_not_gt h) hF
    have h := hquadratic (V+1)
    rw [hzero] at h
    nlinarith
  have hbound : 4 / F ≤ V := by
    have h := hquadratic (2/F)
    have he : V - 4*(2/F) + F*(2/F)^2 = V - 4/F := by
      field_simp
      <;> ring
    rw [he] at h
    linarith
  have hcov : statisticalCovTrace μ p u = V := by
    simp [statisticalCovTrace, hmean, V]
  exact ⟨hFpos, hcov ▸ hbound⟩

end CramerRao
end FiniteCopy.POVM







