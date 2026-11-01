import FiniteCopy.GradientBounds
import FiniteCopy.Width
open MeasureTheory Set

namespace CopyQuantumMetrology.GradientBounds

set_option maxHeartbeats 800000

open GlobalBounds

lemma edge_interval_bound {J m s : ℝ} (hm : |m| ≤ J-1/2)
    (hm₁ : |m+1| ≤ J-1/2) (hs : s ∈ Icc m (m+1)) : |s| ≤ J-1/2 := by
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  obtain ⟨hm₁l, hm₁u⟩ := abs_le.mp hm₁
  exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩

lemma edge_coefficient_product_le {J m s : ℝ} (hJ : 0 < J)
    (hm : |m| ≤ J-1/2) (hm₁ : |m+1| ≤ J-1/2) (hs : s ∈ Icc m (m+1)) :
    q J (m+1/2)*Real.sqrt (J^2-s^2) ≤ 4*J*(J-|s|) := by
  have hsJ := edge_interval_bound hm hm₁ hs
  have hmJ := edge_interval_bound hm hm₁ (s := m+1/2) (by constructor <;> linarith)
  have hrad := Width.radial_bounds hJ (show |s| ≤ J by linarith)
  have hradm := Width.radial_bounds hJ (show |m+1/2| ≤ J by linarith)
  have hnear : |s|-|m+1/2| ≤ 1/2 := by
    have h := abs_sub_abs_le_abs_sub s (m+1/2)
    have hn : |s-(m+1/2)| ≤ 1/2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact h.trans hn
  have hcs : q J (m+1/2)^2 ≤ 4*J*(J-|s|) := by
    rw [q_sq, max_eq_left (by nlinarith [abs_nonneg (m+1/2)] : 0 ≤ J^2-(m+1/2)^2)]
    have h := mul_le_mul_of_nonneg_left (show J-|m+1/2| ≤ 2*(J-|s|) by linarith) hJ.le
    nlinarith only [hradm.2, h]
  have hBs : (Real.sqrt (J^2-s^2))^2 = J^2-s^2 := Real.sq_sqrt (by nlinarith [abs_nonneg s])
  nlinarith [sq_nonneg (q J (m+1/2)-Real.sqrt (J^2-s^2)),
    mul_nonneg hJ.le (show 0 ≤ J-|s| by linarith)]

-- 直接接入原始正则化方差及其真实参数导数。
theorem regularized_edge_derivative_uniform {J m s ε : ℝ} (hJ : 0 < J)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : |m| ≤ J-1/2)
    (hm₁ : |m+1| ≤ J-1/2) (hs : s ∈ Icc m (m+1)) :
    q J (m+1/2) *
      (∫ t, q J t * movingDeriv s (Width.width J ε s) (Width.width₁ J ε s) t^2) ≤
      (4096/ε^7)*J := by
  have hsJ := edge_interval_bound hm hm₁ hs
  have hsJ' : |s| ≤ J := by linarith
  have he := gaussian_edge_derivative_uniform (S₁ := Width.width₁ J ε s) hJ
    (show 1/2 ≤ J-|s| by linarith) hsJ' (show J-|s| ≤ J by linarith [abs_nonneg s])
    (Width.radial_bounds hJ hsJ').1 (Width.width_lower hJ hε hε1 hsJ')
    (q_nonneg J (m+1/2)) (edge_coefficient_product_le hJ hm hm₁ hs)
  have hd := Width.width₁_bound hJ hε hε1 hsJ'
  have hds : (Width.width₁ J ε s)^2 ≤ (2/ε^3)^2 := by
    nlinarith [sq_abs (Width.width₁ J ε s), abs_nonneg (Width.width₁ J ε s)]
  have hc : 40+768*(Width.width₁ J ε s)^2 ≤ 4096/ε^7 := by
    have hp : ε^7 ≤ 1 := pow_le_one₀ hε.le hε1
    apply le_trans (show 40+768*(Width.width₁ J ε s)^2 ≤ 40+768*(2/ε^3)^2 by linarith)
    apply (le_div_iff₀ (pow_pos hε 7)).2
    field_simp
    nlinarith only [hp, hε1]
  exact he.trans (mul_le_mul_of_nonneg_right hc hJ.le)

lemma q_eq_zero_outside {J t : ℝ} (hJ : 0 ≤ J) (ht : t ∉ Icc (-J) J) : q J t = 0 := by
  have hh : J^2-t^2 ≤ 0 := by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht <;> nlinarith
  unfold q
  rw [max_eq_right hh, Real.sqrt_zero]

lemma integrable_q_mul {J : ℝ} (hJ : 0 ≤ J) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun t => q J t*f t) := by
  have hi : IntegrableOn (fun t => q J t*f t) (Icc (-J) J) volume :=
    ((continuous_q J).mul hf).continuousOn.integrableOn_compact isCompact_Icc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro t ht
  rw [q_eq_zero_outside hJ ht, zero_mul]

-- 联合可积性由紧参数区间与 q 的紧支集自动给出。
lemma integrable_q_mul_strip {J a : ℝ} (hJ : 0 ≤ J) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f ((Icc a (a+1)) ×ˢ (Icc (-J) J))) :
    Integrable (fun p : ℝ × ℝ => q J p.2*f p)
      ((volume.restrict (Ioc a (a+1))).prod volume) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => q J p.2*f p)
      ((Icc a (a+1)) ×ˢ (Icc (-J) J)) :=
    ((continuous_q J).comp continuous_snd).continuousOn.mul hf
  have hi := hc.integrableOn_compact (μ := volume.prod volume) (isCompact_Icc.prod isCompact_Icc)
  have hi' : IntegrableOn (fun p : ℝ × ℝ => q J p.2*f p)
      ((Ioc a (a+1)) ×ˢ (Icc (-J) J)) (volume.prod volume) :=
    hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
  have hir : Integrable (fun p : ℝ × ℝ => q J p.2*f p)
      ((volume.restrict (Ioc a (a+1))).prod (volume.restrict (Icc (-J) J))) := by
    rwa [Measure.prod_restrict]
  have hiu : IntegrableOn (fun p : ℝ × ℝ => q J p.2*f p)
      (univ ×ˢ (Icc (-J) J)) ((volume.restrict (Ioc a (a+1))).prod volume) := by
    unfold IntegrableOn
    rwa [← Measure.prod_restrict, Measure.restrict_univ]
  apply hiu.integrable_of_forall_notMem_eq_zero
  intro p hp
  have hp' : p.2 ∉ Icc (-J) J := by simpa only [mem_prod, mem_univ, true_and] using hp
  rw [q_eq_zero_outside hJ hp', zero_mul]

lemma continuous_column_sample (s S : ℝ) : Continuous (column s S) := by
  unfold column
  fun_prop

lemma continuousOn_movingDeriv {S S₁ : ℝ → ℝ} {a : ℝ}
    (hS : ContinuousOn S (Icc a (a+1))) (hS₁ : ContinuousOn S₁ (Icc a (a+1)))
    (hpos : ∀ s ∈ Icc a (a+1), 0 < S s) :
    ContinuousOn (fun p : ℝ × ℝ => movingDeriv p.1 (S p.1) (S₁ p.1) p.2)
      ((Icc a (a+1)) ×ˢ univ) := by
  have hSc : ContinuousOn (fun p : ℝ × ℝ => S p.1) ((Icc a (a+1)) ×ˢ univ) :=
    hS.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hS₁c : ContinuousOn (fun p : ℝ × ℝ => S₁ p.1) ((Icc a (a+1)) ×ˢ univ) :=
    hS₁.comp continuous_fst.continuousOn (fun p hp => hp.1)
  intro p hp
  have hScp := hSc p hp
  have hS₁cp := hS₁c p hp
  have hsp := hpos p.1 hp.1
  have hz : ContinuousWithinAt (fun p : ℝ × ℝ => p.2-p.1) ((Icc a (a+1)) ×ˢ univ) p :=
    continuous_snd.continuousWithinAt.sub continuous_fst.continuousWithinAt
  have hn := (hScp.const_mul (2*Real.pi)).rpow_const
    (Or.inl (show 2*Real.pi*S p.1 ≠ 0 by positivity) :
      2*Real.pi*S p.1 ≠ 0 ∨ 0 ≤ (-1/4 : ℝ))
  have he := (((hz.pow 2).neg).div (hScp.const_mul 4)
    (show 4*S p.1 ≠ 0 by positivity)).rexp
  have hscore := (hz.div (hScp.const_mul 2) (show 2*S p.1 ≠ 0 by positivity)).add
    ((hS₁cp.div (hScp.const_mul 4) (show 4*S p.1 ≠ 0 by positivity)).mul
      (((hz.pow 2).div hScp hsp.ne').sub_const 1))
  unfold movingDeriv column
  exact (hn.mul he).mul hscore

-- 实际 G_m：导数、FTC、Cauchy–Schwarz、Fubini 与高斯矩全部已经接通。
theorem regularized_gradient_uniform {J m ε : ℝ} (hJ : 0 < J)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : |m| ≤ J-1/2) (hm₁ : |m+1| ≤ J-1/2) :
    q J (m+1/2) * (∫ t, q J t *
      (column (m+1) (Width.width J ε (m+1)) t-column m (Width.width J ε m) t)^2) ≤
      (4096/ε^7)*J := by
  let v := fun s t => column s (Width.width J ε s) t
  let D := fun s t => movingDeriv s (Width.width J ε s) (Width.width₁ J ε s) t
  have hpos : ∀ s ∈ Icc m (m+1), 0 < Width.width J ε s := by
    intro s hs
    apply Width.width_pos hJ hε
    linarith [edge_interval_bound hm hm₁ hs]
  have hDc : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) ((Icc m (m+1)) ×ˢ univ) :=
    continuousOn_movingDeriv (Width.continuous_width hJ.ne' hε).continuousOn
      (Width.continuous_width₁ hε).continuousOn hpos
  have hprod : Integrable (fun p : ℝ × ℝ => q J p.2*D p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) :=
    integrable_q_mul_strip hJ.le ((hDc.pow 2).mono (Set.prod_mono Subset.rfl (subset_univ _)))
  have hv : ∀ t s, s ∈ Icc m (m+1) → HasDerivAt (fun s => v s t) (D s t) s := by
    intro t s hs
    simpa only [v, D, movingDeriv] using
      hasDerivAt_column_moving t (Width.hasDerivAt_width hJ.ne' hε s) (hpos s hs)
  have hD : ∀ t, ContinuousOn (fun s => D s t) (Icc m (m+1)) := by
    intro t
    have hpair : Continuous (fun s : ℝ => (s,t)) := continuous_id.prodMk continuous_const
    exact hDc.comp (f := fun s : ℝ => (s,t)) hpair.continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have hfinite : Integrable (fun t => q J t*(v (m+1) t-v m t)^2) :=
    integrable_q_mul hJ.le (((continuous_column_sample _ _).sub (continuous_column_sample _ _)).pow 2)
  have he := weighted_finite_difference_le m (q_nonneg J) hv hD hfinite hprod
  calc
    _ ≤ q J (m+1/2)*(∫ s in Ioc m (m+1), ∫ t, q J t*D s t^2) :=
      mul_le_mul_of_nonneg_left he (q_nonneg J (m+1/2))
    _ = ∫ s in Ioc m (m+1), q J (m+1/2)*(∫ t, q J t*D s t^2) := by
      rw [integral_const_mul]
    _ ≤ ∫ _s in Ioc m (m+1), (4096/ε^7)*J := by
      apply setIntegral_mono_on (hprod.integral_prod_left.const_mul _)
        (integrableOn_const (hs := by simp)) measurableSet_Ioc
      intro s hs
      exact regularized_edge_derivative_uniform hJ hε hε1 hm hm₁ ⟨hs.1.le, hs.2⟩
    _ = _ := by
      simp only [setIntegral_const, Real.volume_real_Ioc_of_le (show m ≤ m+1 by linarith)]
      ring

end CopyQuantumMetrology.GradientBounds

