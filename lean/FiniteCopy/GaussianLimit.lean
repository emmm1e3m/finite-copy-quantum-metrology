import FiniteCopy.ContinuousEnergy
import FiniteCopy.EndpointBounds
import FiniteCopy.EnergyAssembly
import FiniteCopy.Width
import FiniteCopy.RegularizedGradient
import FiniteCopy.FiniteDifferenceEnergy
import FiniteCopy.SecondDerivative
import FiniteCopy.PositionUniform
import FiniteCopy.BulkParameters

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CopyQuantumMetrology.GaussianLimit


/-- 统一自然数与 Fin 两种自旋坐标表示。 -/
theorem spinJ_eq (n : ℕ) : GlobalBounds.spinJ n = spinJ n := rfl

theorem spinM_eq (n : ℕ) (i : Fin (n+1)) : GlobalBounds.spinM n i = spinM n i := rfl

theorem spinWidth_eq_width (n : ℕ) (eps : ℝ) (i : Fin (n+1)) :
    spinWidth n eps i = Width.width (spinJ n) eps (spinM n i) := by
  rw [spinWidth_eq_paper]
  unfold Width.width Width.profile Width.root
  ring

theorem width_eq_global (J eps m : ℝ) :
    Width.width J eps m = GlobalBounds.width J m (GlobalBounds.regularizedWidth eps (m/J)) := by
  unfold Width.width Width.profile Width.root GlobalBounds.width GlobalBounds.regularizedWidth
  ring

theorem spinPoint_eq (n i : ℕ) :
    RateFunctional.spinPoint (n+1) i = GlobalBounds.spinM n i / spinJ n := by
  rw [RateFunctional.spinPoint_physical (Nat.succ_pos n)]
  unfold GlobalBounds.spinM spinJ
  push_cast
  congr 2
  ring

theorem positionProfile_eq (eps x : ℝ) :
    RateFunctional.positionProfile eps x = x^2 * GlobalBounds.regularizedWidth eps x := rfl

theorem gradientProfile_eq (eps x : ℝ) :
    RateFunctional.gradientProfile eps x = Real.sqrt (x^2+eps^2)/2 := by
  unfold RateFunctional.gradientProfile RateFunctional.width
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_inv]
  ring

theorem I_eq_regularized (n : ℕ) (eps : ℝ) (i : ℕ) (hi : i ≤ n) :
    ContinuousEnergy.I n eps i = ∫ t, (GlobalBounds.k (spinJ n) (GlobalBounds.spinM n i) - GlobalBounds.q (spinJ n) t)^2 *
      column (GlobalBounds.spinM n i) (Width.width (spinJ n) eps (GlobalBounds.spinM n i)) t^2 := by
  have h := ContinuousEnergy.I_eq_gaussian n eps ⟨i, by omega⟩
  rw [spinWidth_eq_width] at h
  exact h

theorem I_nonneg (n : ℕ) (eps : ℝ) (i : ℕ) : 0 ≤ ContinuousEnergy.I n eps i :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem G_eq_regularized (n : ℕ) (eps : ℝ) (i : ℕ) (hi : i < n) :
    ContinuousEnergy.G n eps i =
      GlobalBounds.q (spinJ n) (GlobalBounds.spinM n i + 1/2) *
      ∫ t, GlobalBounds.q (spinJ n) t *
        (column (GlobalBounds.spinM n i + 1)
          (Width.width (spinJ n) eps (GlobalBounds.spinM n i + 1)) t -
         column (GlobalBounds.spinM n i)
          (Width.width (spinJ n) eps (GlobalBounds.spinM n i)) t)^2 := by
  unfold ContinuousEnergy.G
  simp_rw [ContinuousEnergy.spinV_eq n eps _ (i+1) (by omega),
    ContinuousEnergy.spinV_eq n eps _ i (by omega), spinColumn, spinWidth_eq_width]
  have hnxt : spinM n ⟨i+1, by omega⟩ = GlobalBounds.spinM n i + 1 := by
    unfold spinM GlobalBounds.spinM
    push_cast
    ring
  simp_rw [hnxt]
  rw [← ContinuousEnergy.q_right_eq_spinEdge n i (by omega), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold spinM GlobalBounds.spinM
  ring

theorem G_nonneg (n : ℕ) (eps : ℝ) (i : ℕ) : 0 ≤ ContinuousEnergy.G n eps i :=
  integral_nonneg (fun _ => mul_nonneg
    (mul_nonneg (GlobalBounds.q_nonneg _ _) (FiniteCopy.Algebra.spinEdge_nonneg n i)) (sq_nonneg _))

theorem I_global {n : ℕ} {eps : ℝ} (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (i : ℕ) (hi : i ≤ n) : ContinuousEnergy.I n eps i / spinJ n ≤ 14 / eps^2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ (spinJ_pos n)).2
  rw [I_eq_regularized n eps i hi, width_eq_global]
  exact GlobalBounds.gaussian_energy_regularized (by unfold spinJ; linarith) heps heps1
    (GlobalBounds.spinM_abs_le hi)

theorem G_global {n : ℕ} {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (i : ℕ) (hi : i < n) : ContinuousEnergy.G n eps i / spinJ n ≤ 4096 / eps^7 := by
  apply (div_le_iff₀ (spinJ_pos n)).2
  rw [G_eq_regularized n eps i hi]
  have hnxt : GlobalBounds.spinM n (i+1) = GlobalBounds.spinM n i + 1 := by
    unfold GlobalBounds.spinM
    push_cast
    ring
  apply GradientBounds.regularized_gradient_uniform (spinJ_pos n) heps heps1
    (GlobalBounds.spinM_abs_le (by omega))
  rw [← hnxt]
  exact GlobalBounds.spinM_abs_le (by omega)

theorem R_eq_correction (n i : ℕ) (hi : i ≤ n) :
    ContinuousEnergy.R n i = GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i) := by
  unfold ContinuousEnergy.R GlobalBounds.correction GlobalBounds.spinM
  rw [spinJ_eq, ContinuousEnergy.q_right_eq_spinEdge n i hi, ContinuousEnergy.q_left_eq_previous n i hi]

theorem correction_error {n : ℕ} (hn : 1 ≤ n) :
    |(∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i) / ((n+1 : ℕ) * spinJ n)| ≤
      2 * (1 + Real.log (n+1 : ℕ)) / spinJ n := by
  have hn0 : 0 ≤ (∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i) := by
    apply Finset.sum_nonneg
    intro i hi
    unfold ContinuousEnergy.R
    positivity
  rw [abs_of_nonneg (div_nonneg hn0 (mul_nonneg (by positivity) (spinJ_pos n).le))]
  have he : (∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i) =
      ∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact R_eq_correction n i (by simpa using hi)
  rw [he]
  exact GlobalBounds.normalized_correction_le_log hn

theorem U_normalize (n : ℕ) (eps : ℝ) :
    ContinuousEnergy.U n eps / spinJ n =
      ((∑ i ∈ Finset.range (n+1), ContinuousEnergy.I n eps i / spinJ n) +
        (∑ i ∈ Finset.range n, ContinuousEnergy.G n eps i / spinJ n)) / (n+1 : ℕ) +
      (∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i) / ((n+1 : ℕ) * spinJ n) := by
  simpa only [ContinuousEnergy.U, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
    RateFunctional.raw_energy_normalize (n+1) (spinJ n) (ContinuousEnergy.I n eps) (ContinuousEnergy.G n eps) (ContinuousEnergy.R n)

theorem good_column_scaled {n i : ℕ} {delta : ℝ} (hi : i ≤ n)
    (hb : i ∉ GlobalBounds.endpointColumns n delta) :
    |GlobalBounds.spinM n i / spinJ n| ≤ 1-delta := by
  have hb' : |GlobalBounds.spinM n i| ≤ (1-delta) * spinJ n := by
    by_contra h
    apply hb
    exact GlobalBounds.mem_endpointColumns.2 ⟨hi, lt_of_not_ge h⟩
  rw [abs_div, abs_of_pos (spinJ_pos n)]
  exact (div_le_iff₀ (spinJ_pos n)).2 hb'

theorem good_edge_columns {n i : ℕ} {delta : ℝ} (hi : i < n)
    (hb : i ∉ GlobalBounds.endpointEdges n delta) :
    i ∉ GlobalBounds.endpointColumns n delta ∧ i+1 ∉ GlobalBounds.endpointColumns n delta := by
  classical
  simpa only [GlobalBounds.endpointEdges, Finset.mem_filter, Finset.mem_range, hi, true_and,
    not_or] using hb

theorem bulk_interval_scaled {J m delta s : ℝ} (hJ : 0 < J)
    (hm : |m/J| ≤ 1-delta) (hm1 : |(m+1)/J| ≤ 1-delta)
    (hs : s ∈ Icc m (m+1)) : |s/J| ≤ 1-delta := by
  rw [abs_div, abs_of_pos hJ] at hm hm1 ⊢
  apply (div_le_iff₀ hJ).2
  have hml := abs_le.1 ((div_le_iff₀ hJ).1 hm)
  have hmr := abs_le.1 ((div_le_iff₀ hJ).1 hm1)
  exact abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩

set_option maxHeartbeats 500000 in
/-- 从真实二阶导数矩到真实有限差分；端点与尾部均不另作截断。 -/
theorem regularized_difference_error {J m eps delta η : ℝ}
    (hJ : 1 ≤ J) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hη : 0 < η)
    (hm : |m| ≤ J-1/2) (hm1 : |m+1| ≤ J-1/2)
    (hmb : |m/J| ≤ 1-delta) (hm1b : |(m+1)/J| ≤ 1-delta) :
    |GlobalBounds.q J (m+1/2) *
        (∫ t, GlobalBounds.q J t *
          (column (m+1) (Width.width J eps (m+1)) t-column m (Width.width J eps m) t)^2) -
      GlobalBounds.q J (m+1/2) *
        (∫ t, GlobalBounds.q J t * SecondDerivative.regularizedFirst J eps m t^2)| ≤
      η * ((4096/eps^7)*J) + (1+1/η) * (16384/(eps^12*delta^4)) := by
  let c := GlobalBounds.q J (m+1/2)
  let v := fun s t => column s (Width.width J eps s) t
  let D₁ := SecondDerivative.regularizedFirst J eps
  let D₂ := SecondDerivative.regularizedSecond J eps
  have hJp : 0 < J := by linarith
  have hc : 0 ≤ c := GlobalBounds.q_nonneg J _
  have hcJ : c ≤ J := SecondDerivative.q_le_J hJp.le _
  have hsbulk (s : ℝ) (hs : s ∈ Icc m (m+1)) : |s/J| ≤ 1-delta :=
    bulk_interval_scaled hJp hmb hm1b hs
  have hsinside (s : ℝ) (hs : s ∈ Icc m (m+1)) : |s| < J := by
    have hh := hsbulk s hs
    rw [abs_div, abs_of_pos hJp] at hh
    have hh' := (div_le_iff₀ hJp).1 hh
    nlinarith
  have hpos (s : ℝ) (hs : s ∈ Icc m (m+1)) : 0 < Width.width J eps s :=
    Width.width_pos hJp heps (hsinside s hs)
  have hD₂c : ContinuousOn (fun p : ℝ × ℝ => D₂ p.1 p.2) (Icc m (m+1) ×ˢ univ) :=
    SecondDerivative.continuousOn_second (S := Width.width J eps)
      (S₁ := Width.width₁ J eps) (S₂ := Width.width₂ J eps) (a := m)
      (Width.continuous_width hJp.ne' heps).continuousOn
      (Width.continuous_width₁ heps).continuousOn (Width.continuous_width₂ heps).continuousOn hpos
  have hD₂s (t : ℝ) : ContinuousOn (fun s => D₂ s t) (Icc m (m+1)) := by
    have hpair : Continuous (fun s : ℝ => (s,t)) := continuous_id.prodMk continuous_const
    exact hD₂c.comp (f := fun s : ℝ => (s,t)) hpair.continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have hD₁t : Continuous (D₁ m) := by
    unfold D₁ SecondDerivative.regularizedFirst column columnScore
    fun_prop
  have hvt (s : ℝ) : Continuous (v s) := GradientBounds.continuous_column_sample _ _
  have hprod0 : Integrable (fun p : ℝ × ℝ => GlobalBounds.q J p.2*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) :=
    GradientBounds.integrable_q_mul_strip hJp.le
      ((hD₂c.pow 2).mono (Set.prod_mono Subset.rfl (subset_univ _)))
  have hprod : Integrable (fun p : ℝ × ℝ => (c*GlobalBounds.q J p.2)*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) := by
    simpa only [mul_assoc] using hprod0.const_mul c
  have hfac (f : ℝ → ℝ) : (∫ t, (c*GlobalBounds.q J t)*f t) =
      c * ∫ t, GlobalBounds.q J t*f t := by simp_rw [mul_assoc]; rw [integral_const_mul]
  have hA : (∫ t, (c*GlobalBounds.q J t)*D₁ m t^2) ≤ (4096/eps^7)*J := by
    rw [hfac]
    simp_rw [D₁, SecondDerivative.regularizedFirst_eq]
    exact GradientBounds.regularized_edge_derivative_uniform hJp heps heps1 hm hm1
      (show m ∈ Icc m (m+1) by constructor <;> linarith)
  have hB : (∫ s in Ioc m (m+1), ∫ t, (c*GlobalBounds.q J t)*D₂ s t^2) ≤
      16384/(eps^12*delta^4) := by
    calc
      _ ≤ ∫ _s in Ioc m (m+1), 16384/(eps^12*delta^4) := by
        apply setIntegral_mono_on hprod.integral_prod_left
          (integrableOn_const (hs := by simp)) measurableSet_Ioc
        intro s hs
        rw [hfac]
        calc
          _ ≤ c * (16384/(J*eps^12*delta^4)) := mul_le_mul_of_nonneg_left
            (SecondDerivative.regularized_second_bulk hJ heps heps1 hd hd1
              (hsbulk s ⟨hs.1.le, hs.2⟩)) hc
          _ ≤ J * (16384/(J*eps^12*delta^4)) :=
            mul_le_mul_of_nonneg_right hcJ (by positivity)
          _ = _ := by field_simp
      _ = _ := by
        simp only [setIntegral_const, Real.volume_real_Ioc_of_le (show m ≤ m+1 by linarith)]
        ring
  have he := GradientBounds.weighted_finite_difference_energy_error_le
    (v := v) (D₁ := D₁) (D₂ := D₂) (q := fun t => c*GlobalBounds.q J t) m hη
    (fun t => mul_nonneg hc (GlobalBounds.q_nonneg J t))
    (fun t s hs => SecondDerivative.hasDerivAt_regularizedColumn hJp heps (hsinside s hs) t)
    (fun t s hs => SecondDerivative.hasDerivAt_regularizedFirst hJp heps (hsinside s hs) t)
    hD₂s
    (by simpa only [mul_assoc, Pi.pow_apply, Pi.sub_apply] using
      (GradientBounds.integrable_q_mul hJp.le (((hvt (m+1)).sub (hvt m)).pow 2)).const_mul c)
    (by simpa only [mul_assoc, Pi.pow_apply, Pi.sub_apply] using
      (GradientBounds.integrable_q_mul hJp.le (hD₁t.pow 2)).const_mul c)
    (by simpa only [mul_assoc, Pi.pow_apply, Pi.sub_apply] using
      (GradientBounds.integrable_q_mul hJp.le ((((hvt (m+1)).sub (hvt m)).sub hD₁t).pow 2)).const_mul c)
    hprod hA hB
  rw [hfac, hfac] at he
  exact he

theorem endpoint_column_fraction {n : ℕ} {delta : ℝ} (hd : 0 ≤ delta) :
    (((Finset.range (n+1)).filter (fun i => i ∈ GlobalBounds.endpointColumns n delta)).card : ℝ) /
      (n+1 : ℕ) ≤ delta + 1 / spinJ n := by
  classical
  have hc : ((Finset.range (n+1)).filter (fun i => i ∈ GlobalBounds.endpointColumns n delta)).card ≤
      (GlobalBounds.endpointColumns n delta).card := by
    apply Finset.card_le_card
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hcr : (((Finset.range (n+1)).filter (fun i => i ∈ GlobalBounds.endpointColumns n delta)).card : ℝ) ≤
      (GlobalBounds.endpointColumns n delta).card := by exact_mod_cast hc
  have hc' : (((Finset.range (n+1)).filter (fun i => i ∈ GlobalBounds.endpointColumns n delta)).card : ℝ) ≤
      2 * delta * spinJ n + 2 :=
    hcr.trans (GlobalBounds.endpointColumns_card_le hd n)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).2
  have he : (delta + 1 / spinJ n) * (n+1 : ℕ) = 2 * delta * spinJ n + 2 := by
    have hJ := (spinJ_pos n).ne'
    have hn : ((n+1 : ℕ) : ℝ) = 2 * spinJ n := by simp [spinJ]; ring
    rw [hn]
    field_simp
    <;> ring
  rwa [he]

def differenceBudget (J eps delta : ℝ) : ℝ :=
  (1 / Real.sqrt J) * (4096 / eps^7) +
    (1 + Real.sqrt J) * (16384 / (J * eps^12 * delta^4))

theorem regularized_difference_normalized {J m eps delta : ℝ}
    (hJ : 1 ≤ J) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hm : |m| ≤ J-1/2) (hm1 : |m+1| ≤ J-1/2)
    (hmb : |m/J| ≤ 1-delta) (hm1b : |(m+1)/J| ≤ 1-delta) :
    |(GlobalBounds.q J (m+1/2) *
        (∫ t, GlobalBounds.q J t *
          (column (m+1) (Width.width J eps (m+1)) t-column m (Width.width J eps m) t)^2)) / J -
      (GlobalBounds.q J (m+1/2) *
        (∫ t, GlobalBounds.q J t * SecondDerivative.regularizedFirst J eps m t^2)) / J| ≤
      differenceBudget J eps delta := by
  have hJp : 0 < J := by linarith
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJp
  have he := regularized_difference_error hJ heps heps1 hd hd1 (by positivity : 0 < 1/Real.sqrt J)
    hm hm1 hmb hm1b
  rw [← sub_div, abs_div, abs_of_pos hJp]
  have hh := div_le_div_of_nonneg_right he hJp.le
  apply hh.trans_eq
  unfold differenceBudget
  field_simp
  <;> ring

def derivativeGradient (n : ℕ) (eps : ℝ) (i : ℕ) : ℝ :=
  (GlobalBounds.q (spinJ n) (GlobalBounds.spinM n i+1/2) *
    (∫ t, GlobalBounds.q (spinJ n) t *
      SecondDerivative.regularizedFirst (spinJ n) eps (GlobalBounds.spinM n i) t^2)) / spinJ n

theorem G_difference_bulk {n i : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hi : i < n)
    (hb : i ∉ GlobalBounds.endpointEdges n delta) :
    |ContinuousEnergy.G n eps i / spinJ n - derivativeGradient n eps i| ≤
      differenceBudget (spinJ n) eps delta := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hbl, hbr⟩ := good_edge_columns hi hb
  have hml := good_column_scaled (by omega : i ≤ n) hbl
  have hmr := good_column_scaled (by omega : i+1 ≤ n) hbr
  have hnxt : GlobalBounds.spinM n (i+1) = GlobalBounds.spinM n i+1 := by
    unfold GlobalBounds.spinM
    push_cast
    ring
  rw [hnxt] at hmr
  unfold derivativeGradient
  rw [G_eq_regularized n eps i hi]
  apply regularized_difference_normalized (J := spinJ n) (m := GlobalBounds.spinM n i)
    (by unfold spinJ; linarith) heps heps1 hd hd1
    (GlobalBounds.spinM_abs_le (by omega))
  · rw [← hnxt]
    exact GlobalBounds.spinM_abs_le (by omega)
  · exact hml
  · exact hmr

theorem I_bulk {n i : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hi : i ≤ n)
    (hlargeE : 1/eps ≤ spinJ n) (hlargeD : 1 ≤ spinJ n * delta)
    (hb : i ∉ GlobalBounds.endpointColumns n delta) :
    |ContinuousEnergy.I n eps i / spinJ n -
      RateFunctional.positionProfile eps (RateFunctional.spinPoint (n+1) i)| ≤
      6000/(eps^2*delta^6*Real.sqrt (spinJ n)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := good_column_scaled hi hb
  have he := Bulk.explicit_position_error (J := spinJ n) (x := GlobalBounds.spinM n i / spinJ n)
    (by unfold spinJ; linarith) heps heps1 hd hd1 hx hlargeE hlargeD
  have hcoord : spinJ n * (GlobalBounds.spinM n i / spinJ n) = GlobalBounds.spinM n i := by
    field_simp [(spinJ_pos n).ne']
  rw [hcoord] at he
  rw [I_eq_regularized n eps i hi, spinPoint_eq]
  simpa only [RateFunctional.positionProfile, RateFunctional.width, Width.root,
    div_eq_mul_inv, one_mul] using he

theorem derivativeGradient_bulk {n i : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hi : i ≤ n)
    (hb : i ∉ GlobalBounds.endpointColumns n delta) :
    |derivativeGradient n eps i -
      RateFunctional.gradientProfile eps (RateFunctional.spinPoint (n+1) i)| ≤
      64/(eps^6*delta^2*Real.sqrt (spinJ n)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ : 1 ≤ spinJ n := by unfold spinJ; linarith
  have hx := good_column_scaled hi hb
  have hm := (BulkParameters.bulk_geometry hJ hd hd1 hx).1
  have he := BulkParameters.actual_gradient_main_bulk hJ heps heps1 hd hd1 hx
  have hder (t : ℝ) : deriv (fun s => column s (Width.width (spinJ n) eps s) t)
      (GlobalBounds.spinM n i) = SecondDerivative.regularizedFirst (spinJ n) eps (GlobalBounds.spinM n i) t :=
    (SecondDerivative.hasDerivAt_regularizedColumn (spinJ_pos n) heps hm t).deriv
  simp_rw [hder] at he
  unfold derivativeGradient
  rw [spinPoint_eq, gradientProfile_eq]
  simpa only [Width.root] using he

theorem G_bulk {n i : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hi : i < n)
    (hb : i ∉ GlobalBounds.endpointEdges n delta) :
    |ContinuousEnergy.G n eps i / spinJ n -
      RateFunctional.gradientProfile eps (RateFunctional.spinPoint (n+1) i)| ≤
      differenceBudget (spinJ n) eps delta + 64/(eps^6*delta^2*Real.sqrt (spinJ n)) := by
  calc
    _ ≤ |ContinuousEnergy.G n eps i / spinJ n - derivativeGradient n eps i| +
        |derivativeGradient n eps i -
          RateFunctional.gradientProfile eps (RateFunctional.spinPoint (n+1) i)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (G_difference_bulk hn heps heps1 hd hd1 hi hb)
      (derivativeGradient_bulk hn heps heps1 hd hd1 (by omega) (good_edge_columns hi hb).1)

theorem endpoint_edge_fraction {n : ℕ} {delta : ℝ} (hd : 0 ≤ delta) :
    (((Finset.range n).filter (fun i => i ∈ GlobalBounds.endpointEdges n delta)).card : ℝ) /
      (n+1 : ℕ) ≤ 2 * (delta + 1 / spinJ n) := by
  classical
  have hc : ((Finset.range n).filter (fun i => i ∈ GlobalBounds.endpointEdges n delta)).card ≤
      (GlobalBounds.endpointEdges n delta).card := by
    apply Finset.card_le_card
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hcr : (((Finset.range n).filter (fun i => i ∈ GlobalBounds.endpointEdges n delta)).card : ℝ) ≤
      (GlobalBounds.endpointEdges n delta).card := by exact_mod_cast hc
  have hc' : (((Finset.range n).filter (fun i => i ∈ GlobalBounds.endpointEdges n delta)).card : ℝ) ≤
      4 * delta * spinJ n + 4 :=
    hcr.trans (GlobalBounds.endpointEdges_card_le hd n)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).2
  have he : (2 * (delta + 1 / spinJ n)) * (n+1 : ℕ) = 4 * delta * spinJ n + 4 := by
    have hJ := (spinJ_pos n).ne'
    have hn : ((n+1 : ℕ) : ℝ) = 2 * spinJ n := by simp [spinJ]; ring
    rw [hn]
    field_simp
    <;> ring
  rwa [he]

/-- 任意固定参数幂次都转为已证明的对数幂小量。 -/
theorem monomial_sqrt_limit (p q : ℕ) :
    Tendsto (fun J : ℝ => 1 / (epsilon J ^ p * delta J ^ q * Real.sqrt J))
      atTop (𝓝 0) := by
  have he : (fun J : ℝ => 1 / (epsilon J ^ p * delta J ^ q * Real.sqrt J)) =
      (fun J => widthLog J ^ (p + 8*q) / Real.sqrt J) := by
    funext J
    simp only [delta, epsilon, div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow, inv_inv,
      pow_add, pow_mul]
    ring
  rw [he]
  exact log_pow_div_sqrt_tendsto_zero (p+8*q)

theorem monomial_linear_limit (p q : ℕ) :
    Tendsto (fun J : ℝ => 1 / (epsilon J ^ p * delta J ^ q * J))
      atTop (𝓝 0) := by
  have he : (fun J : ℝ => 1 / (epsilon J ^ p * delta J ^ q * J)) =
      (fun J => widthLog J ^ (p + 8*q) / J) := by
    funext J
    simp only [delta, epsilon, div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow, inv_inv,
      pow_add, pow_mul]
    ring
  rw [he]
  exact log_pow_div_tendsto_zero (p+8*q)

theorem differenceBudget_limit :
    Tendsto (fun J : ℝ => differenceBudget J (epsilon J) (delta J)) atTop (𝓝 0) := by
  have hh := (((monomial_sqrt_limit 7 0).const_mul 4096).add
    ((monomial_linear_limit 12 4).const_mul 16384)).add
    ((monomial_sqrt_limit 12 4).const_mul 16384)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with J hJ
  have hs := Real.sqrt_pos.2 hJ
  have hsq := Real.sq_sqrt hJ.le
  have heps := epsilon_pos hJ.le
  have hd : 0 < delta J := pow_pos heps 8
  unfold differenceBudget
  field_simp
  nlinarith only [hsq]

def endpointBudget (J eps delta : ℝ) : ℝ :=
  (14/eps^2+2)*(delta+1/J) + 2*(4096/eps^7+2)*(delta+1/J)

theorem spinPoint_mem (n i : ℕ) (hi : i ≤ n) :
    RateFunctional.spinPoint (n+1) i ∈ Icc (-1 : ℝ) 1 := by
  apply RateFunctional.cell_subset (d := n+1) (k := i) (Nat.succ_pos n) (by omega)
  simpa only [uIcc_of_le RateFunctional.edge_mono] using
    RateFunctional.spinPoint_in_cell (d := n+1) (k := i)

/-- 局部误差接入后的实际 U 界；所有端区、修正和网格误差均已实例化。 -/
theorem actual_energy_error {n : ℕ} {eps delta ηI ηG : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 ≤ delta)
    (hηI : 0 ≤ ηI) (hηG : 0 ≤ ηG)
    (hI : ∀ i ≤ n, i ∉ GlobalBounds.endpointColumns n delta →
      |ContinuousEnergy.I n eps i / spinJ n -
        RateFunctional.positionProfile eps (RateFunctional.spinPoint (n+1) i)| ≤ ηI)
    (hG : ∀ i < n, i ∉ GlobalBounds.endpointEdges n delta →
      |ContinuousEnergy.G n eps i / spinJ n -
        RateFunctional.gradientProfile eps (RateFunctional.spinPoint (n+1) i)| ≤ ηG) :
    |ContinuousEnergy.U n eps / spinJ n - Real.sqrt (1+eps^2)/2| ≤
      ηI + ηG + endpointBudget (spinJ n) eps delta + 7/(4*spinJ n) +
        2*(1+Real.log (n+1 : ℕ))/spinJ n := by
  let badI := GlobalBounds.endpointColumns n delta
  let badG := GlobalBounds.endpointEdges n delta
  let BI := 14/eps^2+2
  let BG := 4096/eps^7+2
  have hBI : 0 ≤ BI := by dsimp [BI]; positivity
  have hBG : 0 ≤ BG := by dsimp [BG]; positivity
  have hib (i : ℕ) (hi : i < n+1) (_hb : i ∈ badI) :
      |ContinuousEnergy.I n eps i / spinJ n -
        RateFunctional.positionProfile eps (RateFunctional.spinPoint (n+1) i)| ≤ BI := by
    apply RateFunctional.position_error_of_global_bound heps heps1 (spinPoint_mem n i (by omega))
    rw [abs_of_nonneg (div_nonneg (I_nonneg n eps i) (spinJ_pos n).le)]
    exact I_global hn heps heps1 i (by omega)
  have hgb (i : ℕ) (hi : i < n) (_hb : i ∈ badG) :
      |ContinuousEnergy.G n eps i / spinJ n -
        RateFunctional.gradientProfile eps (RateFunctional.spinPoint (n+1) i)| ≤ BG := by
    apply RateFunctional.gradient_error_of_global_bound heps heps1 (spinPoint_mem n i (by omega))
    rw [abs_of_nonneg (div_nonneg (G_nonneg n eps i) (spinJ_pos n).le)]
    exact G_global heps heps1 i hi
  have hh := RateFunctional.regularized_energy_error
    (d := n+1) (I := fun i => ContinuousEnergy.I n eps i / spinJ n)
    (G := fun i => ContinuousEnergy.G n eps i / spinJ n)
    (r := (∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i) / ((n+1 : ℕ)*spinJ n))
    badI badG (Nat.succ_pos n) heps heps1 hηI hηG
    (fun i hi hb => hI i (by omega) hb) hib
    (fun i hi hb => hG i (by simpa using hi) hb)
    (fun i hi hb => hgb i (by simpa using hi) hb) (correction_error hn)
  simp only [Nat.add_sub_cancel] at hh
  rw [← U_normalize] at hh
  have hci : BI * ((Finset.range (n+1)).filter (fun i => i ∈ badI)).card / (n+1 : ℕ) ≤
      BI * (delta + 1/spinJ n) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (endpoint_column_fraction hd) hBI
  have hcg : BG * ((Finset.range n).filter (fun i => i ∈ badG)).card / (n+1 : ℕ) ≤
      BG * (2 * (delta + 1/spinJ n)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (endpoint_edge_fraction hd) hBG
  have hmesh : 2/(n+1 : ℕ) + 3/(2*(n+1 : ℕ)) = 7/(4*spinJ n) := by
    have hn' : ((n+1 : ℕ) : ℝ) = 2*spinJ n := by simp [spinJ]; ring
    rw [hn']
    ring
  calc
    _ ≤ ηI + ηG + BI*(delta+1/spinJ n) + BG*(2*(delta+1/spinJ n)) +
        (2/(n+1 : ℕ)+3/(2*(n+1 : ℕ))) + 2*(1+Real.log (n+1 : ℕ))/spinJ n := by
      linarith
    _ = _ := by rw [hmesh]; dsimp [endpointBudget, BI, BG]; ring

theorem endpointBudget_limit :
    Tendsto (fun J : ℝ => endpointBudget J (epsilon J) (delta J)) atTop (𝓝 0) := by
  have hh := ((((((epsilon_tendsto_zero.pow 6).const_mul 14).add
    ((epsilon_tendsto_zero.pow 8).const_mul 6)).add
    (epsilon_tendsto_zero.const_mul 8192)).add
    ((log_pow_div_tendsto_zero 2).const_mul 14)).add
    ((log_pow_div_tendsto_zero 7).const_mul 8192)).add
    ((tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun J : ℝ => J) atTop atTop)) :
      Tendsto (fun J : ℝ => (6 : ℝ)/J) atTop (𝓝 0))
  simp only [zero_pow (by omega : 6 ≠ 0), zero_pow (by omega : 8 ≠ 0), mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with J hJ
  have hL := (widthLog_pos hJ).ne'
  unfold endpointBudget delta epsilon
  field_simp
  <;> ring

theorem correctionBudget_limit :
    Tendsto (fun J : ℝ => 2*(1+Real.log (2*J))/J) atTop (𝓝 0) := by
  have hlog : Tendsto (fun J : ℝ => Real.log J / J) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hconst : Tendsto (fun J : ℝ => (2*(1+Real.log 2))/J) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh := hconst.add (hlog.const_mul 2)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with J hJ
  rw [Real.log_mul (by norm_num) hJ.ne']
  ring

def totalBudget (J eps delta : ℝ) : ℝ :=
  6000/(eps^2*delta^6*Real.sqrt J) +
    (differenceBudget J eps delta + 64/(eps^6*delta^2*Real.sqrt J)) +
    endpointBudget J eps delta + 7/(4*J) + 2*(1+Real.log (2*J))/J

theorem totalBudget_limit :
    Tendsto (fun J : ℝ => totalBudget J (epsilon J) (delta J)) atTop (𝓝 0) := by
  have hi : Tendsto (fun J : ℝ => 6000/(epsilon J^2*delta J^6*Real.sqrt J)) atTop (𝓝 0) := by
    simpa only [← mul_div_assoc, mul_one, mul_zero] using (monomial_sqrt_limit 2 6).const_mul 6000
  have hg : Tendsto (fun J : ℝ => 64/(epsilon J^6*delta J^2*Real.sqrt J)) atTop (𝓝 0) := by
    simpa only [← mul_div_assoc, mul_one, mul_zero] using (monomial_sqrt_limit 6 2).const_mul 64
  have hm : Tendsto (fun J : ℝ => 7/(4*J)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun J : ℝ => J) atTop atTop) :
      Tendsto (fun J : ℝ => (7/4 : ℝ)/J) atTop (𝓝 0)) using 1
    ext J
    ring
  simpa only [totalBudget, add_zero] using
    (((hi.add (differenceBudget_limit.add hg)).add endpointBudget_limit).add hm).add correctionBudget_limit

theorem actual_total_error {n : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hlargeE : 1/eps ≤ spinJ n) (hlargeD : 1 ≤ spinJ n * delta) :
    |ContinuousEnergy.U n eps / spinJ n - Real.sqrt (1+eps^2)/2| ≤
      totalBudget (spinJ n) eps delta := by
  have hJ := spinJ_pos n
  have hηI : 0 ≤ 6000/(eps^2*delta^6*Real.sqrt (spinJ n)) := by positivity
  have hηG : 0 ≤ differenceBudget (spinJ n) eps delta +
      64/(eps^6*delta^2*Real.sqrt (spinJ n)) := by unfold differenceBudget; positivity
  have he := actual_energy_error hn heps heps1 hd.le hηI hηG
    (fun i hi hb => I_bulk hn heps heps1 hd hd1 hi hlargeE hlargeD hb)
    (fun i hi hb => G_bulk hn heps heps1 hd hd1 hi hb)
  have hn' : ((n+1 : ℕ) : ℝ) = 2*spinJ n := by simp [spinJ]; ring
  simpa only [totalBudget, hn'] using he

theorem spinJ_atTop : Tendsto spinJ atTop atTop := spinScale_atTop

theorem eventually_spin_admissible : ∀ᶠ n : ℕ in atTop,
    1 ≤ n ∧ 0 < epsilon (spinJ n) ∧ epsilon (spinJ n) ≤ 1 ∧
      0 < delta (spinJ n) ∧ delta (spinJ n) < 1/2 ∧
      2 ≤ spinJ n * delta (spinJ n) ∧
      1 ≤ spinJ n * epsilon (spinJ n) * delta (spinJ n)^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), spinJ_atTop.eventually eventually_admissible]
    with n hn ha
  exact ⟨hn, ha⟩

theorem spinJ_div_nat_limit :
    Tendsto (fun n : ℕ => spinJ n / n) atTop (𝓝 (1/2 : ℝ)) := by
  have hh := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).div_const 2
  norm_num only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold spinJ
  field_simp
  <;> ring

theorem actual_lower_limit :
    Tendsto (fun n : ℕ => NHLowerBound.spinL n / n) atTop (𝓝 (1/4 : ℝ)) := by
  have hh := NHLowerBound.canonical_spinL_ratio_limit.div_const 2
  convert hh using 1
  · ext n
    ring
  · norm_num

theorem actual_W_nonneg (n : ℕ) :
    0 ≤ ContinuousEnergy.W n (epsilon (spinJ n)) :=
  (NHLowerBound.spinL_nonneg n).trans
    (ContinuousEnergy.spinL_le_W n (epsilon_pos (spinJ_pos n).le))

theorem actual_W_zero (eps : ℝ) : ContinuousEnergy.W 0 eps = 0 := by
  simp [ContinuousEnergy.W, ContinuousEnergy.varianceDensity, ContinuousEnergy.diagonal,
    ContinuousEnergy.quotient, FiniteCopy.Algebra.moment, FiniteCopy.Algebra.spinA]

theorem gaussian_sandwich_limit
    (hU : Tendsto (fun n : ℕ => ContinuousEnergy.U n (epsilon (spinJ n)) / spinJ n)
      atTop (𝓝 (1/2 : ℝ))) :
    Tendsto (fun n : ℕ => ContinuousEnergy.W n (epsilon (spinJ n)) / n)
      atTop (𝓝 (1/4 : ℝ)) := by
  have hUn : Tendsto (fun n : ℕ => ContinuousEnergy.U n (epsilon (spinJ n)) / n)
      atTop (𝓝 (1/4 : ℝ)) := by
    have hh := hU.mul spinJ_div_nat_limit
    convert hh using 1
    · ext n
      symm
      exact div_mul_div_cancel₀ (spinJ_pos n).ne'
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le actual_lower_limit hUn
  · intro n
    exact div_le_div_of_nonneg_right
      (ContinuousEnergy.spinL_le_W n (epsilon_pos (spinJ_pos n).le)) (Nat.cast_nonneg n)
  · intro n
    exact div_le_div_of_nonneg_right
      (ContinuousEnergy.W_le_U n (epsilon_pos (spinJ_pos n).le)) (Nat.cast_nonneg n)

/-- 显式对数参数的实际 U 极限：终端不接受任何能量误差假设。 -/
theorem actual_U_limit :
    Tendsto (fun n : ℕ => ContinuousEnergy.U n (epsilon (spinJ n)) / spinJ n)
      atTop (𝓝 (1/2 : ℝ)) := by
  have hb : ∀ᶠ n : ℕ in atTop,
      |ContinuousEnergy.U n (epsilon (spinJ n)) / spinJ n -
        Real.sqrt (1+epsilon (spinJ n)^2)/2| ≤
        totalBudget (spinJ n) (epsilon (spinJ n)) (delta (spinJ n)) := by
    filter_upwards [eventually_spin_admissible] with n ha
    obtain ⟨hn, heps, heps1, hd, hdhalf, hlargeD, htail⟩ := ha
    have hd1 : delta (spinJ n) ≤ 1 := by linarith
    have hd2 : delta (spinJ n)^2 ≤ 1 := pow_le_one₀ hd.le hd1
    have hJe : 1 ≤ spinJ n * epsilon (spinJ n) := by
      have hh := mul_le_mul_of_nonneg_left hd2 (mul_nonneg (spinJ_pos n).le heps.le)
      exact htail.trans (by simpa only [mul_one] using hh)
    have hlargeE : 1/epsilon (spinJ n) ≤ spinJ n := (div_le_iff₀ heps).2 hJe
    exact actual_total_error hn heps heps1 hd hd1 hlargeE (by linarith)
  have he := squeeze_zero' (Eventually.of_forall (fun n : ℕ =>
      abs_nonneg (ContinuousEnergy.U n (epsilon (spinJ n)) / spinJ n -
        Real.sqrt (1+epsilon (spinJ n)^2)/2))) hb (totalBudget_limit.comp spinJ_atTop)
  have hz : Tendsto (fun n : ℕ => ContinuousEnergy.U n (epsilon (spinJ n)) / spinJ n -
      Real.sqrt (1+epsilon (spinJ n)^2)/2) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 he
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
    hz.add (regularized_target_tendsto.comp spinJ_atTop)

/-- n=2j 的实际共同方差极限，供真实 Schur 加权风险直接使用。 -/
theorem actual_W_limit :
    Tendsto (fun n : ℕ => ContinuousEnergy.W n (epsilon (spinJ n)) / n)
      atTop (𝓝 (1/4 : ℝ)) := gaussian_sandwich_limit actual_U_limit


end CopyQuantumMetrology.GaussianLimit


