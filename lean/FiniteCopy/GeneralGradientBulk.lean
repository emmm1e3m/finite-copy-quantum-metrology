import FiniteCopy.GeneralGradientBounds
open MeasureTheory Set
noncomputable section
namespace CopyQuantumMetrology.GeneralGradient
open GlobalBounds GradientBounds

set_option maxHeartbeats 700000

def bulkConstant (e d : ℝ) : ℝ := 130/(e^6*d^2)+32768/(e^12*d^4)

lemma bulkConstant_nonneg {e d : ℝ} (he : 0 < e) (hd : 0 < d) : 0 ≤ bulkConstant e d := by
  unfold bulkConstant
  positivity

lemma scalar_moving_main_bulk {J m S T e d b : ℝ} (hJ : 1 ≤ J)
    (he : 0 < e) (he1 : e ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hm : |m/J| ≤ 1-d) (hSl : J*d/4 ≤ S) (hT : |T| ≤ 2/e^3)
    (hb : 0 < b) (hwidth : S=(J^2-m^2)*b/J) :
    |q J (m+1/2)*(∫ t, q J t*movingDeriv m S T t^2)/J-1/(4*b)| ≤
      64/(e^6*d^2*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  obtain ⟨hmint,hBL⟩ := BulkParameters.bulk_geometry hJ hd hd1 hm
  have hrad : 0 < J^2-m^2 := by nlinarith [sq_abs m, abs_nonneg m]
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hi := (BulkParameters.movingFirst_integral_error T hJp.le hrad hSp).trans
    (BulkParameters.score_budget_bound hJ he he1 hd hd1 hmint.le hBL hSl hT)
  change |(∫ t, q J t*movingDeriv m S T t^2)-Real.sqrt (J^2-m^2)/(4*S)| ≤
    55/(e^6*d^2*Real.sqrt J) at hi
  have hmain : (J^2-m^2)/(4*J*S)=1/(4*b) := by
    rw [hwidth]
    field_simp [hJp.ne', hrad.ne', hb.ne']
  have hc := (BulkParameters.coefficient_main_error hJ hmint.le hrad hSp).trans
    (BulkParameters.coefficient_budget hJ he he1 hd hd1 hSl)
  rw [hmain] at hc
  have hcn : 0 ≤ q J (m+1/2)/J := div_nonneg (q_nonneg J _) hJp.le
  have hcle : q J (m+1/2)/J ≤ 1 := (div_le_one hJp).2 (SecondDerivative.q_le_J hJp.le _)
  have heq : q J (m+1/2)*(∫ t, q J t*movingDeriv m S T t^2)/J-1/(4*b) =
      (q J (m+1/2)/J)*((∫ t, q J t*movingDeriv m S T t^2)-Real.sqrt (J^2-m^2)/(4*S))+
      (q J (m+1/2)*Real.sqrt (J^2-m^2)/(4*J*S)-1/(4*b)) := by ring
  rw [heq]
  calc
    _ ≤ |(q J (m+1/2)/J)*((∫ t, q J t*movingDeriv m S T t^2)-Real.sqrt (J^2-m^2)/(4*S))|+
        |q J (m+1/2)*Real.sqrt (J^2-m^2)/(4*J*S)-1/(4*b)| := abs_add_le _ _
    _ = (q J (m+1/2)/J)*|(∫ t, q J t*movingDeriv m S T t^2)-Real.sqrt (J^2-m^2)/(4*S)|+
        |q J (m+1/2)*Real.sqrt (J^2-m^2)/(4*J*S)-1/(4*b)| := by rw [abs_mul,abs_of_nonneg hcn]
    _ ≤ 1*(55/(e^6*d^2*Real.sqrt J))+2/(e^6*d^2*Real.sqrt J) :=
      add_le_add (mul_le_mul hcle hi (abs_nonneg _) (by positivity)) hc
    _ = 57/(e^6*d^2*Real.sqrt J) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (by positivity)

-- 微分与连续性前提作用于真实列，有限差分能量界由FTC推得。
theorem gaussian_difference_error {S T U : ℝ → ℝ} {J m e d η : ℝ}
    (hJ : 1 ≤ J) (he : 0 < e) (he1 : e ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η)
    (hSc : ContinuousOn S (Icc m (m+1))) (hTc : ContinuousOn T (Icc m (m+1)))
    (hUc : ContinuousOn U (Icc m (m+1)))
    (hSder : ∀ s ∈ Icc m (m+1), HasDerivAt S (T s) s)
    (hTder : ∀ s ∈ Icc m (m+1), HasDerivAt T (U s) s)
    (hSl : ∀ s ∈ Icc m (m+1), J*d/4 ≤ S s)
    (hTb : ∀ s ∈ Icc m (m+1), |T s| ≤ 2/e^3)
    (hUb : ∀ s ∈ Icc m (m+1), |U s| ≤ 3/(J*e^5)) :
    |q J (m+1/2)*(∫ t, q J t*(column (m+1) (S (m+1)) t-column m (S m) t)^2)-
      q J (m+1/2)*(∫ t, q J t*movingDeriv m (S m) (T m) t^2)| ≤
      η*((66/(e^6*d^2))*J)+(1+1/η)*(16384/(e^12*d^4)) := by
  let c := q J (m+1/2)
  let v := fun s t => column s (S s) t
  let D₁ := fun s t => movingDeriv s (S s) (T s) t
  let D₂ := fun s t => SecondDerivative.second s (S s) (T s) (U s) t
  have hJp : 0 < J := by linarith
  have hc : 0 ≤ c := q_nonneg J _
  have hcJ : c ≤ J := SecondDerivative.q_le_J hJp.le _
  have hm : m ∈ Icc m (m+1) := ⟨le_rfl,by linarith⟩
  have hpos : ∀ s ∈ Icc m (m+1), 0 < S s := by
    intro s hs
    exact lt_of_lt_of_le (by positivity) (hSl s hs)
  have hD₂c : ContinuousOn (fun p : ℝ × ℝ => D₂ p.1 p.2) (Icc m (m+1) ×ˢ univ) :=
    SecondDerivative.continuousOn_second hSc hTc hUc hpos
  have hD₂s (t : ℝ) : ContinuousOn (fun s => D₂ s t) (Icc m (m+1)) := by
    have hp : Continuous (fun s : ℝ => (s,t)) := continuous_id.prodMk continuous_const
    exact hD₂c.comp (f := fun s : ℝ => (s,t)) hp.continuousOn (fun s hs => ⟨hs,mem_univ _⟩)
  have hD₁t : Continuous (D₁ m) := continuous_movingDeriv _ _ _
  have hvt (s : ℝ) : Continuous (v s) := continuous_column_sample _ _
  have hprod0 : Integrable (fun p : ℝ × ℝ => q J p.2*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) :=
    integrable_q_mul_strip hJp.le ((hD₂c.pow 2).mono (Set.prod_mono Subset.rfl (subset_univ _)))
  have hprod : Integrable (fun p : ℝ × ℝ => (c*q J p.2)*D₂ p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) := by
    simpa only [mul_assoc] using hprod0.const_mul c
  have hfac (f : ℝ → ℝ) : (∫ t, (c*q J t)*f t)=c*∫ t, q J t*f t := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  have hA : (∫ t, (c*q J t)*D₁ m t^2) ≤ (66/(e^6*d^2))*J := by
    rw [hfac]
    calc
      _ ≤ c*(66/(e^6*d^2)) := mul_le_mul_of_nonneg_left
        (scalar_first_bulk hJ he he1 hd hd1 (hSl m hm) (hTb m hm)) hc
      _ ≤ J*(66/(e^6*d^2)) := mul_le_mul_of_nonneg_right hcJ (by positivity)
      _ = _ := by ring
  have hB : (∫ s in Ioc m (m+1), ∫ t, (c*q J t)*D₂ s t^2) ≤ 16384/(e^12*d^4) := by
    calc
      _ ≤ ∫ _s in Ioc m (m+1), 16384/(e^12*d^4) := by
        apply setIntegral_mono_on hprod.integral_prod_left
          (integrableOn_const (hs := by simp)) measurableSet_Ioc
        intro s hs
        have hss : s ∈ Icc m (m+1) := ⟨hs.1.le,hs.2⟩
        rw [hfac]
        calc
          _ ≤ c*(16384/(J*e^12*d^4)) := mul_le_mul_of_nonneg_left
            (scalar_second_bulk s hJ he he1 hd hd1 (hSl s hss) (hTb s hss) (hUb s hss)) hc
          _ ≤ J*(16384/(J*e^12*d^4)) := mul_le_mul_of_nonneg_right hcJ (by positivity)
          _ = _ := by field_simp
      _ = _ := by
        simp only [setIntegral_const,Real.volume_real_Ioc_of_le (show m ≤ m+1 by linarith)]
        ring
  have hh := weighted_finite_difference_energy_error_le (v := v) (D₁ := D₁) (D₂ := D₂)
    (q := fun t => c*q J t) m hη (fun t => mul_nonneg hc (q_nonneg J t))
    (fun t s hs => hasDerivAt_column_moving t (hSder s hs) (hpos s hs))
    (fun t s hs => hasDerivAt_movingDeriv t (hSder s hs) (hTder s hs) (hpos s hs)) hD₂s
    (by simpa only [mul_assoc,Pi.pow_apply,Pi.sub_apply] using
      (integrable_q_mul hJp.le (((hvt (m+1)).sub (hvt m)).pow 2)).const_mul c)
    (by simpa only [mul_assoc,Pi.pow_apply,Pi.sub_apply] using
      (integrable_q_mul hJp.le (hD₁t.pow 2)).const_mul c)
    (by simpa only [mul_assoc,Pi.pow_apply,Pi.sub_apply] using
      (integrable_q_mul hJp.le ((((hvt (m+1)).sub (hvt m)).sub hD₁t).pow 2)).const_mul c)
    hprod hA hB
  rw [hfac,hfac] at hh
  exact hh

lemma difference_budget_simplify {J A B : ℝ} (hJ : 1 ≤ J) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ((1/Real.sqrt J)*(A*J)+(1+1/(1/Real.sqrt J))*B)/J ≤ (A+2*B)/Real.sqrt J := by
  have hJp : 0 < J := by linarith
  have hr := Real.sqrt_pos.mpr hJp
  have hrs := Real.sq_sqrt hJp.le
  have hrJ : Real.sqrt J ≤ J := by nlinarith
  calc
    _ = A/Real.sqrt J+B/J+B/Real.sqrt J := by
      field_simp
      nlinarith [congrArg (fun x : ℝ => B*x) hrs]
    _ ≤ A/Real.sqrt J+B/Real.sqrt J+B/Real.sqrt J := by gcongr
    _ = _ := by ring

theorem gaussian_gradient_bulk {S T U : ℝ → ℝ} {J m e d b : ℝ}
    (hJ : 1 ≤ J) (he : 0 < e) (he1 : e ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hm : |m/J| ≤ 1-d) (hb : 0 < b) (hwidth : S m=(J^2-m^2)*b/J)
    (hSc : ContinuousOn S (Icc m (m+1))) (hTc : ContinuousOn T (Icc m (m+1)))
    (hUc : ContinuousOn U (Icc m (m+1)))
    (hSder : ∀ s ∈ Icc m (m+1), HasDerivAt S (T s) s)
    (hTder : ∀ s ∈ Icc m (m+1), HasDerivAt T (U s) s)
    (hSl : ∀ s ∈ Icc m (m+1), J*d/4 ≤ S s)
    (hTb : ∀ s ∈ Icc m (m+1), |T s| ≤ 2/e^3)
    (hUb : ∀ s ∈ Icc m (m+1), |U s| ≤ 3/(J*e^5)) :
    |q J (m+1/2)*(∫ t, q J t*(column (m+1) (S (m+1)) t-column m (S m) t)^2)/J-
      1/(4*b)| ≤ bulkConstant e d/Real.sqrt J := by
  have hJp : 0 < J := by linarith
  have hmp : m ∈ Icc m (m+1) := ⟨le_rfl,by linarith⟩
  let G := q J (m+1/2)*(∫ t, q J t*(column (m+1) (S (m+1)) t-column m (S m) t)^2)
  let H := q J (m+1/2)*(∫ t, q J t*movingDeriv m (S m) (T m) t^2)
  have he' := gaussian_difference_error hJ he he1 hd hd1
    (by positivity : 0 < 1/Real.sqrt J) hSc hTc hUc hSder hTder hSl hTb hUb
  have hed : |G/J-H/J| ≤ (66/(e^6*d^2)+2*(16384/(e^12*d^4)))/Real.sqrt J := by
    rw [← sub_div,abs_div,abs_of_pos hJp]
    exact (div_le_div_of_nonneg_right he' hJp.le).trans
      (difference_budget_simplify hJ (by positivity) (by positivity))
  have hem : |H/J-1/(4*b)| ≤ 64/(e^6*d^2*Real.sqrt J) :=
    scalar_moving_main_bulk hJ he he1 hd hd1 hm (hSl m hmp) (hTb m hmp) hb hwidth
  change |G/J-1/(4*b)| ≤ _
  calc
    _ ≤ |G/J-H/J|+|H/J-1/(4*b)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hed hem
    _ = _ := by unfold bulkConstant; ring

end CopyQuantumMetrology.GeneralGradient
