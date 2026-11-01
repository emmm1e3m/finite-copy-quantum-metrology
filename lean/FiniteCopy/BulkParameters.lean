import FiniteCopy.Width
import FiniteCopy.GlobalBounds
import FiniteCopy.GaussianTransport
import FiniteCopy.GradientMain

open MeasureTheory
noncomputable section
namespace CopyQuantumMetrology.BulkParameters
open GlobalBounds Bulk

lemma bulk_geometry {J m delta : ℝ} (hJ : 1 ≤ J) (hd : 0 < delta)
    (hd1 : delta ≤ 1) (hm : |m/J| ≤ 1-delta) :
    |m| < J ∧ J*delta ≤ Real.sqrt (J^2-m^2) := by
  have hJp : 0 < J := by linarith
  have hm' : |m| ≤ (1-delta)*J := by
    rw [abs_div, abs_of_pos hJp] at hm
    exact (div_le_iff₀ hJp).1 hm
  have hmint : |m| < J := by nlinarith
  have hrad : 0 < J^2-m^2 := by nlinarith [sq_abs m, abs_nonneg m]
  have hB := Real.sqrt_nonneg (J^2-m^2)
  have hBsq := Real.sq_sqrt hrad.le
  have hprod := mul_nonneg (abs_nonneg m) (sub_nonneg.mpr hmint.le)
  have hr : J-|m| ≤ Real.sqrt (J^2-m^2) := by nlinarith [sq_abs m]
  exact ⟨hmint, (by nlinarith : J*delta ≤ J-|m|).trans hr⟩

lemma sqrt_width_lower {J delta S : ℝ} (hJ : 0 < J) (hd : 0 < delta)
    (hd1 : delta ≤ 1) (hS : J*delta/4 ≤ S) :
    Real.sqrt J*delta/2 ≤ Real.sqrt S := by
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hJr := Real.sqrt_nonneg J
  have hSr := Real.sqrt_nonneg S
  have hJ2 := Real.sq_sqrt hJ.le
  have hS2 := Real.sq_sqrt hSp.le
  have hd2 : delta^2 ≤ delta := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hd2 hJ.le
  nlinarith [sq_nonneg (Real.sqrt J*delta/2)]

lemma score_budget_bound {J m eps delta B S T : ℝ}
    (hJ : 1 ≤ J) (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hm : |m| ≤ J)
    (hB : J*delta ≤ B) (hS : J*delta/4 ≤ S) (hT : |T| ≤ 2/eps^3) :
    6*J*(|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))+
      2*|m|/(B*Real.sqrt S)+3/(4*B) ≤
      55/(eps^6*delta^2*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hJr := Real.sqrt_pos.mpr hJp
  have hSr := Real.sqrt_pos.mpr hSp
  have hsqrt := sqrt_width_lower hJp hd hd1 hS
  have hJrJ : Real.sqrt J ≤ J := by nlinarith [Real.sq_sqrt hJp.le]
  have he3 : eps^3 ≤ 1 := by exact pow_le_one₀ he.le he1
  have he6 : eps^6 ≤ 1 := by exact pow_le_one₀ he.le he1
  have he63 : eps^6 ≤ eps^3 := by nlinarith [sq_nonneg (eps^3), pow_pos he 3]
  have hd2 : delta^2 ≤ delta := by nlinarith
  have ht2 : T^2 ≤ 4/eps^6 := by
    have ht := (sq_le_sq₀ (abs_nonneg T) (by positivity : 0 ≤ 2/eps^3)).2 hT
    norm_num [div_pow, ← pow_mul] at ht
    exact ht
  have h1 : 6*J*(|T|/(4*S*Real.sqrt S)) ≤ 24/(eps^6*delta^2*Real.sqrt J) := by
    calc
      _ ≤ 6*J*((2/eps^3)/(4*(J*delta/4)*(Real.sqrt J*delta/2))) := by gcongr
      _ = 24/(eps^3*delta^2*Real.sqrt J) := by field_simp; ring
      _ ≤ _ := by gcongr
  have h2 : 6*J*(T^2/(16*S^2)) ≤ 24/(eps^6*delta^2*Real.sqrt J) := by
    calc
      _ ≤ 6*J*((4/eps^6)/(16*(J*delta/4)^2)) := by gcongr
      _ = 24/(eps^6*delta^2*J) := by field_simp; ring
      _ ≤ _ := by gcongr
  have h3 : 2*|m|/(B*Real.sqrt S) ≤ 4/(eps^6*delta^2*Real.sqrt J) := by
    calc
      _ ≤ 2*J/((J*delta)*(Real.sqrt J*delta/2)) := by gcongr
      _ = 4/(delta^2*Real.sqrt J) := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        calc
          _ = eps^6*(delta^2*Real.sqrt J) := by ring
          _ ≤ _ := mul_le_of_le_one_left (by positivity) he6
  have h4 : 3/(4*B) ≤ 3/(eps^6*delta^2*Real.sqrt J) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    calc
      eps^6*delta^2*Real.sqrt J ≤ 1*delta*J := by gcongr
      _ ≤ 4*B := by nlinarith
  calc
    _ = 6*J*(|T|/(4*S*Real.sqrt S))+6*J*(T^2/(16*S^2))+
      2*|m|/(B*Real.sqrt S)+3/(4*B) := by ring
    _ ≤ 24/(eps^6*delta^2*Real.sqrt J)+24/(eps^6*delta^2*Real.sqrt J)+
      4/(eps^6*delta^2*Real.sqrt J)+3/(eps^6*delta^2*Real.sqrt J) := by gcongr
    _ = _ := by ring

lemma q_standard_gap {J m S : ℝ} (hB : 0 < J^2-m^2) (hS : 0 < S) (y : ℝ) :
    |q J (m+Real.sqrt S*y)-Real.sqrt (J^2-m^2)| ≤
      (2*|m| * Real.sqrt S/Real.sqrt (J^2-m^2))*|y|+
        (S/Real.sqrt (J^2-m^2))*y^2 := by
  have hBp := Real.sqrt_pos.mpr hB
  have hsp := Real.sqrt_pos.mpr hS
  have hnum : |(m+Real.sqrt S*y)^2-m^2| ≤ 2*|m| * Real.sqrt S*|y|+S*y^2 := by
    have he : (m+Real.sqrt S*y)^2-m^2 = 2*m*Real.sqrt S*y+S*y^2 := by
      nlinarith [Real.sq_sqrt hS.le]
    rw [he]
    calc
      _ ≤ |2*m*Real.sqrt S*y|+|S*y^2| := abs_add_le _ _
      _ = _ := by simp [abs_mul, abs_of_pos hsp, abs_of_pos hS, abs_pow]
  calc
    _ ≤ |(m+Real.sqrt S*y)^2-m^2|/Real.sqrt (J^2-m^2) := abs_q_sub_sqrt hB _
    _ ≤ (2*|m| * Real.sqrt S*|y|+S*y^2)/Real.sqrt (J^2-m^2) :=
      div_le_div_of_nonneg_right hnum hBp.le
    _ = _ := by ring

lemma coefficient_gap {J m : ℝ} (hJ : 1 ≤ J) (hm : |m| ≤ J)
    (hB : 0 < J^2-m^2) :
    |q J (m+1/2)-Real.sqrt (J^2-m^2)| ≤ 5*J/(4*Real.sqrt (J^2-m^2)) := by
  have hBp := Real.sqrt_pos.mpr hB
  have hnum : |(m+1/2)^2-m^2| ≤ 5*J/4 := by
    rw [show (m+1/2)^2-m^2=m+1/4 by ring]
    have ha := abs_add_le m (1/4)
    norm_num at ha
    linarith
  calc
    _ ≤ |(m+1/2)^2-m^2|/Real.sqrt (J^2-m^2) := abs_q_sub_sqrt hB _
    _ ≤ (5*J/4)/Real.sqrt (J^2-m^2) := div_le_div_of_nonneg_right hnum hBp.le
    _ = _ := by ring

lemma coefficient_main_error {J m S : ℝ} (hJ : 1 ≤ J) (hm : |m| ≤ J)
    (hB : 0 < J^2-m^2) (hS : 0 < S) :
    |q J (m+1/2)*Real.sqrt (J^2-m^2)/(4*J*S)-(J^2-m^2)/(4*J*S)| ≤ 5/(16*S) := by
  have hJp : 0 < J := by linarith
  have hBp := Real.sqrt_pos.mpr hB
  have he : q J (m+1/2)*Real.sqrt (J^2-m^2)/(4*J*S)-(J^2-m^2)/(4*J*S) =
      (q J (m+1/2)-Real.sqrt (J^2-m^2))*Real.sqrt (J^2-m^2)/(4*J*S) := by
    calc
      _ = (q J (m+1/2)*Real.sqrt (J^2-m^2)-(J^2-m^2))/(4*J*S) := by ring
      _ = (q J (m+1/2)*Real.sqrt (J^2-m^2)-Real.sqrt (J^2-m^2)^2)/(4*J*S) := by
        rw [Real.sq_sqrt hB.le]
      _ = _ := by ring
  rw [he, abs_div, abs_mul, abs_of_pos hBp, abs_of_pos (by positivity : 0 < 4*J*S)]
  calc
    _ ≤ (5*J/(4*Real.sqrt (J^2-m^2)))*Real.sqrt (J^2-m^2)/(4*J*S) := by
      gcongr
      exact coefficient_gap hJ hm hB
    _ = _ := by field_simp; ring

lemma coefficient_budget {J eps delta S : ℝ} (hJ : 1 ≤ J)
    (he : 0 < eps) (he1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hS : J*delta/4 ≤ S) : 5/(16*S) ≤ 2/(eps^6*delta^2*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hJr := Real.sqrt_pos.mpr hJp
  have hJrJ : Real.sqrt J ≤ J := by nlinarith [Real.sq_sqrt hJp.le]
  have he6 : eps^6 ≤ 1 := pow_le_one₀ he.le he1
  have hd2 : delta^2 ≤ delta := by nlinarith
  calc
    _ ≤ 5/(16*(J*delta/4)) := by gcongr
    _ = (5/4)/(J*delta) := by ring
    _ ≤ 2/(J*delta) := by gcongr; norm_num
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc
        _ ≤ 1*delta*J := by gcongr
        _ = J*delta := by ring

def movingFirst (m S T t : ℝ) : ℝ :=
  column m S t*((t-m)/(2*S)+T/(4*S)*((t-m)^2/S-1))

lemma movingFirst_standardize (J m T : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, q J t*movingFirst m S T t^2) =
      ∫ y, q J (m+Real.sqrt S*y)*standardScore S T y^2*column 0 1 y^2 := by
  have hr := Real.sqrt_pos.mpr hS
  have hscore (y : ℝ) :
      (m+Real.sqrt S*y-m)/(2*S)+T/(4*S)*((m+Real.sqrt S*y-m)^2/S-1)=
        standardScore S T y := by
    unfold standardScore
    rw [show m+Real.sqrt S*y-m=Real.sqrt S*y by ring, mul_pow, Real.sq_sqrt hS.le]
    have hfirst : Real.sqrt S*y/(2*S)=y/(2*Real.sqrt S) := by
      field_simp
      rw [Real.sq_sqrt hS.le]
      ring
    rw [hfirst]
    field_simp
  calc
    _ = ∫ t, (q J t*((t-m)/(2*S)+T/(4*S)*((t-m)^2/S-1))^2)*column m S t^2 := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold movingFirst
      ring
    _ = ∫ y, (q J (m+Real.sqrt S*y)*
        ((m+Real.sqrt S*y-m)/(2*S)+T/(4*S)*((m+Real.sqrt S*y-m)^2/S-1))^2)*
          column 0 1 y^2 := gaussian_integral_standardize _ m hS
    _ = _ := by simp_rw [hscore]

lemma movingFirst_integral_error {J m S : ℝ} (T : ℝ) (hJ : 0 ≤ J)
    (hB : 0 < J^2-m^2) (hS : 0 < S) :
    |(∫ t, q J t*movingFirst m S T t^2)-Real.sqrt (J^2-m^2)/(4*S)| ≤
      6*J*(|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))+
        2*|m|/(Real.sqrt (J^2-m^2)*Real.sqrt S)+3/(4*Real.sqrt (J^2-m^2)) := by
  have hBp := Real.sqrt_pos.mpr hB
  have hSr := Real.sqrt_pos.mpr hS
  have hQc : Continuous (fun y : ℝ => q J (m+Real.sqrt S*y)) := by
    exact (continuous_q J).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hQJ : ∀ y, q J (m+Real.sqrt S*y) ≤ J := by
    intro y
    nlinarith [q_sq_le J (m+Real.sqrt S*y),q_nonneg J (m+Real.sqrt S*y)]
  have hi := standardScore_weight_integral_error
    (Real.sqrt (J^2-m^2)) J (2*|m| * Real.sqrt S/Real.sqrt (J^2-m^2))
    (S/Real.sqrt (J^2-m^2)) S T hS hQc
    (fun y => q_nonneg J _) hQJ (by positivity) (by positivity) (q_standard_gap hB hS)
  rw [movingFirst_standardize J m T hS]
  convert hi using 1
  field_simp
  rw [Real.sq_sqrt hS.le]
  ring

lemma movingFirst_eq_deriv {J eps m : ℝ} (hJ : 0 < J) (he : 0 < eps)
    (hm : |m| < J) (t : ℝ) :
    movingFirst m (Width.width J eps m) (Width.width₁ J eps m) t =
      deriv (fun s => column s (Width.width J eps s) t) m := by
  exact (hasDerivAt_column_moving t (Width.hasDerivAt_width hJ.ne' he m)
    (Width.width_pos hJ he hm)).deriv.symm

theorem regularized_moving_main_bulk {J eps delta m : ℝ}
    (hJ : 1 ≤ J) (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hm : |m/J| ≤ 1-delta) :
    |q J (m+1/2)*(∫ t, q J t*
      movingFirst m (Width.width J eps m) (Width.width₁ J eps m) t^2)/J-
      Width.root eps (m/J)/2| ≤ 64/(eps^6*delta^2*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  obtain ⟨hmint, hBL⟩ := bulk_geometry hJ hd hd1 hm
  have hrad : 0 < J^2-m^2 := by nlinarith [sq_abs m, abs_nonneg m]
  let B := Real.sqrt (J^2-m^2)
  let S := Width.width J eps m
  let T := Width.width₁ J eps m
  let c := q J (m+1/2)
  let I := ∫ t, q J t*movingFirst m S T t^2
  have hBp : 0 < B := Real.sqrt_pos.mpr hrad
  have hSp : 0 < S := Width.width_pos hJp he hmint
  have hSL : J*delta/4 ≤ S := (Width.bulk_width_bounds hJp he he1 hd.le hm).1
  have hT : |T| ≤ 2/eps^3 := Width.width₁_bound hJp he he1 hmint.le
  have hi := (movingFirst_integral_error T hJp.le hrad hSp).trans
    (score_budget_bound hJ he he1 hd hd1 hmint.le hBL hSL hT)
  change |I-B/(4*S)| ≤ 55/(eps^6*delta^2*Real.sqrt J) at hi
  have hroot := Width.root_pos he (m/J)
  have hmain : (J^2-m^2)/(4*J*S)=Width.root eps (m/J)/2 := by
    dsimp [S]
    rw [Width.width_eq_radial hJp.ne']
    field_simp [hJp.ne', hroot.ne', hrad.ne']
    ring
  have hc := (coefficient_main_error hJ hmint.le hrad hSp).trans
    (coefficient_budget hJ he he1 hd hd1 hSL)
  rw [hmain] at hc
  change |c*B/(4*J*S)-Width.root eps (m/J)/2| ≤
    2/(eps^6*delta^2*Real.sqrt J) at hc
  have hcn : 0 ≤ c/J := div_nonneg (q_nonneg J _) hJp.le
  have hcle : c/J ≤ 1 := by
    apply (div_le_one hJp).2
    dsimp [c]
    nlinarith [q_sq_le J (m+1/2),q_nonneg J (m+1/2)]
  change |c*I/J-Width.root eps (m/J)/2| ≤ _
  have heq : c*I/J-Width.root eps (m/J)/2 =
      (c/J)*(I-B/(4*S))+(c*B/(4*J*S)-Width.root eps (m/J)/2) := by ring
  rw [heq]
  calc
    _ ≤ |(c/J)*(I-B/(4*S))|+|c*B/(4*J*S)-Width.root eps (m/J)/2| := abs_add_le _ _
    _ = (c/J)*|I-B/(4*S)|+|c*B/(4*J*S)-Width.root eps (m/J)/2| := by
      rw [abs_mul,abs_of_nonneg hcn]
    _ ≤ 1*(55/(eps^6*delta^2*Real.sqrt J))+2/(eps^6*delta^2*Real.sqrt J) :=
      add_le_add (mul_le_mul hcle hi (abs_nonneg _) (by positivity)) hc
    _ = 57/(eps^6*delta^2*Real.sqrt J) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (by positivity)

-- 终端结论直接作用于原始Gaussian列的真实参数导数。
theorem actual_gradient_main_bulk {J eps delta m : ℝ}
    (hJ : 1 ≤ J) (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hm : |m/J| ≤ 1-delta) :
    |q J (m+1/2)*(∫ t, q J t*
      (deriv (fun s => column s (Width.width J eps s) t) m)^2)/J-
      Width.root eps (m/J)/2| ≤ 64/(eps^6*delta^2*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  have hmint := (bulk_geometry hJ hd hd1 hm).1
  simpa only [movingFirst_eq_deriv hJp he hmint] using
    regularized_moving_main_bulk hJ he he1 hd hd1 hm

end CopyQuantumMetrology.BulkParameters

