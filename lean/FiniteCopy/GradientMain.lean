import FiniteCopy.BulkAsymptotics
import FiniteCopy.GaussianTransport
import FiniteCopy.GlobalBounds
open MeasureTheory
namespace CopyQuantumMetrology.Bulk
open GlobalBounds

noncomputable def standardScore (S T y : ℝ) : ℝ :=
  y/(2*Real.sqrt S)+T/(4*S)*(y^2-1)

lemma standardScore_error (S T y : ℝ) (hS : 0 < S) :
    |standardScore S T y^2-(y/(2*Real.sqrt S))^2| ≤
      (|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))*(1+2*y^2+y^4) := by
  have hs := Real.sqrt_pos.mpr hS
  have hy : |y| ≤ 1+y^2 := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  have hy2 : |y^2-1| ≤ y^2+1 := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg y),abs_one])
  have hr : |standardScore S T y-y/(2*Real.sqrt S)| ≤ |T|/(4*S)*(y^2+1) := by
    unfold standardScore
    rw [add_sub_cancel_left,abs_mul,abs_div,abs_of_pos (by positivity : 0 < 4*S)]
    exact mul_le_mul_of_nonneg_left hy2 (by positivity)
  have he := square_error_of_remainder hr
  have hy' := mul_le_mul_of_nonneg_right hy (by positivity : 0 ≤ y^2+1)
  calc
    _ ≤ 2*|y/(2*Real.sqrt S)| *(|T|/(4*S)*(y^2+1))+(|T|/(4*S)*(y^2+1))^2 := he
    _ ≤ (|T|/(4*S*Real.sqrt S))*((1+y^2)*(y^2+1))+
        (T^2/(16*S^2))*(y^2+1)^2 := by
      rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt S)]
      have ht := mul_le_mul_of_nonneg_left hy' (by positivity : 0 ≤ |T|/(4*S*Real.sqrt S))
      calc
        _ = (|T|/(4*S*Real.sqrt S))*(|y| *(y^2+1))+
            (T^2/(16*S^2))*(y^2+1)^2 := by rw [mul_pow,div_pow,sq_abs]; ring
        _ ≤ _ := add_le_add ht le_rfl
    _ = _ := by ring

lemma score_weight_error (Q B J A C S T y : ℝ) (hS : 0 < S)
    (hQ : 0 ≤ Q) (hQJ : Q ≤ J) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hgap : |Q-B| ≤ A*|y|+C*y^2) :
    |Q*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2| ≤
      (J*(|T|/(4*S*Real.sqrt S)+T^2/(16*S^2)))*(1+2*y^2+y^4)+
      (A/(4*S))*(y^2+y^4)+(C/(4*S))*y^4 := by
  have hs := Real.sqrt_pos.mpr hS
  have hss := Real.sq_sqrt hS.le
  have hy : |y| ≤ 1+y^2 := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  have he : Q*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2 =
      Q*(standardScore S T y^2-(y/(2*Real.sqrt S))^2)+(Q-B)*(y/(2*Real.sqrt S))^2 := by ring
  have hl : (y/(2*Real.sqrt S))^2=y^2/(4*S) := by rw [div_pow,mul_pow,hss]; norm_num
  rw [he]
  calc
    _ ≤ |Q*(standardScore S T y^2-(y/(2*Real.sqrt S))^2)|+
        |(Q-B)*(y/(2*Real.sqrt S))^2| := abs_add_le _ _
    _ = Q*|standardScore S T y^2-(y/(2*Real.sqrt S))^2|+
        |Q-B| *(y^2/(4*S)) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hQ,
        abs_of_nonneg (sq_nonneg (y/(2*Real.sqrt S))),hl]
    _ ≤ J*((|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))*(1+2*y^2+y^4))+
        (A*|y|+C*y^2)*(y^2/(4*S)) := by
      apply add_le_add
      · exact mul_le_mul hQJ (standardScore_error S T y hS) (abs_nonneg _) (hQ.trans hQJ)
      · exact mul_le_mul_of_nonneg_right hgap (by positivity)
    _ ≤ J*((|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))*(1+2*y^2+y^4))+
        (A*(1+y^2)+C*y^2)*(y^2/(4*S)) := by
      gcongr
    _ = _ := by ring

lemma integral_polynomial_three (D A C : ℝ) :
    (∫ y, (D*(1+2*y^2+y^4)+A*(y^2+y^4)+C*y^4)*column 0 1 y^2)=6*D+4*A+3*C := by
  have h0 := integrable_column_sq 0 (by norm_num : (0:ℝ)<1)
  have h2 := integrable_standard_moment 2
  have h4 := integrable_standard_moment 4
  have hD := (h0.add (h2.const_mul 2)).add h4
  have hA := h2.add h4
  have eD := integral_add (h0.add (h2.const_mul 2)) h4
  have eA := integral_add h2 h4
  have e0 := integral_add h0 (h2.const_mul 2)
  simp only [Pi.add_apply] at eD eA e0
  calc
    _ = ∫ y, D*((column 0 1 y^2+2*(y^2*column 0 1 y^2))+y^4*column 0 1 y^2)+
        A*(y^2*column 0 1 y^2+y^4*column 0 1 y^2)+C*(y^4*column 0 1 y^2) := by
      congr 1
      ext y
      ring
    _ = _ := by
      have e1 := integral_add ((hD.const_mul D).add (hA.const_mul A)) (h4.const_mul C)
      have e2 := integral_add (hD.const_mul D) (hA.const_mul A)
      simp only [Pi.add_apply] at e1 e2
      rw [e1,e2,integral_const_mul,integral_const_mul,integral_const_mul,eD,eA,e0,
        integral_const_mul,integral_column_sq 0 (by norm_num : (0:ℝ)<1),integral_standard_second,
        integral_standard_fourth]
      ring

lemma integrable_polynomial_three (D A C : ℝ) :
    Integrable (fun y => (D*(1+2*y^2+y^4)+A*(y^2+y^4)+C*y^4)*column 0 1 y^2) := by
  have h0 := integrable_column_sq 0 (by norm_num : (0:ℝ)<1)
  have h2 := integrable_standard_moment 2
  have h4 := integrable_standard_moment 4
  have ht := ((((h0.add (h2.const_mul 2)).add h4).const_mul D).add
    ((h2.add h4).const_mul A)).add (h4.const_mul C)
  convert ht using 1
  ext y
  simp only [Pi.add_apply]
  ring

lemma standardScore_weight_integral_error {Q : ℝ → ℝ} (B J A C S T : ℝ) (hS : 0 < S)
    (hQc : Continuous Q) (hQ : ∀ y, 0 ≤ Q y) (hQJ : ∀ y, Q y ≤ J)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hgap : ∀ y, |Q y-B| ≤ A*|y|+C*y^2) :
    |(∫ y, Q y*standardScore S T y^2*column 0 1 y^2)-B/(4*S)| ≤
      6*J*(|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))+A/S+3*C/(4*S) := by
  let D := J*(|T|/(4*S*Real.sqrt S)+T^2/(16*S^2))
  have hm := integrable_polynomial_three D (A/(4*S)) (C/(4*S))
  have hl : Integrable (fun y => B*(y/(2*Real.sqrt S))^2*column 0 1 y^2) := by
    convert (integrable_standard_moment 2).const_mul (B/(4*S)) using 1
    ext y
    rw [div_pow,mul_pow,Real.sq_sqrt hS.le]
    ring
  have el : (∫ y, B*(y/(2*Real.sqrt S))^2*column 0 1 y^2)=B/(4*S) := by
    have ef : (fun y : ℝ => B*(y/(2*Real.sqrt S))^2*column 0 1 y^2)=
        fun y => (B/(4*S))*(y^2*column 0 1 y^2) := by
      ext y
      rw [div_pow,mul_pow,Real.sq_sqrt hS.le]
      ring
    rw [ef,integral_const_mul,integral_standard_second,mul_one]
  have hb : ∀ᵐ y, ‖(Q y*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2)*column 0 1 y^2‖ ≤
      (D*(1+2*y^2+y^4)+(A/(4*S))*(y^2+y^4)+(C/(4*S))*y^4)*column 0 1 y^2 := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (column 0 1 y))]
    exact mul_le_mul_of_nonneg_right (score_weight_error (Q y) B J A C S T y hS (hQ y) (hQJ y) hA hC (hgap y)) (sq_nonneg _)
  have hd : Integrable (fun y => (Q y*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2)*column 0 1 y^2) := by
    apply hm.mono' _ hb
    have hc : Continuous (fun y => (Q y*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2)*column 0 1 y^2) := by
      unfold standardScore column
      fun_prop
    exact hc.aestronglyMeasurable
  have hf : Integrable (fun y => Q y*standardScore S T y^2*column 0 1 y^2) := by
    convert hd.add hl using 1
    ext y
    simp only [Pi.add_apply]
    ring
  have hn := norm_integral_le_of_norm_le hm hb
  have ee : (∫ y, (Q y*standardScore S T y^2-B*(y/(2*Real.sqrt S))^2)*column 0 1 y^2)=
      (∫ y, Q y*standardScore S T y^2*column 0 1 y^2)-B/(4*S) := by
    simp_rw [sub_mul]
    rw [integral_sub hf hl,el]
  rw [ee,Real.norm_eq_abs,integral_polynomial_three] at hn
  convert hn using 1 <;> dsimp [D] <;> ring

end CopyQuantumMetrology.Bulk


