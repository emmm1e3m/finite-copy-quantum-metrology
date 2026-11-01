import FiniteCopy.ActualPosition
import FiniteCopy.Width
open MeasureTheory
namespace CopyQuantumMetrology.Bulk
open GlobalBounds

lemma positionConstant_bound {x B D : ℝ} (hB : 0 < B) (hx : |x| ≤ 1)
    (hD : 1 ≤ D) (hBD : 1/B ≤ D) : positionConstant x B ≤ 6*D^3 := by
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x,abs_nonneg x]
  have hD0 : 0 ≤ D := by linarith
  have hD3 : D ≤ D^3 := by nlinarith [sq_nonneg (D-1),mul_nonneg hD0 (show 0 ≤ D^2-1 by nlinarith)]
  have hb3 : 1/B^3 ≤ D^3 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/B) hBD 3
    simpa only [div_pow,one_pow] using hh
  have hxb : x^2/B^3 ≤ D^3 :=
    (div_le_div_of_nonneg_right hx2 (by positivity)).trans hb3
  calc
    _ = (1/B)/2+4*(x^2/B^3)+1/B^3 := by unfold positionConstant; ring
    _ ≤ D^3/2+4*D^3+D^3 := by gcongr; exact hBD.trans hD3
    _ ≤ _ := by nlinarith [pow_nonneg hD0 3]

lemma position_error_coefficient_bound {x B D : ℝ} (hB : 0 < B) (hx : |x| ≤ 1)
    (hD : 1 ≤ D) (hBD : 1/B ≤ D) :
    48*|x/B| *positionConstant x B+147*positionConstant x B^2 ≤ 6000*D^6 := by
  have hC := positionConstant_nonneg x hB
  have hCb := positionConstant_bound hB hx hD hBD
  have hxB : |x/B| ≤ D := by
    rw [abs_div,abs_of_pos hB]
    exact (div_le_div_of_nonneg_right hx hB.le).trans hBD
  have hD0 : 0 ≤ D := by linarith
  have hD4 : D^4 ≤ D^6 := pow_le_pow_right₀ hD (by norm_num)
  calc
    _ ≤ 48*D*(6*D^3)+147*(6*D^3)^2 := by gcongr
    _ = 288*D^4+5292*D^6 := by ring
    _ ≤ _ := by nlinarith [pow_nonneg hD0 6]

lemma position_remainder_uniform {J x B h E D : ℝ} (hJ : 0 < J) (hB : 0 < B)
    (hx : |x| ≤ 1) (hD : 1 ≤ D) (hBD : 1/B ≤ D) (hh : 0 ≤ h)
    (hscale : J*h^2 ≤ E) (hhE : h ≤ E/Real.sqrt J) :
    J*h^3*(48*|x/B| *positionConstant x B+147*positionConstant x B^2) ≤
      6000*E^2*D^6/Real.sqrt J := by
  have hE : 0 ≤ E := (by positivity : 0 ≤ J*h^2).trans hscale
  have hcoef := position_error_coefficient_bound hB hx hD hBD
  calc
    _ ≤ J*h^3*(6000*D^6) := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = (J*h^2)*h*(6000*D^6) := by ring
    _ ≤ E*(E/Real.sqrt J)*(6000*D^6) := by gcongr
    _ = _ := by ring

-- 显式宽度的实际列位置能量；参数损失是固定的 eps^-2 delta^-6。
theorem explicit_position_error {J eps delta x : ℝ} (hJ : 1 ≤ J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hx : |x| ≤ 1-delta) (hlargeE : 1/eps ≤ J) (hlargeD : 1 ≤ J*delta) :
    |(∫ t, (k J (J*x)-q J t)^2*column (J*x) (Width.width J eps (J*x)) t^2)/J-
      x^2/(2*Width.root eps x)| ≤ 6000/(eps^2*delta^6*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  have hJ0 := ne_of_gt hJp
  let B := Real.sqrt (1-x^2)
  let S := Width.width J eps (J*x)
  let b := 1/(2*Width.root eps x)
  let h := Real.sqrt S/J
  let E := 1/eps
  let D := 1/delta
  have hx1 : |x| ≤ 1 := by linarith
  have hx2 : x^2 ≤ (1-delta)^2 := by nlinarith [sq_abs x,abs_nonneg x]
  have hrad : delta ≤ 1-x^2 := by nlinarith
  have hradp : 0 < 1-x^2 := hd.trans_le hrad
  have hB : 0 < B := Real.sqrt_pos.mpr hradp
  have hBs : B^2=1-x^2 := Real.sq_sqrt hradp.le
  have hdB : delta ≤ B := by nlinarith [sq_nonneg (delta-B)]
  have hBD : 1/B ≤ D := by dsimp [D]; exact one_div_le_one_div_of_le hd hdB
  have hD : 1 ≤ D := by dsimp [D]; exact (le_div_iff₀ hd).2 (by simpa using hd1)
  have hE : 1 ≤ E := by dsimp [E]; exact (le_div_iff₀ heps).2 (by simpa using heps1)
  have hxJ : (J*x)/J=x := by field_simp
  have hbounds := Width.bulk_width_bounds (s := J*x) hJp heps heps1 hd.le
    (by simpa only [hxJ] using hx)
  change J*delta/4 ≤ S ∧ S ≤ J/eps at hbounds
  have hS : 0 < S := (by positivity : 0 < J*delta/4).trans_le hbounds.1
  have hs := Real.sqrt_pos.mpr hS
  have hss := Real.sq_sqrt hS.le
  have hSrepr : S=J*B^2*b := by
    dsimp [S,Width.width,Width.profile,b]
    rw [hxJ,hBs]
    ring
  have hh : 0 < h := div_pos hs hJp
  have hwidth : J*h^2=B^2*b := by
    dsimp [h]
    rw [div_pow,hss,hSrepr]
    field_simp
  have hSmax : S ≤ J^2 := by
    calc
      S ≤ J/eps := hbounds.2
      _ = J*(1/eps) := by ring
      _ ≤ J*J := mul_le_mul_of_nonneg_left hlargeE hJp.le
      _ = J^2 := by ring
  have hsrJ : Real.sqrt S ≤ J := by nlinarith
  have hh1 : h ≤ 1 := (div_le_one hJp).2 hsrJ
  have hSquarter : (1:ℝ)/4 ≤ S := by linarith [hbounds.1]
  have hsrhalf : (1:ℝ)/2 ≤ Real.sqrt S := by nlinarith
  have hstep : 1/(2*J) ≤ h := by
    dsimp [h]
    calc
      _ = ((1:ℝ)/2)/J := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsrhalf hJp.le
  have hscale : J*h^2 ≤ E := by
    have he : J*h^2=S/J := by
      dsimp [h]
      rw [div_pow,hss]
      field_simp
    rw [he]
    apply (div_le_iff₀ hJp).2
    convert hbounds.2 using 1 <;> dsimp [E] <;> ring
  have hSJ : S ≤ J*E := by simpa only [div_eq_mul_inv,one_mul,E] using hbounds.2
  have hsqrtJ := Real.sqrt_pos.mpr hJp
  have hsqJ := Real.sq_sqrt hJp.le
  have hE0 : 0 ≤ E := by linarith
  have hE2 : E ≤ E^2 := by nlinarith only [hE,sq_nonneg (E-1)]
  have hSE : S ≤ J*E^2 := hSJ.trans (mul_le_mul_of_nonneg_left hE2 hJp.le)
  have hJE : (Real.sqrt J*E)^2=J*E^2 := by rw [mul_pow,hsqJ]
  have hsE : Real.sqrt S ≤ Real.sqrt J*E := by
    apply (sq_le_sq₀ hs.le (mul_nonneg hsqrtJ.le hE0)).1
    rw [hss,hJE]
    exact hSE
  have hhE : h ≤ E/Real.sqrt J := by
    dsimp [h]
    apply (div_le_div_iff₀ hJp hsqrtJ).2
    have ht := mul_le_mul_of_nonneg_right hsE hsqrtJ.le
    calc
      _ ≤ (Real.sqrt J*E)*Real.sqrt J := ht
      _ = E*(Real.sqrt J)^2 := by ring
      _ = E*J := by rw [hsqJ]
  have hi := actual_position_error_width hJp hB hBs hh hh1 hstep hwidth
  have hr := position_remainder_uniform hJp hB hx1 hD hBD hh.le hscale hhE
  have hifinal := hi.trans hr
  rw [← hSrepr] at hifinal
  convert hifinal using 1
  · dsimp [S,b]
    ring
  · dsimp [E,D]
    field_simp
    <;> ring

end CopyQuantumMetrology.Bulk

