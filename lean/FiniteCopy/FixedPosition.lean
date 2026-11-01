import FiniteCopy.FixedDefinitions
import FiniteCopy.PositionUniform
open MeasureTheory
namespace CopyQuantumMetrology.FixedWidth
open GlobalBounds Bulk

lemma I_global {b : ℝ → ℝ} {J m L M : ℝ} (hJ : 1 ≤ J) (hL : 0 < L)
    (hb : ∀ x ∈ Set.Icc (-1:ℝ) 1, L ≤ b x ∧ b x ≤ M) (hm : |m| ≤ J-1/2) :
    I b J m ≤ (5/2+16*M+12*M^2)*J := by
  have hJp : 0 < J := by linarith
  have hx : |m/J| ≤ 1 := by
    rw [abs_div,abs_of_pos hJp]
    apply (div_le_one hJp).2
    linarith
  have hbm := hb (m/J) (abs_le.mp hx)
  exact gaussian_energy_uniform_of_width_bound hJ (hL.trans_le hbm.1) hbm.2 hm

-- 固定b的真实位置积分；只需该点的正上下界，不预设能量误差。
theorem I_bulk {b : ℝ → ℝ} {J x L M delta : ℝ} (hJ : 1 ≤ J)
    (hL : 0 < L) (hM : 1 ≤ M) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hx : |x| ≤ 1-delta) (hbL : L ≤ b x) (hbM : b x ≤ M)
    (hlargeM : M ≤ J) (hlargeL : 1 ≤ J*delta*L) :
    |I b J (J*x)/J-positionProfile b x| ≤ 6000*M^2/(delta^6*Real.sqrt J) := by
  have hJp : 0 < J := by linarith
  have hJ0 := ne_of_gt hJp
  have hbpos : 0 < b x := hL.trans_le hbL
  let B := Real.sqrt (1-x^2)
  let S := width b J (J*x)
  let h := Real.sqrt S/J
  let D := 1/delta
  have hx1 : |x| ≤ 1 := by linarith
  have hx2 : x^2 ≤ (1-delta)^2 := by nlinarith [sq_abs x,abs_nonneg x]
  have hrad : delta ≤ 1-x^2 := by nlinarith
  have hradp : 0 < 1-x^2 := hd.trans_le hrad
  have hB : 0 < B := Real.sqrt_pos.mpr hradp
  have hBs : B^2=1-x^2 := Real.sq_sqrt hradp.le
  have hBs1 : B^2 ≤ 1 := by nlinarith only [hBs,sq_nonneg x]
  have hdB : delta ≤ B := by nlinarith only [hBs,hrad,hd,hd1,hB,sq_nonneg (delta-B)]
  have hBD : 1/B ≤ D := by dsimp [D]; exact one_div_le_one_div_of_le hd hdB
  have hD : 1 ≤ D := by dsimp [D]; exact (le_div_iff₀ hd).2 (by simpa using hd1)
  have hxJ : (J*x)/J=x := by field_simp
  have hSrepr : S=J*B^2*b x := by
    dsimp [S,width,GlobalBounds.width]
    rw [hxJ,hBs]
  have hSlow : J*delta*L ≤ S := by
    rw [hSrepr]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by rw [hBs]; exact hrad) hJp.le
    · exact hbL
    · exact hL.le
    · positivity
  have hSup : S ≤ J*M := by
    rw [hSrepr]
    calc
      _ ≤ (J*1)*M := mul_le_mul (mul_le_mul_of_nonneg_left hBs1 hJp.le) hbM hbpos.le (by positivity)
      _ = _ := by ring
  have hS : 0 < S := (by positivity : 0 < J*delta*L).trans_le hSlow
  have hs := Real.sqrt_pos.mpr hS
  have hss := Real.sq_sqrt hS.le
  have hh : 0 < h := div_pos hs hJp
  have hwidth : J*h^2=B^2*b x := by
    dsimp [h]
    rw [div_pow,hss,hSrepr]
    field_simp
  have hSmax : S ≤ J^2 := hSup.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlargeM hJp.le])
  have hsrJ : Real.sqrt S ≤ J := (sq_le_sq₀ hs.le hJp.le).1 (by rw [hss]; exact hSmax)
  have hh1 : h ≤ 1 := (div_le_one hJp).2 hsrJ
  have hSquarter : (1:ℝ)/4 ≤ S := by linarith only [hlargeL,hSlow]
  have hsrhalf : (1:ℝ)/2 ≤ Real.sqrt S := by nlinarith only [hs,hss,hSquarter]
  have hstep : 1/(2*J) ≤ h := by
    dsimp [h]
    calc
      _ = ((1:ℝ)/2)/J := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsrhalf hJp.le
  have hscale : J*h^2 ≤ M := by
    have he : J*h^2=S/J := by
      dsimp [h]
      rw [div_pow,hss]
      field_simp
    rw [he]
    apply (div_le_iff₀ hJp).2
    simpa only [mul_comm] using hSup
  have hsqrtJ := Real.sqrt_pos.mpr hJp
  have hsqJ := Real.sq_sqrt hJp.le
  have hM0 : 0 ≤ M := by linarith
  have hM2 : M ≤ M^2 := by nlinarith only [hM,sq_nonneg (M-1)]
  have hSM : S ≤ J*M^2 := hSup.trans (mul_le_mul_of_nonneg_left hM2 hJp.le)
  have hJM : (Real.sqrt J*M)^2=J*M^2 := by rw [mul_pow,hsqJ]
  have hsM : Real.sqrt S ≤ Real.sqrt J*M := by
    apply (sq_le_sq₀ hs.le (mul_nonneg hsqrtJ.le hM0)).1
    rw [hss,hJM]
    exact hSM
  have hhM : h ≤ M/Real.sqrt J := by
    dsimp [h]
    apply (div_le_div_iff₀ hJp hsqrtJ).2
    calc
      _ ≤ (Real.sqrt J*M)*Real.sqrt J := mul_le_mul_of_nonneg_right hsM hsqrtJ.le
      _ = M*(Real.sqrt J)^2 := by ring
      _ = M*J := by rw [hsqJ]
  have hi := actual_position_error_width hJp hB hBs hh hh1 hstep hwidth
  have hr := position_remainder_uniform hJp hB hx1 hD hBD hh.le hscale hhM
  have hhfinal := hi.trans hr
  rw [← hSrepr] at hhfinal
  convert hhfinal using 1
  · rfl
  · dsimp [D]
    field_simp

end CopyQuantumMetrology.FixedWidth
