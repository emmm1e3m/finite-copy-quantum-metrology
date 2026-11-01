import FiniteCopy.BulkAsymptotics
import FiniteCopy.GaussianTransport
import FiniteCopy.GlobalBounds

open MeasureTheory
namespace CopyQuantumMetrology.Bulk

noncomputable def symmetricRoot (x r : ℝ) : ℝ :=
  (clippedRoot (1-(x-r)^2)+clippedRoot (1-(x+r)^2))/2

lemma symmetricRoot_error (x B r : ℝ) (hB : 0 < B) (hBs : B^2=1-x^2)
    (hr : |r| ≤ 1) :
    |symmetricRoot x r - B| ≤ r^2 * positionConstant x B := by
  have hp := position_remainder 1 x B r hB (by simpa using hBs)
  have hn := position_remainder 1 x B (-r) hB (by simpa using hBs)
  have hr2 : r^2 ≤ 1 := by nlinarith [sq_abs r, abs_nonneg r]
  have hr4 : r^4 ≤ r^2 := by nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr2)]
  have hs := add_le_add hn hp
  have ha := abs_add_le (clippedRoot (1-(x-r)^2)-B-x*r/B)
    (clippedRoot (1-(x+r)^2)-B+x*r/B)
  have he : symmetricRoot x r-B =
      ((clippedRoot (1-(x-r)^2)-B-x*r/B)+(clippedRoot (1-(x+r)^2)-B+x*r/B))/2 := by
    unfold symmetricRoot
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
  have hn' : |clippedRoot (1-(x-r)^2)-B-x*r/B| ≤
      (1/(2*B)+4*x^2/B^3)*r^2+r^4/B^3 := by
    simpa [sub_eq_add_neg, mul_neg, neg_div, show (-r)^4=r^4 by ring] using hn
  have hp' : |clippedRoot (1-(x+r)^2)-B+x*r/B| ≤
      (1/(2*B)+4*x^2/B^3)*r^2+r^4/B^3 := by simpa using hp
  have hh := add_le_add hn' hp'
  have hb := div_le_div_of_nonneg_right hr4 (by positivity : 0 ≤ B^3)
  calc
    _ ≤ ((1/(2*B)+4*x^2/B^3)*r^2+r^4/B^3)+
        ((1/(2*B)+4*x^2/B^3)*r^2+r^4/B^3) := ha.trans hh
    _ ≤ ((1/(2*B)+4*x^2/B^3)*r^2+r^2/B^3)+
        ((1/(2*B)+4*x^2/B^3)*r^2+r^2/B^3) := by linarith
    _ = _ := by unfold positionConstant; ring

lemma shifted_position_remainder (x B K h y : ℝ) (hB : 0 < B)
    (hBs : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : |K-B| ≤ h^2*positionConstant x B) :
    |(K-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y| ≤
      h*positionConstant x B*(1+y^2+y^4) := by
  have he : (K-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y =
      (K-B)/h+((B-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y) := by ring
  have hk : |(K-B)/h| ≤ h*positionConstant x B := by
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    convert hK using 1 <;> ring
  rw [he]
  calc
    _ ≤ |(K-B)/h|+|(B-clippedRoot (1-(x+h*y)^2))/h-(x/B)*y| := abs_add_le _ _
    _ ≤ h*positionConstant x B+h*positionConstant x B*(y^2+y^4) :=
      add_le_add hk (scaled_position_remainder x B h y hB hBs hh hh1)
    _ = _ := by ring

noncomputable def shiftedErrorPolynomial (x B y : ℝ) : ℝ :=
  2*|x/B| *positionConstant x B*(1+2*y^2+2*y^4+y^6)+
  positionConstant x B^2*(1+2*y^2+3*y^4+2*y^6+y^8)

lemma shifted_position_square_error (x B K h y : ℝ) (hB : 0 < B)
    (hBs : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : |K-B| ≤ h^2*positionConstant x B) :
    |((K-clippedRoot (1-(x+h*y)^2))/h)^2-((x/B)*y)^2| ≤
      h*shiftedErrorPolynomial x B y := by
  have hC := positionConstant_nonneg x hB
  have hr := square_error_of_remainder (shifted_position_remainder x B K h y hB hBs hh hh1 hK)
  have hy : |y| ≤ 1+y^2 := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  have hy' := mul_le_mul_of_nonneg_right hy (by positivity : 0 ≤ 1+y^2+y^4)
  have hh2 : h^2 ≤ h := by nlinarith
  calc
    _ ≤ 2*|(x/B)*y| *(h*positionConstant x B*(1+y^2+y^4))+
        (h*positionConstant x B*(1+y^2+y^4))^2 := hr
    _ ≤ h*(2*|x/B| *positionConstant x B*((1+y^2)*(1+y^2+y^4)))+
        h*(positionConstant x B^2*(1+y^2+y^4)^2) := by
      rw [abs_mul]
      have ht := mul_le_mul_of_nonneg_left hy' (by positivity : 0 ≤ 2*|x/B| *h*positionConstant x B)
      have hs := mul_le_mul_of_nonneg_right hh2 (by positivity : 0 ≤ positionConstant x B^2*(1+y^2+y^4)^2)
      convert add_le_add ht hs using 1 <;> ring
    _ = _ := by unfold shiftedErrorPolynomial; ring

lemma integrable_standard_density : Integrable (fun y : ℝ => column 0 1 y^2) :=
  integrable_column_sq 0 (by norm_num)
lemma integral_standard_density : (∫ y : ℝ, column 0 1 y^2)=1 :=
  integral_column_sq 0 (by norm_num)

lemma integrable_shifted_error (x B : ℝ) :
    Integrable (fun y => shiftedErrorPolynomial x B y*column 0 1 y^2) := by
  have hp := (((integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2)).add
    ((integrable_standard_moment 4).const_mul 2)).add (integrable_standard_moment 6)).const_mul
      (2*|x/B| *positionConstant x B)
  have hq := ((((integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2)).add
    ((integrable_standard_moment 4).const_mul 3)).add ((integrable_standard_moment 6).const_mul 2)).add
    (integrable_standard_moment 8)).const_mul (positionConstant x B^2)
  convert hp.add hq using 1
  ext y
  simp only [shiftedErrorPolynomial,Pi.add_apply]
  ring

lemma integral_shifted_error (x B : ℝ) :
    (∫ y, shiftedErrorPolynomial x B y*column 0 1 y^2)=
      48*|x/B| *positionConstant x B+147*positionConstant x B^2 := by
  let p := fun y : ℝ => ((column 0 1 y^2+2*(y^2*column 0 1 y^2))+2*(y^4*column 0 1 y^2))+
    y^6*column 0 1 y^2
  let q := fun y : ℝ => (((column 0 1 y^2+2*(y^2*column 0 1 y^2))+3*(y^4*column 0 1 y^2))+
    2*(y^6*column 0 1 y^2))+y^8*column 0 1 y^2
  have hp : Integrable p := ((integrable_standard_density.add
    ((integrable_standard_moment 2).const_mul 2)).add ((integrable_standard_moment 4).const_mul 2)).add
    (integrable_standard_moment 6)
  have hq : Integrable q := (((integrable_standard_density.add
    ((integrable_standard_moment 2).const_mul 2)).add ((integrable_standard_moment 4).const_mul 3)).add
    ((integrable_standard_moment 6).const_mul 2)).add (integrable_standard_moment 8)
  have ep : (∫ y, p y)=24 := by
    dsimp [p]
    have e1 := integral_add ((integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2)).add
      ((integrable_standard_moment 4).const_mul 2)) (integrable_standard_moment 6)
    have e2 := integral_add (integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2))
      ((integrable_standard_moment 4).const_mul 2)
    simp only [Pi.add_apply] at e1 e2
    rw [e1,e2,
      integral_add integrable_standard_density ((integrable_standard_moment 2).const_mul 2)]
    simp only [integral_const_mul, integral_standard_density,integral_standard_second,
      integral_standard_fourth,integral_standard_sixth]
    norm_num
  have eq : (∫ y, q y)=147 := by
    dsimp [q]
    have e1 := integral_add (((integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2)).add
      ((integrable_standard_moment 4).const_mul 3)).add ((integrable_standard_moment 6).const_mul 2))
      (integrable_standard_moment 8)
    have e2 := integral_add ((integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2)).add
      ((integrable_standard_moment 4).const_mul 3)) ((integrable_standard_moment 6).const_mul 2)
    have e3 := integral_add (integrable_standard_density.add ((integrable_standard_moment 2).const_mul 2))
      ((integrable_standard_moment 4).const_mul 3)
    simp only [Pi.add_apply] at e1 e2 e3
    rw [e1,e2,e3,
      integral_add integrable_standard_density ((integrable_standard_moment 2).const_mul 2)]
    simp only [integral_const_mul, integral_standard_density,integral_standard_second,
      integral_standard_fourth,integral_standard_sixth,integral_standard_eighth]
    norm_num
  calc
    _ = ∫ y, (2*|x/B| *positionConstant x B)*p y+positionConstant x B^2*q y := by
      congr 1
      ext y
      dsimp [p,q,shiftedErrorPolynomial]
      ring
    _ = _ := by
      rw [integral_add (hp.const_mul _) (hq.const_mul _),integral_const_mul,integral_const_mul,ep,eq]
      ring

lemma shifted_position_integral_error (x B K h : ℝ) (hB : 0 < B)
    (hBs : B^2=1-x^2) (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : |K-B| ≤ h^2*positionConstant x B) :
    |(∫ y, ((K-clippedRoot (1-(x+h*y)^2))/h)^2*column 0 1 y^2)-(x/B)^2| ≤
      h*(48*|x/B| *positionConstant x B+147*positionConstant x B^2) := by
  have hlin : Integrable (fun y => ((x/B)*y)^2*column 0 1 y^2) := by
    convert (integrable_standard_moment 2).const_mul ((x/B)^2) using 1
    ext y
    ring
  have elin : (∫ y, ((x/B)*y)^2*column 0 1 y^2)=(x/B)^2 := by
    simp_rw [mul_pow,mul_assoc]
    rw [integral_const_mul,integral_standard_second,mul_one]
  have hbound : ∀ᵐ y, ‖(((K-clippedRoot (1-(x+h*y)^2))/h)^2-((x/B)*y)^2)*column 0 1 y^2‖ ≤
      h*(shiftedErrorPolynomial x B y*column 0 1 y^2) := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (column 0 1 y))]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (shifted_position_square_error x B K h y hB hBs hh hh1 hK) (sq_nonneg (column 0 1 y))
  have hd : Integrable (fun y => (((K-clippedRoot (1-(x+h*y)^2))/h)^2-((x/B)*y)^2)*column 0 1 y^2) := by
    apply ((integrable_shifted_error x B).const_mul h).mono' _ hbound
    have hc : Continuous (fun y => (((K-clippedRoot (1-(x+h*y)^2))/h)^2-((x/B)*y)^2)*column 0 1 y^2) := by
      unfold clippedRoot column
      fun_prop
    exact hc.aestronglyMeasurable
  have hf : Integrable (fun y => ((K-clippedRoot (1-(x+h*y)^2))/h)^2*column 0 1 y^2) := by
    convert hd.add hlin using 1
    ext y
    simp only [Pi.add_apply]
    ring
  have he := norm_integral_le_of_norm_le ((integrable_shifted_error x B).const_mul h) hbound
  have ee : (∫ y, (((K-clippedRoot (1-(x+h*y)^2))/h)^2-((x/B)*y)^2)*column 0 1 y^2)=
      (∫ y, ((K-clippedRoot (1-(x+h*y)^2))/h)^2*column 0 1 y^2)-(x/B)^2 := by
    simp_rw [sub_mul]
    rw [integral_sub hf hlin,elin]
  rw [ee,Real.norm_eq_abs,integral_const_mul,integral_shifted_error] at he
  exact he

end CopyQuantumMetrology.Bulk


