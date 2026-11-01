import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

noncomputable section
namespace CopyQuantumMetrology.Width

def root (eps x : ℝ) : ℝ := Real.sqrt (x^2 + eps^2)
def profile (eps x : ℝ) : ℝ := (1-x^2)/(2*root eps x)
def profile₁ (eps x : ℝ) : ℝ := -x*(x^2+2*eps^2+1)/(2*root eps x^3)
def profile₂ (eps x : ℝ) : ℝ :=
  ((2+eps^2)*x^2-eps^2-2*eps^4)/(2*root eps x^5)
def width (J eps s : ℝ) : ℝ := J*profile eps (s/J)
def width₁ (J eps s : ℝ) : ℝ := profile₁ eps (s/J)
def width₂ (J eps s : ℝ) : ℝ := profile₂ eps (s/J)/J

lemma root_pos {eps : ℝ} (heps : 0 < eps) (x : ℝ) : 0 < root eps x := by
  unfold root
  exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])

lemma root_sq (eps x : ℝ) : root eps x^2=x^2+eps^2 := by
  exact Real.sq_sqrt (by positivity)

lemma eps_le_root {eps : ℝ} (heps : 0 < eps) (x : ℝ) : eps ≤ root eps x := by
  have hr := root_pos heps x
  have hs := root_sq eps x
  nlinarith [sq_nonneg x]

lemma root_le_two {eps x : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ 1) : root eps x ≤ 2 := by
  have hs := root_sq eps x
  have hr := root_pos heps x
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have he2 : eps^2 ≤ 1 := by nlinarith
  nlinarith

lemma hasDerivAt_root {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    HasDerivAt (root eps) (x/root eps x) x := by
  have hn : x^2+eps^2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hi : HasDerivAt (fun t : ℝ => t^2+eps^2) (2*x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (eps^2) using 1 <;> simp
  convert hi.sqrt hn using 1
  · rfl
  · unfold root
    ring

lemma hasDerivAt_profile {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    HasDerivAt (profile eps) (profile₁ eps x) x := by
  have hr := (root_pos heps x).ne'
  convert (((hasDerivAt_id x).pow 2).const_sub 1).div
    ((hasDerivAt_root heps x).const_mul 2) (by positivity) using 1
  · rfl
  · simp only [profile₁, id_eq]
    field_simp
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [root_sq]
    ring

lemma profile₁_bound {eps x : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ 1) : |profile₁ eps x| ≤ 2/eps^3 := by
  have hr := root_pos heps x
  have he := eps_le_root heps x
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have he2 : eps^2 ≤ 1 := by nlinarith
  have hn : 0 ≤ x^2+2*eps^2+1 := by positivity
  have hn4 : x^2+2*eps^2+1 ≤ 4 := by linarith
  have hnum : |x| * (x^2+2*eps^2+1) ≤ 4 := by
    calc
      _ ≤ 1 * 4 := mul_le_mul hx hn4 hn (by norm_num)
      _ = 4 := by norm_num
  unfold profile₁
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hn, abs_of_pos (by positivity : 0 < 2*root eps x^3)]
  calc
    _ ≤ 4/(2*root eps x^3) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 4/(2*eps^3) := by gcongr
    _ = 2/eps^3 := by ring

lemma hasDerivAt_width {J eps : ℝ} (hJ : J ≠ 0) (heps : 0 < eps) (s : ℝ) :
    HasDerivAt (width J eps) (width₁ J eps s) s := by
  have h := ((hasDerivAt_profile heps (s/J)).comp s ((hasDerivAt_id s).div_const J)).const_mul J
  convert h using 1
  · rfl
  · dsimp [width₁]
    field_simp

lemma width₁_bound {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (heps1 : eps ≤ 1) (hs : |s| ≤ J) : |width₁ J eps s| ≤ 2/eps^3 := by
  apply profile₁_bound heps heps1
  rw [abs_div, abs_of_pos hJ]
  exact (div_le_one hJ).2 hs

lemma width_eq_radial {J : ℝ} (hJ : J ≠ 0) (eps s : ℝ) :
    width J eps s = (J^2-s^2)/(2*J*root eps (s/J)) := by
  unfold width profile
  field_simp

lemma radial_bounds {J s : ℝ} (hJ : 0 < J) (hs : |s| ≤ J) :
    J*(J-|s|) ≤ J^2-s^2 ∧ J^2-s^2 ≤ 2*J*(J-|s|) := by
  have h0 := abs_nonneg s
  have hsq := sq_abs s
  have hp := mul_nonneg h0 (sub_nonneg.mpr hs)
  have hq := sq_nonneg (J-|s|)
  constructor <;> nlinarith

lemma width_lower {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (heps1 : eps ≤ 1) (hs : |s| ≤ J) : (J-|s|)/4 ≤ width J eps s := by
  have hx : |s/J| ≤ 1 := by rw [abs_div, abs_of_pos hJ]; exact (div_le_one hJ).2 hs
  have hr := root_pos heps (s/J)
  have hu := root_le_two heps heps1 hx
  have hrad := (radial_bounds hJ hs).1
  have hn : 0 ≤ J-|s| := sub_nonneg.mpr hs
  rw [width_eq_radial hJ.ne']
  apply (le_div_iff₀ (by positivity : 0 < 2*J*root eps (s/J))).2
  have hm := mul_le_mul_of_nonneg_left hu (mul_nonneg hJ.le hn)
  nlinarith

lemma width_upper {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (hs : |s| ≤ J) : width J eps s ≤ (J-|s|)/eps := by
  have hr := root_pos heps (s/J)
  have hl := eps_le_root heps (s/J)
  have hrad := (radial_bounds hJ hs).2
  have hn : 0 ≤ J-|s| := sub_nonneg.mpr hs
  rw [width_eq_radial hJ.ne']
  apply (div_le_div_iff₀ (by positivity : 0 < 2*J*root eps (s/J)) heps).2
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2*J*(J-|s|))
  have hh := mul_le_mul_of_nonneg_right hrad heps.le
  nlinarith

lemma hasDerivAt_profile₁ {eps : ℝ} (heps : 0 < eps) (x : ℝ) :
    HasDerivAt (profile₁ eps) (profile₂ eps x) x := by
  have hr := (root_pos heps x).ne'
  have hn : HasDerivAt (fun y : ℝ => -y*(y^2+2*eps^2+1))
      (-(3*x^2+2*eps^2+1)) x := by
    convert (hasDerivAt_id x).neg.mul
      ((((hasDerivAt_id x).pow 2).add_const (2*eps^2)).add_const 1) using 1
    · ext y
      rfl
    · simp only [Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  convert hn.div (((hasDerivAt_root heps x).pow 3).const_mul 2)
    (by change 2*root eps x^3 ≠ 0; positivity) using 1
  · rfl
  · unfold profile₂
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
    field_simp
    rw [root_sq]
    ring

lemma profile₂_bound {eps x : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ 1) : |profile₂ eps x| ≤ 3/eps^5 := by
  have hr := root_pos heps x
  have he := eps_le_root heps x
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have he2 : eps^2 ≤ 1 := by nlinarith
  have he4 : eps^4 ≤ 1 := by nlinarith [sq_nonneg (eps^2-1)]
  have ha : 0 ≤ 2+eps^2 := by positivity
  have ha2 : 2+eps^2 ≤ 3 := by linarith
  have hm : (2+eps^2)*x^2 ≤ 3 := by
    calc
      _ ≤ 3*1 := mul_le_mul ha2 hx2 (sq_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  have hmn : 0 ≤ (2+eps^2)*x^2 := mul_nonneg ha (sq_nonneg _)
  have hnum : |(2+eps^2)*x^2-eps^2-2*eps^4| ≤ 6 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg eps, pow_nonneg heps.le 4]
  unfold profile₂
  rw [abs_div, abs_of_pos (by positivity : 0 < 2*root eps x^5)]
  calc
    _ ≤ 6/(2*root eps x^5) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 6/(2*eps^5) := by gcongr
    _ = 3/eps^5 := by ring

lemma hasDerivAt_width₁ {J eps : ℝ} (heps : 0 < eps) (s : ℝ) :
    HasDerivAt (width₁ J eps) (width₂ J eps s) s := by
  convert (hasDerivAt_profile₁ heps (s/J)).comp s ((hasDerivAt_id s).div_const J) using 1
  · rfl
  · unfold width₂
    ring

lemma width₂_bound {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (heps1 : eps ≤ 1) (hs : |s| ≤ J) : |width₂ J eps s| ≤ 3/(J*eps^5) := by
  have hx : |s/J| ≤ 1 := by rw [abs_div, abs_of_pos hJ]; exact (div_le_one hJ).2 hs
  unfold width₂
  rw [abs_div, abs_of_pos hJ]
  calc
    _ ≤ (3/eps^5)/J := div_le_div_of_nonneg_right (profile₂_bound heps heps1 hx) hJ.le
    _ = 3/(J*eps^5) := by ring

lemma deriv_width {J eps : ℝ} (hJ : J ≠ 0) (heps : 0 < eps) :
    deriv (width J eps) = width₁ J eps := by
  funext s
  exact (hasDerivAt_width hJ heps s).deriv

lemma deriv_deriv_width {J eps : ℝ} (hJ : J ≠ 0) (heps : 0 < eps) :
    deriv (deriv (width J eps)) = width₂ J eps := by
  rw [deriv_width hJ heps]
  funext s
  exact (hasDerivAt_width₁ heps s).deriv

lemma continuous_width {J eps : ℝ} (hJ : J ≠ 0) (heps : 0 < eps) :
    Continuous (width J eps) := by
  exact continuous_iff_continuousAt.mpr fun s => (hasDerivAt_width hJ heps s).continuousAt

lemma continuous_width₁ {J eps : ℝ} (heps : 0 < eps) :
    Continuous (width₁ J eps) := by
  exact continuous_iff_continuousAt.mpr fun s => (hasDerivAt_width₁ heps s).continuousAt

lemma continuous_width₂ {J eps : ℝ} (heps : 0 < eps) :
    Continuous (width₂ J eps) := by
  have hc : Continuous (fun s : ℝ => root eps (s/J)) := by unfold root; fun_prop
  have hn : Continuous (fun s : ℝ => (2+eps^2)*(s/J)^2-eps^2-2*eps^4) := by fun_prop
  have hd : Continuous (fun s : ℝ => 2*root eps (s/J)^5) := (hc.pow 5).const_mul 2
  exact (hn.div hd (fun s => by have hr := root_pos heps (s/J); positivity)).div_const J

lemma width_pos {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (hs : |s| < J) : 0 < width J eps s := by
  have hrad : 0 < J^2-s^2 := by
    nlinarith [sq_abs s, abs_nonneg s]
  rw [width_eq_radial hJ.ne']
  exact div_pos hrad (by have hr := root_pos heps (s/J); positivity)

lemma bulk_width_bounds {J eps s delta : ℝ} (hJ : 0 < J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 ≤ delta)
    (hs : |s/J| ≤ 1-delta) : J*delta/4 ≤ width J eps s ∧ width J eps s ≤ J/eps := by
  have hs' : |s| ≤ J*(1-delta) := by
    rw [abs_div, abs_of_pos hJ] at hs
    exact (div_le_iff₀ hJ).1 hs |>.trans_eq (by ring)
  have hsJ : |s| ≤ J := by nlinarith
  constructor
  · exact (by nlinarith : J*delta/4 ≤ (J-|s|)/4).trans (width_lower hJ heps heps1 hsJ)
  · exact (width_upper hJ heps hsJ).trans
      (div_le_div_of_nonneg_right (by linarith [abs_nonneg s]) heps.le)

end CopyQuantumMetrology.Width
