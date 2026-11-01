import FiniteCopy.Gaussian
import FiniteCopy.GlobalBounds
import FiniteCopy.Width
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace CopyQuantumMetrology.SecondDerivative

-- 均值速度为1、均值加速度为0时的真实二阶导数。
def second (m S S₁ S₂ t : ℝ) : ℝ :=
  column m S t * (columnScore m S 1 S₁ t ^ 2 + columnScoreDeriv m S 1 S₁ 0 S₂ t)

def evenPolynomial (m a b c d e t : ℝ) : ℝ :=
  a + b*(t-m)^2 + c*(t-m)^4 + d*(t-m)^6 + e*(t-m)^8

lemma integrable_evenPolynomial (m a b c d e : ℝ) {S : ℝ} (hS : 0 < S) :
    Integrable (fun t => evenPolynomial m a b c d e t * column m S t ^ 2) := by
  convert ((((integrable_column_sq m hS).const_mul a).add
    ((integrable_centered_pow_column_sq m hS 2).const_mul b)).add
    ((integrable_centered_pow_column_sq m hS 4).const_mul c)).add
    ((integrable_centered_pow_column_sq m hS 6).const_mul d) |>.add
    ((integrable_centered_pow_column_sq m hS 8).const_mul e) using 1
  ext t
  simp only [evenPolynomial, Pi.add_apply]
  ring

lemma integral_evenPolynomial (m a b c d e : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, evenPolynomial m a b c d e t * column m S t ^ 2) =
      a + b*S + c*(3*S^2) + d*(15*S^3) + e*(105*S^4) := by
  have h0 := integrable_column_sq m hS
  have h2 := integrable_centered_pow_column_sq m hS 2
  have h4 := integrable_centered_pow_column_sq m hS 4
  have h6 := integrable_centered_pow_column_sq m hS 6
  have h8 := integrable_centered_pow_column_sq m hS 8
  have he : (fun t => evenPolynomial m a b c d e t * column m S t ^ 2) =
      fun t => a*column m S t^2 + b*((t-m)^2*column m S t^2) +
        c*((t-m)^4*column m S t^2) + d*((t-m)^6*column m S t^2) +
        e*((t-m)^8*column m S t^2) := by funext t; unfold evenPolynomial; ring
  have he4 := integral_add ((((h0.const_mul a).add (h2.const_mul b)).add
    (h4.const_mul c)).add (h6.const_mul d)) (h8.const_mul e)
  have he3 := integral_add (((h0.const_mul a).add (h2.const_mul b)).add
    (h4.const_mul c)) (h6.const_mul d)
  have he2 := integral_add ((h0.const_mul a).add (h2.const_mul b)) (h4.const_mul c)
  have he1 := integral_add (h0.const_mul a) (h2.const_mul b)
  simp only [Pi.add_apply] at he4 he3 he2 he1
  rw [he, he4, he3, he2, he1]
  simp only [integral_const_mul, integral_column_sq m hS,
    integral_centered_sq_column_sq m hS, integral_centered_fourth_column_sq m hS,
    integral_centered_sixth_column_sq m hS, integral_centered_eighth_column_sq m hS, mul_one]

def partA (m S t : ℝ) : ℝ := -1/(2*S)+(t-m)^2/(4*S^2)
def partB (m S S₁ t : ℝ) : ℝ := S₁*(-5*(t-m)/(4*S^2)+(t-m)^3/(4*S^3))
def partC (m S S₂ t : ℝ) : ℝ := S₂*(-1/(4*S)+(t-m)^2/(4*S^2))
def partD (m S S₁ t : ℝ) : ℝ := S₁^2*(5/(16*S^2)-5*(t-m)^2/(8*S^3)+(t-m)^4/(16*S^4))

lemma second_eq_parts (m S S₁ S₂ t : ℝ) :
    second m S S₁ S₂ t = column m S t *
      (partA m S t + partB m S S₁ t + partC m S S₂ t + partD m S S₁ t) := by
  unfold second columnScore columnScoreDeriv partA partB partC partD
  ring

lemma square_four_le (a b c d : ℝ) :
    (a+b+c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

lemma partA_sq (m S t : ℝ) :
    partA m S t^2 = evenPolynomial m (1/(4*S^2)) (-1/(4*S^3)) (1/(16*S^4)) 0 0 t := by
  unfold partA evenPolynomial
  ring

lemma partB_sq (m S S₁ t : ℝ) :
    partB m S S₁ t^2 = evenPolynomial m 0 (25*S₁^2/(16*S^4))
      (-5*S₁^2/(8*S^5)) (S₁^2/(16*S^6)) 0 t := by
  unfold partB evenPolynomial
  ring

lemma partC_sq (m S S₂ t : ℝ) :
    partC m S S₂ t^2 = evenPolynomial m (S₂^2/(16*S^2))
      (-S₂^2/(8*S^3)) (S₂^2/(16*S^4)) 0 0 t := by
  unfold partC evenPolynomial
  ring

lemma partD_sq (m S S₁ t : ℝ) :
    partD m S S₁ t^2 = evenPolynomial m (25*S₁^4/(256*S^4))
      (-25*S₁^4/(64*S^5)) (55*S₁^4/(128*S^6))
      (-5*S₁^4/(64*S^7)) (S₁^4/(256*S^8)) t := by
  unfold partD evenPolynomial
  ring

lemma integrable_parts (m S₁ S₂ : ℝ) {S : ℝ} (hS : 0 < S) :
    Integrable (fun t => partA m S t^2 * column m S t^2) ∧
    Integrable (fun t => partB m S S₁ t^2 * column m S t^2) ∧
    Integrable (fun t => partC m S S₂ t^2 * column m S t^2) ∧
    Integrable (fun t => partD m S S₁ t^2 * column m S t^2) := by
  simp_rw [partA_sq, partB_sq, partC_sq, partD_sq]
  exact ⟨integrable_evenPolynomial _ _ _ _ _ _ hS,
    integrable_evenPolynomial _ _ _ _ _ _ hS,
    integrable_evenPolynomial _ _ _ _ _ _ hS,
    integrable_evenPolynomial _ _ _ _ _ _ hS⟩

lemma integral_parts (m S₁ S₂ : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, partA m S t^2 * column m S t^2) = 3/(16*S^2) ∧
    (∫ t, partB m S S₁ t^2 * column m S t^2) = 5*S₁^2/(8*S^3) ∧
    (∫ t, partC m S S₂ t^2 * column m S t^2) = S₂^2/(8*S^2) ∧
    (∫ t, partD m S S₁ t^2 * column m S t^2) = 15*S₁^4/(64*S^4) := by
  simp_rw [partA_sq, partB_sq, partC_sq, partD_sq, integral_evenPolynomial _ _ _ _ _ _ hS]
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

def majorant (m S S₁ S₂ t : ℝ) : ℝ :=
  4*(partA m S t^2*column m S t^2 + partB m S S₁ t^2*column m S t^2 +
    partC m S S₂ t^2*column m S t^2 + partD m S S₁ t^2*column m S t^2)

lemma second_sq_le_majorant (m S S₁ S₂ t : ℝ) :
    second m S S₁ S₂ t^2 ≤ majorant m S S₁ S₂ t := by
  rw [second_eq_parts]
  have hh := mul_le_mul_of_nonneg_right
    (square_four_le (partA m S t) (partB m S S₁ t) (partC m S S₂ t) (partD m S S₁ t))
    (sq_nonneg (column m S t))
  unfold majorant
  convert hh using 1 <;> ring

lemma integrable_majorant (m S₁ S₂ : ℝ) {S : ℝ} (hS : 0 < S) :
    Integrable (majorant m S S₁ S₂) := by
  obtain ⟨ha,hb,hc,hd⟩ := integrable_parts m S₁ S₂ hS
  exact ((ha.add hb).add hc |>.add hd).const_mul 4

lemma continuous_second (m S S₁ S₂ : ℝ) : Continuous (second m S S₁ S₂) := by
  unfold second column columnScore columnScoreDeriv
  fun_prop

lemma integrable_second_sq (m S₁ S₂ : ℝ) {S : ℝ} (hS : 0 < S) :
    Integrable (fun t => second m S S₁ S₂ t^2) := by
  apply (integrable_majorant m S₁ S₂ hS).mono'
    ((continuous_second m S S₁ S₂).pow 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact second_sq_le_majorant m S S₁ S₂ t

def budget (S S₁ S₂ : ℝ) : ℝ :=
  3*((S⁻¹)^2 + S₁^2*(S⁻¹)^3 + S₂^2*(S⁻¹)^2 + S₁^4*(S⁻¹)^4)

theorem integral_second_sq_le (m S₁ S₂ : ℝ) {S : ℝ} (hS : 0 < S) :
    (∫ t, second m S S₁ S₂ t^2) ≤ budget S S₁ S₂ := by
  obtain ⟨ha,hb,hc,hd⟩ := integrable_parts m S₁ S₂ hS
  obtain ⟨ha',hb',hc',hd'⟩ := integral_parts m S₁ S₂ hS
  calc
    _ ≤ ∫ t, majorant m S S₁ S₂ t := integral_mono
      (integrable_second_sq m S₁ S₂ hS) (integrable_majorant m S₁ S₂ hS)
      (second_sq_le_majorant m S S₁ S₂)
    _ = 3/4*(S⁻¹)^2 + 5/2*S₁^2*(S⁻¹)^3 + 1/2*S₂^2*(S⁻¹)^2 +
        15/16*S₁^4*(S⁻¹)^4 := by
      unfold majorant
      have h3 := integral_add ((ha.add hb).add hc) hd
      have h2 := integral_add (ha.add hb) hc
      have h1 := integral_add ha hb
      simp only [Pi.add_apply] at h3 h2 h1
      rw [integral_const_mul, h3, h2, h1, ha', hb', hc', hd']
      ring
    _ ≤ _ := by
      unfold budget
      have h1 : 0 ≤ (S⁻¹)^2 := by positivity
      have h2 : 0 ≤ S₁^2*(S⁻¹)^3 := by positivity
      have h3 : 0 ≤ S₂^2*(S⁻¹)^2 := by positivity
      have h4 : 0 ≤ S₁^4*(S⁻¹)^4 := by positivity
      nlinarith

lemma q_le_J {J : ℝ} (hJ : 0 ≤ J) (t : ℝ) : GlobalBounds.q J t ≤ J := by
  nlinarith [GlobalBounds.q_sq_le J t, GlobalBounds.q_nonneg J t]

lemma integrable_weighted_second_sq (m S₁ S₂ : ℝ) {J S : ℝ}
    (hJ : 0 ≤ J) (hS : 0 < S) :
    Integrable (fun t => GlobalBounds.q J t * second m S S₁ S₂ t^2) := by
  apply ((integrable_second_sq m S₁ S₂ hS).const_mul J).mono'
    ((GlobalBounds.continuous_q J).mul ((continuous_second m S S₁ S₂).pow 2)).aestronglyMeasurable
  filter_upwards [] with t
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (GlobalBounds.q_nonneg J t) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (q_le_J hJ t) (sq_nonneg _)

theorem integral_weighted_second_sq_le (m S₁ S₂ : ℝ) {J S : ℝ}
    (hJ : 0 ≤ J) (hS : 0 < S) :
    (∫ t, GlobalBounds.q J t * second m S S₁ S₂ t^2) ≤ J * budget S S₁ S₂ := by
  calc
    _ ≤ ∫ t, J * second m S S₁ S₂ t^2 := integral_mono
      (integrable_weighted_second_sq m S₁ S₂ hJ hS)
      ((integrable_second_sq m S₁ S₂ hS).const_mul J)
      (fun t => mul_le_mul_of_nonneg_right (q_le_J hJ t) (sq_nonneg _))
    _ = J*(∫ t, second m S S₁ S₂ t^2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_second_sq_le m S₁ S₂ hS) hJ

def regularizedFirst (J eps s t : ℝ) : ℝ :=
  column s (Width.width J eps s) t * columnScore s (Width.width J eps s) 1 (Width.width₁ J eps s) t

def regularizedSecond (J eps s t : ℝ) : ℝ :=
  second s (Width.width J eps s) (Width.width₁ J eps s) (Width.width₂ J eps s) t

lemma hasDerivAt_regularizedColumn {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (hs : |s| < J) (t : ℝ) :
    HasDerivAt (fun x => column x (Width.width J eps x) t) (regularizedFirst J eps s t) s := by
  exact hasDerivAt_column t (hasDerivAt_id s) (Width.hasDerivAt_width hJ.ne' heps s)
    (Width.width_pos hJ heps hs)

lemma regularizedFirst_eq (J eps s t : ℝ) :
    regularizedFirst J eps s t = column s (Width.width J eps s) t *
      ((t-s)/(2*Width.width J eps s) + Width.width₁ J eps s/(4*Width.width J eps s)*
        ((t-s)^2/Width.width J eps s-1)) := by
  unfold regularizedFirst columnScore
  ring

lemma hasDerivAt_regularizedFirst {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (hs : |s| < J) (t : ℝ) :
    HasDerivAt (fun x => regularizedFirst J eps x t) (regularizedSecond J eps s t) s := by
  exact hasDerivAt_column_first t (hasDerivAt_id s) (Width.hasDerivAt_width hJ.ne' heps s)
    (hasDerivAt_const s 1) (Width.hasDerivAt_width₁ heps s) (Width.width_pos hJ heps hs)

lemma deriv_deriv_column_eq {J eps s : ℝ} (hJ : 0 < J) (heps : 0 < eps)
    (hs : |s| < J) (t : ℝ) :
    deriv (deriv (fun x => column x (Width.width J eps x) t)) s = regularizedSecond J eps s t := by
  exact (hasDerivAt_deriv_column t (Filter.Eventually.of_forall (fun x => hasDerivAt_id x))
    (Filter.Eventually.of_forall (fun x => Width.hasDerivAt_width hJ.ne' heps x))
    (hasDerivAt_const s 1) (Width.hasDerivAt_width₁ heps s) (Width.width_pos hJ heps hs)).deriv

lemma budget_le_scaled {S S₁ S₂ u E D : ℝ} (hS : 0 < S)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hE : 1 ≤ E) (hD : 1 ≤ D)
    (hSi : S⁻¹ ≤ 4*u*D) (h1 : |S₁| ≤ 2*E^3) (h2 : |S₂| ≤ 3*u*E^5) :
    budget S S₁ S₂ ≤ 13536*u^2*E^12*D^4 := by
  have hE0 : 0 ≤ E := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hSi0 : 0 ≤ S⁻¹ := by positivity
  have hu2 : u^2 ≤ 1 := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hu3 : u^3 ≤ u^2 := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
  have hu4 : u^4 ≤ u^2 := by nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  have hE12 : 1 ≤ E^12 := one_le_pow₀ hE
  have hE6 : E^6 ≤ E^12 := pow_le_pow_right₀ hE (by norm_num)
  have hE10 : E^10 ≤ E^12 := pow_le_pow_right₀ hE (by norm_num)
  have hD2 : D^2 ≤ D^4 := pow_le_pow_right₀ hD (by norm_num)
  have hD3 : D^3 ≤ D^4 := pow_le_pow_right₀ hD (by norm_num)
  have h1sq : S₁^2 ≤ (2*E^3)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg S₁) (by positivity)).2 h1
  have h2sq : S₂^2 ≤ (3*u*E^5)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg S₂) (by positivity)).2 h2
  have h1four : S₁^4 ≤ (2*E^3)^4 := by
    calc
      _ = (S₁^2)^2 := by ring
      _ ≤ ((2*E^3)^2)^2 := by gcongr
      _ = _ := by ring
  have ha : (S⁻¹)^2 ≤ 16*u^2*E^12*D^4 := by
    calc
      _ ≤ (4*u*D)^2 := by gcongr
      _ = 16*u^2*1*D^2 := by ring
      _ ≤ _ := by gcongr
  have hb : S₁^2*(S⁻¹)^3 ≤ 256*u^2*E^12*D^4 := by
    calc
      _ ≤ (2*E^3)^2*(4*u*D)^3 := by gcongr
      _ = 256*u^3*E^6*D^3 := by ring
      _ ≤ _ := by gcongr
  have hc : S₂^2*(S⁻¹)^2 ≤ 144*u^2*E^12*D^4 := by
    calc
      _ ≤ (3*u*E^5)^2*(4*u*D)^2 := by gcongr
      _ = 144*u^4*E^10*D^2 := by ring
      _ ≤ _ := by gcongr
  have hd : S₁^4*(S⁻¹)^4 ≤ 4096*u^2*E^12*D^4 := by
    calc
      _ ≤ (2*E^3)^4*(4*u*D)^4 := by gcongr
      _ = 4096*u^4*E^12*D^4 := by ring
      _ ≤ _ := by gcongr
  unfold budget
  nlinarith

theorem regularized_budget_bulk {J eps delta s : ℝ} (hJ : 1 ≤ J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hs : |s/J| ≤ 1-delta) :
    J * budget (Width.width J eps s) (Width.width₁ J eps s) (Width.width₂ J eps s) ≤
      16384/(J*eps^12*delta^4) := by
  have hJp : 0 < J := by linarith
  have hsJ : |s| ≤ J := by
    rw [abs_div, abs_of_pos hJp] at hs
    have hh := (div_le_iff₀ hJp).1 hs
    nlinarith
  have hw := Width.bulk_width_bounds hJp heps heps1 hd.le hs
  have hS : 0 < Width.width J eps s := lt_of_lt_of_le (by positivity) hw.1
  have hSi : (Width.width J eps s)⁻¹ ≤ 4*J⁻¹*delta⁻¹ := by
    calc
      _ ≤ (J*delta/4)⁻¹ := inv_anti₀ (by positivity) hw.1
      _ = _ := by ring
  have h1 : |Width.width₁ J eps s| ≤ 2*(eps⁻¹)^3 := by
    convert Width.width₁_bound hJp heps heps1 hsJ using 1 <;> ring
  have h2 : |Width.width₂ J eps s| ≤ 3*J⁻¹*(eps⁻¹)^5 := by
    convert Width.width₂_bound hJp heps heps1 hsJ using 1 <;> ring
  have hbud := budget_le_scaled hS (by positivity : 0 ≤ J⁻¹)
    (inv_le_one₀ hJp |>.2 hJ) ((one_le_inv₀ heps).2 heps1) ((one_le_inv₀ hd).2 hd1) hSi h1 h2
  calc
    _ ≤ J*(13536*(J⁻¹)^2*(eps⁻¹)^12*(delta⁻¹)^4) :=
      mul_le_mul_of_nonneg_left hbud hJp.le
    _ = 13536/(J*eps^12*delta^4) := by field_simp
    _ ≤ _ := by gcongr <;> norm_num

theorem regularized_second_bulk {J eps delta s : ℝ} (hJ : 1 ≤ J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hs : |s/J| ≤ 1-delta) :
    (∫ t, GlobalBounds.q J t * regularizedSecond J eps s t^2) ≤
      16384/(J*eps^12*delta^4) := by
  have hJp : 0 < J := by linarith
  have hw := Width.bulk_width_bounds hJp heps heps1 hd.le hs
  have hS : 0 < Width.width J eps s := lt_of_lt_of_le (by positivity) hw.1
  exact (integral_weighted_second_sq_le s (Width.width₁ J eps s) (Width.width₂ J eps s)
    hJp.le hS).trans (regularized_budget_bulk hJ heps heps1 hd hd1 hs)

-- 终端界直接写在原始Gaussian幅值的真实迭代导数上。
theorem deriv_deriv_column_bulk {J eps delta s : ℝ} (hJ : 1 ≤ J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hs : |s/J| ≤ 1-delta) :
    (∫ t, GlobalBounds.q J t * (deriv (deriv (fun x => column x (Width.width J eps x) t)) s)^2) ≤
      16384/(J*eps^12*delta^4) := by
  have hJp : 0 < J := by linarith
  have hsJ : |s| < J := by
    rw [abs_div, abs_of_pos hJp] at hs
    have hh := (div_le_iff₀ hJp).1 hs
    nlinarith
  simp_rw [deriv_deriv_column_eq hJp heps hsJ]
  exact regularized_second_bulk hJ heps heps1 hd hd1 hs

lemma integrable_regularized_second_bulk {J eps delta s : ℝ} (hJ : 0 < J)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hd : 0 < delta)
    (hs : |s/J| ≤ 1-delta) :
    Integrable (fun t => GlobalBounds.q J t * regularizedSecond J eps s t^2) := by
  have hw := Width.bulk_width_bounds hJ heps heps1 hd.le hs
  have hS : 0 < Width.width J eps s := lt_of_lt_of_le (by positivity) hw.1
  exact integrable_weighted_second_sq s (Width.width₁ J eps s) (Width.width₂ J eps s) hJ.le hS

lemma continuousOn_second {S S₁ S₂ : ℝ → ℝ} {a : ℝ}
    (hS : ContinuousOn S (Set.Icc a (a+1)))
    (hS₁ : ContinuousOn S₁ (Set.Icc a (a+1)))
    (hS₂ : ContinuousOn S₂ (Set.Icc a (a+1)))
    (hpos : ∀ s ∈ Set.Icc a (a+1), 0 < S s) :
    ContinuousOn (fun p : ℝ × ℝ => second p.1 (S p.1) (S₁ p.1) (S₂ p.1) p.2)
      ((Set.Icc a (a+1)) ×ˢ Set.univ) := by
  have hSc : ContinuousOn (fun p : ℝ × ℝ => S p.1) ((Set.Icc a (a+1)) ×ˢ Set.univ) :=
    hS.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hS₁c : ContinuousOn (fun p : ℝ × ℝ => S₁ p.1) ((Set.Icc a (a+1)) ×ˢ Set.univ) :=
    hS₁.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hS₂c : ContinuousOn (fun p : ℝ × ℝ => S₂ p.1) ((Set.Icc a (a+1)) ×ˢ Set.univ) :=
    hS₂.comp continuous_fst.continuousOn (fun p hp => hp.1)
  intro p hp
  have hScp := hSc p hp
  have hS₁cp := hS₁c p hp
  have hS₂cp := hS₂c p hp
  have hsp := hpos p.1 hp.1
  have hz : ContinuousWithinAt (fun p : ℝ × ℝ => p.2-p.1)
      ((Set.Icc a (a+1)) ×ˢ Set.univ) p :=
    continuous_snd.continuousWithinAt.sub continuous_fst.continuousWithinAt
  have hi := hScp.inv₀ hsp.ne'
  have hn := (hScp.const_mul (2*Real.pi)).rpow_const
    (Or.inl (show 2*Real.pi*S p.1 ≠ 0 by positivity) :
      2*Real.pi*S p.1 ≠ 0 ∨ 0 ≤ (-1/4 : ℝ))
  have he := (((hz.pow 2).neg).div (hScp.const_mul 4)
    (show 4*S p.1 ≠ 0 by positivity)).rexp
  have ha := (hi.const_mul (-1/2 : ℝ)).add
    (((hz.pow 2).mul (hi.pow 2)).const_mul (1/4 : ℝ))
  have hb := hS₁cp.mul (((hz.mul (hi.pow 2)).const_mul (-5/4 : ℝ)).add
    (((hz.pow 3).mul (hi.pow 3)).const_mul (1/4 : ℝ)))
  have hc := hS₂cp.mul ((hi.const_mul (-1/4 : ℝ)).add
    (((hz.pow 2).mul (hi.pow 2)).const_mul (1/4 : ℝ)))
  have hd := (hS₁cp.pow 2).mul ((((hi.pow 2).const_mul (5/16 : ℝ)).sub
    (((hz.pow 2).mul (hi.pow 3)).const_mul (5/8 : ℝ))).add
    (((hz.pow 4).mul (hi.pow 4)).const_mul (1/16 : ℝ)))
  convert (hn.mul he).mul (((ha.add hb).add hc).add hd) using 1
  funext y
  rw [second_eq_parts]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply,
    Pi.inv_apply, Pi.div_apply, Pi.neg_apply]
  unfold column partA partB partC partD
  ring


end CopyQuantumMetrology.SecondDerivative

