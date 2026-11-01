import FiniteCopy.GradientBounds
import FiniteCopy.RegularizedGradient
import FiniteCopy.FiniteDifferenceEnergy
import FiniteCopy.SecondDerivative
import FiniteCopy.BulkParameters

open MeasureTheory Set
noncomputable section
namespace CopyQuantumMetrology.GeneralGradient
open GlobalBounds GradientBounds

set_option maxHeartbeats 700000

def globalConstant (L M : ℝ) : ℝ := 24+4/L+144*M^2/L^2+1152*M^2/L

lemma globalConstant_nonneg {L : ℝ} (hL : 0 < L) (M : ℝ) : 0 ≤ globalConstant L M := by
  unfold globalConstant
  positivity

lemma gaussian_edge_derivative_lower {J s r S T c L M : ℝ} (hJ : 0 < J)
    (hr : 1/2 ≤ r) (hs : |s| ≤ J) (hrJ : r ≤ J)
    (hB : J*r ≤ J^2-s^2) (hL : 0 < L) (hS : L*r ≤ S) (hc : 0 ≤ c)
    (hcB : c*Real.sqrt (J^2-s^2) ≤ 4*J*r) (hM : 0 ≤ M) (hT : |T| ≤ 3*M) :
    c*(∫ t, q J t*movingDeriv s S T t^2) ≤ globalConstant L M*J := by
  have hrp : 0 < r := by linarith
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  let B := Real.sqrt (J^2-s^2)
  have he := gaussian_derivative_energy_le (s := s) (S₁ := T) hSp
    (show 0 ≤ 2*B by positivity) (show 0 ≤ 2*B/r^2 by positivity)
    (continuous_q J) (q_nonneg J) (fun t => by
      have h := q_le_quadratic hJ hrp hs hrJ hB t
      convert h using 1 <;> dsimp [B] <;> ring)
  have hrS : r/S ≤ 1/L := (div_le_div_iff₀ hSp hL).2 (by nlinarith)
  have hinvS : 1/S ≤ 2/L := (div_le_div_iff₀ hSp hL).2 (by nlinarith)
  have hinvr : 1/r ≤ 2 := (div_le_iff₀ hrp).2 (by linarith)
  have hrS2 : r/S^2 ≤ 2/L^2 := by
    calc
      _ = (r/S)*(1/S) := by ring
      _ ≤ (1/L)*(2/L) := mul_le_mul hrS hinvS (by positivity) (by positivity)
      _ = _ := by ring
  have hrSinv : 1/(r*S) ≤ 4/L := by
    calc
      _ = (1/r)*(1/S) := by ring
      _ ≤ 2*(2/L) := mul_le_mul hinvr hinvS (by positivity) (by norm_num)
      _ = _ := by ring
  have hT2 : T^2 ≤ 9*M^2 := by
    have h := (sq_le_sq₀ (abs_nonneg T) (by positivity : 0 ≤ 3*M)).2 hT
    norm_num [sq_abs, mul_pow] at h
    exact h
  calc
    _ ≤ c*(2*B/(2*S)+(2*B)*T^2/S^2+3*(2*B/r^2)/2+4*(2*B/r^2)*T^2/S) :=
      mul_le_mul_of_nonneg_left he hc
    _ = (c*B)*(1/S+2*T^2/S^2+3/r^2+8*T^2/(r^2*S)) := by ring
    _ ≤ (4*J*r)*(1/S+2*T^2/S^2+3/r^2+8*T^2/(r^2*S)) :=
      mul_le_mul_of_nonneg_right hcB (by positivity)
    _ = J*(4*(r/S)+8*T^2*(r/S^2)+12*(1/r)+32*T^2*(1/(r*S))) := by
      field_simp
      <;> ring
    _ ≤ J*(4*(1/L)+8*(9*M^2)*(2/L^2)+12*2+32*(9*M^2)*(4/L)) := by gcongr
    _ = _ := by unfold globalConstant; ring

lemma continuous_movingDeriv (s S T : ℝ) : Continuous (movingDeriv s S T) := by
  unfold movingDeriv column
  fun_prop

lemma hasDerivAt_movingDeriv {S T : ℝ → ℝ} {s U : ℝ} (t : ℝ)
    (hS : HasDerivAt S (T s) s) (hT : HasDerivAt T U s) (hpos : 0 < S s) :
    HasDerivAt (fun x => movingDeriv x (S x) (T x) t)
      (SecondDerivative.second s (S s) (T s) U t) s := by
  have h := hasDerivAt_column_first (m := fun x : ℝ => x) (m₁ := fun _ => (1:ℝ))
    t (hasDerivAt_id s) hS (hasDerivAt_const s 1) hT hpos
  convert h using 1
  · funext x
    unfold movingDeriv columnScore
    ring
  · rfl

-- 全局定理仅要求真实微分关系和标量宽度界。
theorem gaussian_gradient_global {S T : ℝ → ℝ} {J m L M : ℝ}
    (hJ : 0 < J) (hL : 0 < L) (hM : 0 ≤ M)
    (hm : |m| ≤ J-1/2) (hm₁ : |m+1| ≤ J-1/2)
    (hSc : ContinuousOn S (Icc m (m+1))) (hTc : ContinuousOn T (Icc m (m+1)))
    (hderiv : ∀ s ∈ Icc m (m+1), HasDerivAt S (T s) s)
    (hSl : ∀ s ∈ Icc m (m+1), L*(J-|s|) ≤ S s)
    (hTb : ∀ s ∈ Icc m (m+1), |T s| ≤ 3*M) :
    q J (m+1/2)*(∫ t, q J t*(column (m+1) (S (m+1)) t-column m (S m) t)^2) ≤
      globalConstant L M*J := by
  let v := fun s t => column s (S s) t
  let D := fun s t => movingDeriv s (S s) (T s) t
  have hpos : ∀ s ∈ Icc m (m+1), 0 < S s := by
    intro s hs
    have hr : 0 < J-|s| := by linarith [edge_interval_bound hm hm₁ hs]
    exact lt_of_lt_of_le (mul_pos hL hr) (hSl s hs)
  have hDc : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc m (m+1) ×ˢ univ) :=
    continuousOn_movingDeriv hSc hTc hpos
  have hprod : Integrable (fun p : ℝ × ℝ => q J p.2*D p.1 p.2^2)
      ((volume.restrict (Ioc m (m+1))).prod volume) :=
    integrable_q_mul_strip hJ.le ((hDc.pow 2).mono (Set.prod_mono Subset.rfl (subset_univ _)))
  have hv : ∀ t s, s ∈ Icc m (m+1) → HasDerivAt (fun s => v s t) (D s t) s := by
    intro t s hs
    exact hasDerivAt_column_moving t (hderiv s hs) (hpos s hs)
  have hD : ∀ t, ContinuousOn (fun s => D s t) (Icc m (m+1)) := by
    intro t
    have hp : Continuous (fun s : ℝ => (s,t)) := continuous_id.prodMk continuous_const
    exact hDc.comp (f := fun s : ℝ => (s,t)) hp.continuousOn (fun s hs => ⟨hs, mem_univ _⟩)
  have hf : Integrable (fun t => q J t*(v (m+1) t-v m t)^2) :=
    integrable_q_mul hJ.le (((continuous_column_sample _ _).sub (continuous_column_sample _ _)).pow 2)
  have he := weighted_finite_difference_le m (q_nonneg J) hv hD hf hprod
  calc
    _ ≤ q J (m+1/2)*(∫ s in Ioc m (m+1), ∫ t, q J t*D s t^2) :=
      mul_le_mul_of_nonneg_left he (q_nonneg J (m+1/2))
    _ = ∫ s in Ioc m (m+1), q J (m+1/2)*(∫ t, q J t*D s t^2) := by rw [integral_const_mul]
    _ ≤ ∫ _s in Ioc m (m+1), globalConstant L M*J := by
      apply setIntegral_mono_on (hprod.integral_prod_left.const_mul _)
        (integrableOn_const (hs := by simp)) measurableSet_Ioc
      intro s hs
      have hss : s ∈ Icc m (m+1) := ⟨hs.1.le, hs.2⟩
      have hsJ := edge_interval_bound hm hm₁ hss
      have hsJ' : |s| ≤ J := by linarith
      exact gaussian_edge_derivative_lower (s := s) (r := J-|s|) (S := S s) (T := T s)
        (c := q J (m+1/2)) (L := L) (M := M) hJ (by linarith) hsJ'
        (by linarith [abs_nonneg s]) (Width.radial_bounds hJ hsJ').1 hL (hSl s hss)
        (q_nonneg J _) (edge_coefficient_product_le hJ hm hm₁ hss) hM (hTb s hss)
    _ = _ := by
      simp only [setIntegral_const, Real.volume_real_Ioc_of_le (show m ≤ m+1 by linarith)]
      ring

-- 复用032的一般高斯二阶矩预算，保留真实S/T/U而不假设能量界。
lemma scalar_second_bulk {J S T U e d : ℝ} (s : ℝ) (hJ : 1 ≤ J)
    (he : 0 < e) (he1 : e ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hSl : J*d/4 ≤ S) (hT : |T| ≤ 2/e^3) (hU : |U| ≤ 3/(J*e^5)) :
    (∫ t, q J t*SecondDerivative.second s S T U t^2) ≤ 16384/(J*e^12*d^4) := by
  have hJp : 0 < J := by linarith
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hSi : S⁻¹ ≤ 4*J⁻¹*d⁻¹ := by
    calc
      _ ≤ (J*d/4)⁻¹ := inv_anti₀ (by positivity) hSl
      _ = _ := by ring
  have hT' : |T| ≤ 2*(e⁻¹)^3 := by convert hT using 1 <;> ring
  have hU' : |U| ≤ 3*J⁻¹*(e⁻¹)^5 := by convert hU using 1 <;> ring
  have hb := SecondDerivative.budget_le_scaled hSp (by positivity : 0 ≤ J⁻¹)
    ((inv_le_one₀ hJp).2 hJ) ((one_le_inv₀ he).2 he1) ((one_le_inv₀ hd).2 hd1) hSi hT' hU'
  calc
    _ ≤ J*SecondDerivative.budget S T U := SecondDerivative.integral_weighted_second_sq_le s T U hJp.le hSp
    _ ≤ J*(13536*(J⁻¹)^2*(e⁻¹)^12*(d⁻¹)^4) := mul_le_mul_of_nonneg_left hb hJp.le
    _ = 13536/(J*e^12*d^4) := by field_simp
    _ ≤ _ := by gcongr <;> norm_num

lemma scalar_first_bulk {J s S T e d : ℝ} (hJ : 1 ≤ J)
    (he : 0 < e) (he1 : e ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hSl : J*d/4 ≤ S) (hT : |T| ≤ 2/e^3) :
    (∫ t, q J t*movingDeriv s S T t^2) ≤ 66/(e^6*d^2) := by
  have hJp : 0 < J := by linarith
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have he6 : e^6 ≤ 1 := pow_le_one₀ he.le he1
  have hd2 : d^2 ≤ d := by nlinarith
  have hT2 : T^2 ≤ 4/e^6 := by
    have hh := (sq_le_sq₀ (abs_nonneg T) (by positivity : 0 ≤ 2/e^3)).2 hT
    norm_num [div_pow, ← pow_mul] at hh
    exact hh
  have hi := gaussian_derivative_energy_le (s := s) (S₁ := T) hSp hJp.le (show (0:ℝ) ≤ 0 by rfl)
    (continuous_q J) (q_nonneg J) (fun t => by simpa using SecondDerivative.q_le_J hJp.le t)
  have h1 : J/(2*S) ≤ 2/(e^6*d^2) := by
    calc
      _ ≤ J/(2*(J*d/4)) := by gcongr
      _ = 2/d := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact (mul_le_of_le_one_left (sq_nonneg d) he6).trans hd2
  have h2 : J*T^2/S^2 ≤ 64/(e^6*d^2) := by
    calc
      _ ≤ J*(4/e^6)/(J*d/4)^2 := by gcongr
      _ = 64/(J*e^6*d^2) := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr hJ) (show 0 ≤ e^6*d^2 by positivity)]
  calc
    _ ≤ J/(2*S)+J*T^2/S^2 := by simpa using hi
    _ ≤ 2/(e^6*d^2)+64/(e^6*d^2) := add_le_add h1 h2
    _ = _ := by ring

end CopyQuantumMetrology.GeneralGradient
