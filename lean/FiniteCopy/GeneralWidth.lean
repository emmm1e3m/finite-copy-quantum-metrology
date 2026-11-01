import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

open Set Filter
open scoped Topology
noncomputable section
namespace CopyQuantumMetrology.GeneralWidth

def K : Set ℝ := Icc (-1) 1
def b₁ (b : ℝ → ℝ) : ℝ → ℝ := derivWithin b K
def b₂ (b : ℝ → ℝ) : ℝ → ℝ := derivWithin (b₁ b) K
def profile (b : ℝ → ℝ) (x : ℝ) : ℝ := (1-x^2)*b x
def profile₁ (b : ℝ → ℝ) (x : ℝ) : ℝ := -2*x*b x+(1-x^2)*b₁ b x
def profile₂ (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2*b x-4*x*b₁ b x+(1-x^2)*b₂ b x
def width (J : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ := J*(1-(s/J)^2)*b (s/J)
def width₁ (J : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ := profile₁ b (s/J)
def width₂ (J : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ := profile₂ b (s/J)/J

lemma uniqueDiff_K : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (by norm_num)

lemma contDiffOn_b₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContDiffOn ℝ 1 (b₁ b) K := hb.derivWithin uniqueDiff_K (by norm_num)

lemma continuousOn_b₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContinuousOn (b₁ b) K := (contDiffOn_b₁ hb).continuousOn

lemma continuousOn_b₂ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContinuousOn (b₂ b) K :=
  (contDiffOn_b₁ hb).continuousOn_derivWithin uniqueDiff_K (by norm_num)

lemma hasDerivAt_b {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt b (b₁ b x) x := by
  have hxc : x ∈ K := ⟨hx.1.le,hx.2.le⟩
  exact ((hb.differentiableOn (by norm_num)) x hxc).hasDerivWithinAt.hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

lemma hasDerivAt_b₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt (b₁ b) (b₂ b x) x := by
  have hxc : x ∈ K := ⟨hx.1.le,hx.2.le⟩
  exact (((contDiffOn_b₁ hb).differentiableOn (by norm_num)) x hxc).hasDerivWithinAt.hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

-- 正的区间C²假设直接产生统一常数，不要求端点外延。
theorem exists_uniform_bounds {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    (hpos : ∀ x ∈ K, 0 < b x) :
    ∃ L M : ℝ, 0 < L ∧ 1 ≤ M ∧ ∀ x ∈ K,
      L ≤ b x ∧ |b x| ≤ M ∧ |b₁ b x| ≤ M ∧ |b₂ b x| ≤ M := by
  have hK : IsCompact K := isCompact_Icc
  have hne : K.Nonempty := ⟨0,by norm_num [K]⟩
  obtain ⟨L,hL,hLb⟩ := hK.exists_forall_le' hb.continuousOn hpos
  let f := fun x => max |b x| (max |b₁ b x| |b₂ b x|)
  have hfc : ContinuousOn f K := hb.continuousOn.abs.sup
    ((continuousOn_b₁ hb).abs.sup (continuousOn_b₂ hb).abs)
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn hne hfc
  refine ⟨L,max 1 (f z),hL,le_max_left _ _,?_⟩
  intro x hx
  have hf : f x ≤ max 1 (f z) := (isMaxOn_iff.mp hmax x hx).trans (le_max_right _ _)
  exact ⟨hLb x hx, (le_max_left _ _).trans hf,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hf,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hf⟩

lemma continuousOn_profile {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContinuousOn (profile b) K := by
  unfold profile
  exact (continuousOn_const.sub (continuousOn_id.pow 2)).mul hb.continuousOn

lemma continuousOn_profile₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContinuousOn (profile₁ b) K := by
  have h0 := hb.continuousOn
  have h1 := continuousOn_b₁ hb
  unfold profile₁
  fun_prop

lemma continuousOn_profile₂ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) :
    ContinuousOn (profile₂ b) K := by
  have h0 := hb.continuousOn
  have h1 := continuousOn_b₁ hb
  have h2 := continuousOn_b₂ hb
  unfold profile₂
  fun_prop

lemma hasDerivAt_profile {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt (profile b) (profile₁ b x) x := by
  convert (((hasDerivAt_id x).pow 2).const_sub 1).mul (hasDerivAt_b hb hx) using 1
  · rfl
  · simp only [profile₁, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,pow_one]
    ring

lemma hasDerivAt_profile₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt (profile₁ b) (profile₂ b x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -2*y) (-2) x := by
    simpa using (hasDerivAt_id x).const_mul (-2)
  convert (hlin.mul (hasDerivAt_b hb hx)).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).mul (hasDerivAt_b₁ hb hx)) using 1
  · rfl
  · simp only [profile₂, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,pow_one]
    ring

lemma scaled_mem {J s : ℝ} (hJ : 0 < J) (hs : s ∈ Icc (-J) J) : s/J ∈ K := by
  have hsa : |s| ≤ J := abs_le.mpr hs
  have hx : |s/J| ≤ 1 := by rw [abs_div,abs_of_pos hJ]; exact (div_le_one hJ).2 hsa
  exact abs_le.mp hx

lemma scaled_mem_interior {J s : ℝ} (hJ : 0 < J) (hs : |s| < J) : s/J ∈ Ioo (-1) 1 := by
  have hx : |s/J| < 1 := by rw [abs_div,abs_of_pos hJ]; exact (div_lt_one hJ).2 hs
  exact abs_lt.mp hx

lemma continuousOn_width {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J : ℝ} (hJ : 0 < J) :
    ContinuousOn (width J b) (Icc (-J) J) := by
  have hcomp := (continuousOn_profile hb).comp (continuous_id.div_const J).continuousOn
    (fun s hs => scaled_mem hJ hs)
  convert hcomp.const_mul J using 1
  ext s
  simp only [width, profile, Function.comp_apply, id_eq]
  ring

lemma continuousOn_width₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J : ℝ} (hJ : 0 < J) :
    ContinuousOn (width₁ J b) (Icc (-J) J) :=
  (continuousOn_profile₁ hb).comp (continuous_id.div_const J).continuousOn
    (fun s hs => scaled_mem hJ hs)

lemma continuousOn_width₂ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J : ℝ} (hJ : 0 < J) :
    ContinuousOn (width₂ J b) (Icc (-J) J) :=
  ((continuousOn_profile₂ hb).comp (continuous_id.div_const J).continuousOn
    (fun s hs => scaled_mem hJ hs)).div_const J

lemma hasDerivAt_width {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J s : ℝ}
    (hJ : 0 < J) (hs : |s| < J) : HasDerivAt (width J b) (width₁ J b s) s := by
  have h := ((hasDerivAt_profile hb (scaled_mem_interior hJ hs)).comp s
    ((hasDerivAt_id s).div_const J)).const_mul J
  convert h using 1
  · ext t
    simp only [width, profile, Function.comp_apply, id_eq]
    ring
  · unfold width₁
    field_simp

lemma hasDerivAt_width₁ {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J s : ℝ}
    (hJ : 0 < J) (hs : |s| < J) : HasDerivAt (width₁ J b) (width₂ J b s) s := by
  convert (hasDerivAt_profile₁ hb (scaled_mem_interior hJ hs)).comp s
    ((hasDerivAt_id s).div_const J) using 1
  · rfl
  · unfold width₂
    ring

lemma hasDerivAt_deriv_width {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K) {J s : ℝ}
    (hJ : 0 < J) (hs : |s| < J) : HasDerivAt (deriv (width J b)) (width₂ J b s) s := by
  have hnear : ∀ᶠ t in 𝓝 s, |t| < J := continuous_abs.continuousAt.eventually (gt_mem_nhds hs)
  apply (hasDerivAt_width₁ hb hJ hs).congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  exact (hasDerivAt_width hb hJ ht).deriv

lemma abs_profile₁_le {b : ℝ → ℝ} {M x : ℝ} (hx : |x| ≤ 1)
    (h0 : |b x| ≤ M) (h1 : |b₁ b x| ≤ M) : |profile₁ b x| ≤ 3*M := by
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hp : 0 ≤ 1-x^2 := by linarith
  have hp1 : 1-x^2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  unfold profile₁
  calc
    _ ≤ |-2*x*b x|+|(1-x^2)*b₁ b x| := abs_add_le _ _
    _ = 2*|x| * |b x|+(1-x^2)*|b₁ b x| := by simp [abs_mul,abs_of_nonneg hp]
    _ ≤ 2*1*M+1*M := by gcongr
    _ = _ := by ring

lemma abs_profile₂_le {b : ℝ → ℝ} {M x : ℝ} (hx : |x| ≤ 1)
    (h0 : |b x| ≤ M) (h1 : |b₁ b x| ≤ M) (h2 : |b₂ b x| ≤ M) :
    |profile₂ b x| ≤ 7*M := by
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hp : 0 ≤ 1-x^2 := by linarith
  have hp1 : 1-x^2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  unfold profile₂
  calc
    _ ≤ |-2*b x-4*x*b₁ b x|+|(1-x^2)*b₂ b x| := abs_add_le _ _
    _ ≤ |-2*b x|+|4*x*b₁ b x|+|(1-x^2)*b₂ b x| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = 2*|b x|+4*|x| * |b₁ b x|+(1-x^2)*|b₂ b x| := by
      simp [abs_mul,abs_of_nonneg hp]
    _ ≤ 2*M+4*1*M+1*M := by gcongr
    _ = _ := by ring

lemma width_eq_radial {J : ℝ} (hJ : J ≠ 0) (b : ℝ → ℝ) (s : ℝ) :
    width J b s = (J^2-s^2)*b (s/J)/J := by
  unfold width
  field_simp

lemma radial_bounds {J s : ℝ} (hs : |s| ≤ J) :
    J*(J-|s|) ≤ J^2-s^2 ∧ J^2-s^2 ≤ 2*J*(J-|s|) := by
  have hp := mul_nonneg (abs_nonneg s) (sub_nonneg.mpr hs)
  have hq := sq_nonneg (J-|s|)
  constructor <;> nlinarith [sq_abs s]

lemma width_lower {b : ℝ → ℝ} {J s L : ℝ} (hJ : 0 < J) (hL : 0 ≤ L)
    (hs : |s| ≤ J) (hbL : L ≤ b (s/J)) : L*(J-|s|) ≤ width J b s := by
  have hr : 0 ≤ J-|s| := sub_nonneg.mpr hs
  have hb : 0 ≤ b (s/J) := hL.trans hbL
  rw [width_eq_radial hJ.ne']
  apply (le_div_iff₀ hJ).2
  calc
    _ = (J*(J-|s|))*L := by ring
    _ ≤ (J*(J-|s|))*b (s/J) := mul_le_mul_of_nonneg_left hbL (mul_nonneg hJ.le hr)
    _ ≤ _ := mul_le_mul_of_nonneg_right (radial_bounds hs).1 hb

lemma width_upper {b : ℝ → ℝ} {J s M : ℝ} (hJ : 0 < J)
    (hs : |s| ≤ J) (hbM : |b (s/J)| ≤ M) : width J b s ≤ 2*M*(J-|s|) := by
  have hr : 0 ≤ J-|s| := sub_nonneg.mpr hs
  have hM : 0 ≤ M := (abs_nonneg _).trans hbM
  have hrad : 0 ≤ J^2-s^2 := (mul_nonneg hJ.le hr).trans (radial_bounds hs).1
  rw [width_eq_radial hJ.ne']
  apply (div_le_iff₀ hJ).2
  calc
    _ ≤ (J^2-s^2)*M := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbM) hrad
    _ ≤ (2*J*(J-|s|))*M := mul_le_mul_of_nonneg_right (radial_bounds hs).2 hM
    _ = _ := by ring

lemma width₁_bound {b : ℝ → ℝ} {J s M : ℝ} (hJ : 0 < J) (hs : |s| ≤ J)
    (h0 : |b (s/J)| ≤ M) (h1 : |b₁ b (s/J)| ≤ M) : |width₁ J b s| ≤ 3*M := by
  exact abs_profile₁_le (abs_le.mpr (scaled_mem hJ (abs_le.mp hs))) h0 h1

lemma width₂_bound {b : ℝ → ℝ} {J s M : ℝ} (hJ : 0 < J) (hs : |s| ≤ J)
    (h0 : |b (s/J)| ≤ M) (h1 : |b₁ b (s/J)| ≤ M) (h2 : |b₂ b (s/J)| ≤ M) :
    |width₂ J b s| ≤ 7*M/J := by
  unfold width₂
  rw [abs_div,abs_of_pos hJ]
  exact div_le_div_of_nonneg_right
    (abs_profile₂_le (abs_le.mpr (scaled_mem hJ (abs_le.mp hs))) h0 h1 h2) hJ.le

lemma width_pos {b : ℝ → ℝ} {J s : ℝ} (hJ : 0 < J) (hs : |s| < J)
    (hpos : ∀ x ∈ K, 0 < b x) : 0 < width J b s := by
  have hx := scaled_mem_interior hJ hs
  have hsq : (s/J)^2 < 1 := by nlinarith [sq_nonneg (s/J), hx.1, hx.2]
  unfold width
  exact mul_pos (mul_pos hJ (by linarith)) (hpos _ ⟨hx.1.le,hx.2.le⟩)

lemma bulk_width_lower {b : ℝ → ℝ} {J s L delta : ℝ} (hJ : 0 < J) (hL : 0 ≤ L)
    (hd : 0 ≤ delta) (hs : |s/J| ≤ 1-delta) (hbL : L ≤ b (s/J)) :
    L*J*delta ≤ width J b s := by
  have hs' : |s| ≤ (1-delta)*J := by
    rw [abs_div,abs_of_pos hJ] at hs
    exact (div_le_iff₀ hJ).1 hs
  have hsJ : |s| ≤ J := by nlinarith
  have h := mul_le_mul_of_nonneg_left (by nlinarith : J*delta ≤ J-|s|) hL
  calc
    _ = L*(J*delta) := by ring
    _ ≤ L*(J-|s|) := h
    _ ≤ _ := width_lower hJ hL hsJ hbL

-- 所有宽度预算的常数最终只来自给定正C²函数。
theorem exists_width_constants {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b K)
    (hpos : ∀ x ∈ K, 0 < b x) :
    ∃ L M : ℝ, 0 < L ∧ 1 ≤ M ∧
      (∀ x ∈ K, L ≤ b x ∧ |b x| ≤ M ∧ |b₁ b x| ≤ M ∧ |b₂ b x| ≤ M) ∧
      ∀ J s : ℝ, 0 < J → |s| ≤ J →
        L*(J-|s|) ≤ width J b s ∧ width J b s ≤ 2*M*(J-|s|) ∧
        |width₁ J b s| ≤ 3*M ∧ |width₂ J b s| ≤ 7*M/J := by
  obtain ⟨L,M,hL,hM,hbounds⟩ := exists_uniform_bounds hb hpos
  refine ⟨L,M,hL,hM,hbounds,?_⟩
  intro J s hJ hs
  obtain ⟨h0,h1,h2,h3⟩ := hbounds (s/J) (scaled_mem hJ (abs_le.mp hs))
  exact ⟨width_lower hJ hL.le hs h0,width_upper hJ hs h1,
    width₁_bound hJ hs h1 h2,width₂_bound hJ hs h1 h2 h3⟩

end CopyQuantumMetrology.GeneralWidth
