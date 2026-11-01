import FiniteCopy.GeneralGradientBulk
import FiniteCopy.GeneralWidth
import FiniteCopy.FixedDefinitions
open MeasureTheory Set
noncomputable section
namespace CopyQuantumMetrology.FixedWidth
open GeneralGradient

set_option maxHeartbeats 700000

def gradientScale (M : ℝ) : ℝ := 1/(1+7*M)
def gradientCutoff (L delta : ℝ) : ℝ := min 1 L*delta

lemma gradientScale_pos {M : ℝ} (hM : 1 ≤ M) : 0 < gradientScale M := by
  unfold gradientScale
  positivity

lemma gradientScale_le_one {M : ℝ} (hM : 1 ≤ M) : gradientScale M ≤ 1 := by
  unfold gradientScale
  exact (div_le_one (by positivity : 0 < 1+7*M)).2 (by linarith)

lemma gradientScale_bounds {M : ℝ} (hM : 1 ≤ M) :
    3*M ≤ 2/(gradientScale M)^3 ∧ 7*M ≤ 3/(gradientScale M)^5 := by
  have hE : 1 ≤ 1+7*M := by linarith
  have h3 : 1+7*M ≤ (1+7*M)^3 := by
    simpa using pow_le_pow_right₀ hE (by norm_num : (1:ℕ) ≤ 3)
  have h5 : 1+7*M ≤ (1+7*M)^5 := by
    simpa using pow_le_pow_right₀ hE (by norm_num : (1:ℕ) ≤ 5)
  simp only [gradientScale,div_eq_mul_inv,one_mul,inv_pow,inv_inv]
  constructor <;> nlinarith

lemma gradientCutoff_bounds {L delta : ℝ} (hL : 0 < L) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    0 < gradientCutoff L delta ∧ gradientCutoff L delta ≤ 1 ∧
      gradientCutoff L delta ≤ delta ∧ gradientCutoff L delta ≤ L*delta := by
  have hmin : 0 < min 1 L := lt_min (by norm_num) hL
  have hdd : min 1 L*delta ≤ delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) L) hd.le
  exact ⟨mul_pos hmin hd,hdd.trans hd1,hdd,mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le⟩

lemma gradient_interval_subset {J m : ℝ} (hm : |m| ≤ J-1/2) (hm₁ : |m+1| ≤ J-1/2) :
    Icc m (m+1) ⊆ Icc (-J) J := by
  intro s hs
  exact abs_le.mp ((GradientBounds.edge_interval_bound hm hm₁ hs).trans (by linarith))

lemma gradient_bulk_interval {J m delta s : ℝ} (hJ : 0 < J)
    (hm : |m/J| ≤ 1-delta) (hm₁ : |(m+1)/J| ≤ 1-delta) (hs : s ∈ Icc m (m+1)) :
    |s/J| ≤ 1-delta := by
  rw [abs_div,abs_of_pos hJ] at hm hm₁ ⊢
  apply (div_le_iff₀ hJ).2
  have hl := abs_le.1 ((div_le_iff₀ hJ).1 hm)
  have hr := abs_le.1 ((div_le_iff₀ hJ).1 hm₁)
  exact abs_le.2 ⟨by linarith [hs.1],by linarith [hs.2]⟩

-- 由一般正C²轮廓的标量界闭合真实G全局界。
theorem G_global_of_bounds {b : ℝ → ℝ} {L M J m : ℝ}
    (hb : ContDiffOn ℝ 2 b GeneralWidth.K) (hL : 0 < L) (hM : 1 ≤ M)
    (hbound : ∀ x ∈ GeneralWidth.K,
      L ≤ b x ∧ |b x| ≤ M ∧ |GeneralWidth.b₁ b x| ≤ M ∧ |GeneralWidth.b₂ b x| ≤ M)
    (hJ : 1 ≤ J) (hm : |m| ≤ J-1/2) (hm₁ : |m+1| ≤ J-1/2) :
    G b J m ≤ globalConstant L M*J := by
  have hJp : 0 < J := by linarith
  have hsub := gradient_interval_subset hm hm₁
  have hsi (s : ℝ) (hs : s ∈ Icc m (m+1)) : |s| < J := by
    linarith [GradientBounds.edge_interval_bound hm hm₁ hs]
  have hx (s : ℝ) (hs : s ∈ Icc m (m+1)) := GeneralWidth.scaled_mem hJp (hsub hs)
  exact gaussian_gradient_global (S := GeneralWidth.width J b) (T := GeneralWidth.width₁ J b)
    hJp hL (by linarith) hm hm₁
    ((GeneralWidth.continuousOn_width hb hJp).mono hsub)
    ((GeneralWidth.continuousOn_width₁ hb hJp).mono hsub)
    (fun s hs => GeneralWidth.hasDerivAt_width hb hJp (hsi s hs))
    (fun s hs => GeneralWidth.width_lower hJp hL.le (hsi s hs).le (hbound _ (hx s hs)).1)
    (fun s hs => GeneralWidth.width₁_bound hJp (hsi s hs).le
      (hbound _ (hx s hs)).2.1 (hbound _ (hx s hs)).2.2.1)

theorem G_bulk_of_bounds {b : ℝ → ℝ} {L M J m delta : ℝ}
    (hb : ContDiffOn ℝ 2 b GeneralWidth.K) (hL : 0 < L) (hM : 1 ≤ M)
    (hbound : ∀ x ∈ GeneralWidth.K,
      L ≤ b x ∧ |b x| ≤ M ∧ |GeneralWidth.b₁ b x| ≤ M ∧ |GeneralWidth.b₂ b x| ≤ M)
    (hJ : 1 ≤ J) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hm : |m/J| ≤ 1-delta) (hm₁ : |(m+1)/J| ≤ 1-delta) :
    |G b J m/J-1/(4*b (m/J))| ≤
      bulkConstant (gradientScale M) (gradientCutoff L delta)/Real.sqrt J := by
  have hJp : 0 < J := by linarith
  obtain ⟨hdp,hdle,hdd,hdL⟩ := gradientCutoff_bounds hL hd hd1
  obtain ⟨hscale₁,hscale₂⟩ := gradientScale_bounds hM
  have hsbulk (s : ℝ) (hs : s ∈ Icc m (m+1)) : |s/J| ≤ 1-delta :=
    gradient_bulk_interval hJp hm hm₁ hs
  have hsi (s : ℝ) (hs : s ∈ Icc m (m+1)) : |s| < J := by
    have h := hsbulk s hs
    rw [abs_div,abs_of_pos hJp] at h
    have hh := (div_le_iff₀ hJp).1 h
    nlinarith
  have hsub : Icc m (m+1) ⊆ Icc (-J) J := fun s hs => abs_le.mp (hsi s hs).le
  have hx (s : ℝ) (hs : s ∈ Icc m (m+1)) := GeneralWidth.scaled_mem hJp (hsub hs)
  have hmp : m ∈ Icc m (m+1) := ⟨le_rfl,by linarith⟩
  apply gaussian_gradient_bulk (S := GeneralWidth.width J b)
    (T := GeneralWidth.width₁ J b) (U := GeneralWidth.width₂ J b)
    hJ (gradientScale_pos hM) (gradientScale_le_one hM) hdp hdle
    (by linarith) (hL.trans_le (hbound _ (hx m hmp)).1)
    (GeneralWidth.width_eq_radial hJp.ne' b m)
    ((GeneralWidth.continuousOn_width hb hJp).mono hsub)
    ((GeneralWidth.continuousOn_width₁ hb hJp).mono hsub)
    ((GeneralWidth.continuousOn_width₂ hb hJp).mono hsub)
    (fun s hs => GeneralWidth.hasDerivAt_width hb hJp (hsi s hs))
    (fun s hs => GeneralWidth.hasDerivAt_width₁ hb hJp (hsi s hs))
  · intro s hs
    have hw := GeneralWidth.bulk_width_lower hJp hL.le hd.le (hsbulk s hs) (hbound _ (hx s hs)).1
    have hh := mul_le_mul_of_nonneg_left hdL hJp.le
    have h0 : 0 ≤ J*gradientCutoff L delta := by positivity
    nlinarith only [hh,hw,h0]
  · intro s hs
    exact (GeneralWidth.width₁_bound hJp (hsi s hs).le
      (hbound _ (hx s hs)).2.1 (hbound _ (hx s hs)).2.2.1).trans hscale₁
  · intro s hs
    have hu := GeneralWidth.width₂_bound hJp (hsi s hs).le
      (hbound _ (hx s hs)).2.1 (hbound _ (hx s hs)).2.2.1 (hbound _ (hx s hs)).2.2.2
    calc
      _ ≤ 7*M/J := hu
      _ ≤ (3/(gradientScale M)^5)/J := div_le_div_of_nonneg_right hscale₂ hJp.le
      _ = _ := by ring

-- 面向总装的接口只保留论文中原始的正C²假设。
theorem G_global_exists {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b GeneralWidth.K)
    (hpos : ∀ x ∈ GeneralWidth.K, 0 < b x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℝ, 1 ≤ J → ∀ m : ℝ,
      |m| ≤ J-1/2 → |m+1| ≤ J-1/2 → G b J m ≤ C*J := by
  obtain ⟨L,M,hL,hM,hbounds⟩ := GeneralWidth.exists_uniform_bounds hb hpos
  exact ⟨globalConstant L M,globalConstant_nonneg hL M,
    fun J hJ m hm hm₁ => G_global_of_bounds hb hL hM hbounds hJ hm hm₁⟩

theorem G_bulk_exists {b : ℝ → ℝ} (hb : ContDiffOn ℝ 2 b GeneralWidth.K)
    (hpos : ∀ x ∈ GeneralWidth.K, 0 < b x) {delta : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ J : ℝ, 1 ≤ J → ∀ m : ℝ,
      |m/J| ≤ 1-delta → |(m+1)/J| ≤ 1-delta →
      |G b J m/J-1/(4*b (m/J))| ≤ K/Real.sqrt J := by
  obtain ⟨L,M,hL,hM,hbounds⟩ := GeneralWidth.exists_uniform_bounds hb hpos
  exact ⟨bulkConstant (gradientScale M) (gradientCutoff L delta),
    bulkConstant_nonneg (gradientScale_pos hM) (gradientCutoff_bounds hL hd hd1).1,
    fun J hJ m hm hm₁ => G_bulk_of_bounds hb hL hM hbounds hJ hd hd1 hm hm₁⟩

end CopyQuantumMetrology.FixedWidth
