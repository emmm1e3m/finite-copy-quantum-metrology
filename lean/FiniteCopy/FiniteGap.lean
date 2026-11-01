import FiniteCopy.Algebra

open scoped BigOperators
open Finset
open FiniteCopy.Algebra (capA capR capR_bounds capR_succ)

noncomputable section

namespace FiniteCopy.Gap

/-- n=2j 是边数，节点编号为 0,...,n。 -/
def coeff (n i : ℕ) : ℝ := Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) - i))

def cap (x τ : ℝ) : ℝ := max (x - τ) 0

theorem coeff_nonneg (n i : ℕ) : 0 ≤ coeff n i := Real.sqrt_nonneg _

theorem coeff_sq (n i : ℕ) (hi : i ≤ n) :
    coeff n i ^ 2 = ((i : ℝ) + 1) * ((n : ℝ) - i) := by
  unfold coeff
  apply Real.sq_sqrt
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
  positivity

theorem coeff_one_pos (n : ℕ) (hn : 10 ≤ n) : 0 < coeff n 1 := by
  unfold coeff
  apply Real.sqrt_pos.2
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num
  linarith

theorem coeff_reflect (n i : ℕ) (hi : i < n) :
    coeff n (n - 1 - i) = coeff n i := by
  have hs : (n - 1 - i : ℕ) + i + 1 = n := by omega
  have hsR : (n - 1 - i : ℕ) + (i : ℝ) + 1 = n := by exact_mod_cast hs
  unfold coeff
  congr 1
  nlinarith

/-- 附录中的三个有理比值界，直接覆盖所有 n≥10。 -/
theorem central_ratio_bounds (n : ℕ) (hn : 10 ≤ n) :
    (23 / 20 : ℝ) * coeff n 1 < coeff n 2 ∧
    (6 / 5 : ℝ) * coeff n 1 < coeff n 3 ∧
    (5 / 4 : ℝ) * coeff n 1 < coeff n 4 := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := coeff_sq n 1 (by omega)
  have h2 := coeff_sq n 2 (by omega)
  have h3 := coeff_sq n 3 (by omega)
  have h4 := coeff_sq n 4 (by omega)
  have p1 := coeff_nonneg n 1
  have p2 := coeff_nonneg n 2
  have p3 := coeff_nonneg n 3
  have p4 := coeff_nonneg n 4
  norm_num at h1 h2 h3 h4
  constructor
  · nlinarith
  constructor <;> nlinarith

def sixEdges (n : ℕ) : Finset ℕ := {2, 3, 4, n - 3, n - 4, n - 5}

theorem sixEdges_subset (n : ℕ) (hn : 10 ≤ n) : sixEdges n ⊆ range n := by
  intro i hi
  simp only [sixEdges, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [mem_range] <;> omega

theorem sum_sixEdges (n : ℕ) (hn : 10 ≤ n) (f : ℕ → ℝ) :
    (∑ i ∈ sixEdges n, f i) =
      f 2 + f 3 + f 4 + f (n - 3) + f (n - 4) + f (n - 5) := by
  have h23 : (2 : ℕ) ≠ 3 := by omega
  have h24 : (2 : ℕ) ≠ 4 := by omega
  have h34 : (3 : ℕ) ≠ 4 := by omega
  have h2a : 2 ≠ n - 3 := by omega
  have h2b : 2 ≠ n - 4 := by omega
  have h2c : 2 ≠ n - 5 := by omega
  have h3a : 3 ≠ n - 3 := by omega
  have h3b : 3 ≠ n - 4 := by omega
  have h3c : 3 ≠ n - 5 := by omega
  have h4a : 4 ≠ n - 3 := by omega
  have h4b : 4 ≠ n - 4 := by omega
  have h4c : 4 ≠ n - 5 := by omega
  have hab : n - 3 ≠ n - 4 := by omega
  have hac : n - 3 ≠ n - 5 := by omega
  have hbc : n - 4 ≠ n - 5 := by omega
  simp [sixEdges, h23, h24, h34, h2a, h2b, h2c, h3a, h3b, h3c,
    h4a, h4b, h4c, hab, hac, hbc]
  ring

theorem six_coeff_sum (n : ℕ) (hn : 10 ≤ n) :
    (∑ i ∈ sixEdges n, (coeff n i - coeff n 1)) =
      2 * (coeff n 2 + coeff n 3 + coeff n 4) - 6 * coeff n 1 := by
  rw [sum_sixEdges n hn]
  have h2 := coeff_reflect n 2 (by omega)
  have h3 := coeff_reflect n 3 (by omega)
  have h4 := coeff_reflect n 4 (by omega)
  have e2 : n - 1 - 2 = n - 3 := by omega
  have e3 : n - 1 - 3 = n - 4 := by omega
  have e4 : n - 1 - 4 = n - 5 := by omega
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [h2, h3, h4]
  ring

theorem cap_sum_at_first_inner_edge (n : ℕ) (hn : 10 ≤ n) :
    coeff n 1 < ∑ i ∈ range n, cap (coeff n i) (coeff n 1) := by
  have hbounds := central_ratio_bounds n hn
  have hp := coeff_one_pos n hn
  have hstrict : coeff n 1 < ∑ i ∈ sixEdges n, (coeff n i - coeff n 1) := by
    rw [six_coeff_sum n hn]
    linarith [hbounds.1, hbounds.2.1, hbounds.2.2]
  apply hstrict.trans_le
  calc
    (∑ i ∈ sixEdges n, (coeff n i - coeff n 1)) ≤
        ∑ i ∈ sixEdges n, cap (coeff n i) (coeff n 1) := by
      apply sum_le_sum
      intro i hi
      exact le_max_left _ _
    _ ≤ ∑ i ∈ range n, cap (coeff n i) (coeff n 1) :=
      sum_le_sum_of_subset_of_nonneg (sixEdges_subset n hn) (fun _ _ _ => le_max_right _ _)

/-- 任意满足真实截顶方程的 τ 均严格超过第二条边。 -/
theorem cap_root_gt_first_inner_edge (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) : coeff n 1 < τ := by
  by_contra h
  have ht : τ ≤ coeff n 1 := le_of_not_gt h
  have hsum : (∑ i ∈ range n, cap (coeff n i) (coeff n 1)) ≤ τ := by
    rw [← hroot]
    apply sum_le_sum
    intro i hi
    exact max_le_max (by linarith) le_rfl
  exact (not_lt_of_ge (hsum.trans ht)) (cap_sum_at_first_inner_edge n hn)

/-- 每条边上的两个平方项；端点项在 r₀=0,rₙ=1 时消失。 -/
def edgeSOS (a r v : ℕ → ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  (1 - r i) * (t * v i - a i * v (i + 1)) ^ 2 +
    r (i + 1) * (t * v (i + 1) - a i * v i) ^ 2

def Saturated (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ i < n, edgeSOS a r v t i = 0

theorem edgeSOS_nonneg (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1) (i : ℕ) (hi : i < n) :
    0 ≤ edgeSOS a r v t i := by
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hr i (by omega)).2) (sq_nonneg _))
    (mul_nonneg (hr (i + 1) (by omega)).1 (sq_nonneg _))

theorem saturated_of_sum_zero (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hzero : (∑ i ∈ range n, edgeSOS a r v t i) = 0) : Saturated n a r v t := by
  intro i hi
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun k hk => edgeSOS_nonneg n a r v t hr k (mem_range.mp hk))).mp hzero i (mem_range.mpr hi)

theorem saturated_forward (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hs : Saturated n a r v t) (i : ℕ) (hi : i < n) (hri : r i < 1) :
    t * v i = a i * v (i + 1) := by
  have he := hs i hi
  unfold edgeSOS at he
  have hother : 0 ≤ r (i + 1) * (t * v (i + 1) - a i * v i) ^ 2 :=
    mul_nonneg (hr (i + 1) (by omega)).1 (sq_nonneg _)
  have hz : (t * v i - a i * v (i + 1)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (t * v i - a i * v (i + 1))]
  nlinarith [sq_nonneg (t * v i - a i * v (i + 1))]

theorem saturated_backward (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hs : Saturated n a r v t) (i : ℕ) (hi : i < n) (hri : 0 < r (i + 1)) :
    t * v (i + 1) = a i * v i := by
  have he := hs i hi
  unfold edgeSOS at he
  have hother : 0 ≤ (1 - r i) * (t * v i - a i * v (i + 1)) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (hr i (by omega)).2) (sq_nonneg _)
  have hz : (t * v (i + 1) - a i * v i) ^ 2 = 0 := by
    nlinarith [sq_nonneg (t * v (i + 1) - a i * v i)]
  nlinarith [sq_nonneg (t * v (i + 1) - a i * v i)]

theorem saturated_zero_iff_next (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (ht : 0 < t) (ha : ∀ i < n, 0 < a i)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hm : ∀ i < n, r i ≤ r (i + 1))
    (hs : Saturated n a r v t) (i : ℕ) (hi : i < n) :
    v i = 0 ↔ v (i + 1) = 0 := by
  by_cases hri : r i < 1
  · have he := saturated_forward n a r v t hr hs i hi hri
    constructor <;> intro hz <;> rw [hz] at he <;> nlinarith [ha i hi]
  · have hri' : 0 < r (i + 1) := by linarith [hm i hi]
    have he := saturated_backward n a r v t hr hs i hi hri'
    constructor <;> intro hz <;> rw [hz] at he <;> nlinarith [ha i hi]

/-- 正 t 的非零饱和向量，在连接链上无零坐标。 -/
theorem saturated_nowhere_zero (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (ht : 0 < t) (ha : ∀ i < n, 0 < a i)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hm : ∀ i < n, r i ≤ r (i + 1))
    (hs : Saturated n a r v t) (hv : ∃ k ≤ n, v k ≠ 0) : ∀ i ≤ n, v i ≠ 0 := by
  have hconn : ∀ i ≤ n, v i = 0 ↔ v 0 = 0 := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      exact (saturated_zero_iff_next n a r v t ht ha hr hm hs i (by omega)).symm.trans
        (ih (by omega))
  rcases hv with ⟨k, hk, hkn⟩
  intro i hi hiz
  exact hkn ((hconn k hk).mpr ((hconn i hi).mp hiz))

/-- 两个正系数的平台递推迫使谱参数等于截顶高度。 -/
theorem saturated_parameter (n : ℕ) (a r v : ℕ → ℝ) (t τ : ℝ)
    (ht : 0 < t) (hτ : 0 < τ) (ha : ∀ i < n, 0 < a i)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hm : ∀ i < n, r i ≤ r (i + 1))
    (hs : Saturated n a r v t) (hv : ∃ k ≤ n, v k ≠ 0)
    (hplateau : ∃ k < n, a k = τ ∧ r k < r (k + 1)) : t = τ := by
  rcases hplateau with ⟨k, hk, hak, hrk⟩
  have hfor := saturated_forward n a r v t hr hs k hk (by linarith [(hr (k+1) (by omega)).2])
  have hback := saturated_backward n a r v t hr hs k hk (by linarith [(hr k (by omega)).1])
  rw [hak] at hfor hback
  have hz := saturated_nowhere_zero n a r v t ht ha hr hm hs hv k (by omega)
  have he : (t ^ 2 - τ ^ 2) * v k = 0 := by
    nlinarith [congrArg (fun z : ℝ => t * z) hfor, congrArg (fun z : ℝ => τ * z) hback]
  have he' : t ^ 2 - τ ^ 2 = 0 := (mul_eq_zero.mp he).resolve_right hz
  nlinarith

/-- t=0 时内部节点必须消失。 -/
theorem saturated_zero_parameter_interior (n : ℕ) (a r v : ℕ → ℝ)
    (ha : ∀ i < n, 0 < a i)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hm : ∀ i < n, r i ≤ r (i + 1))
    (hs : Saturated n a r v 0) (i : ℕ) (hi0 : 0 < i) (hin : i < n) : v i = 0 := by
  have him : i - 1 < n := by omega
  have hie : i - 1 + 1 = i := by omega
  by_cases hri : r (i - 1) < 1
  · have he := saturated_forward n a r v 0 hr hs (i - 1) him hri
    rw [hie] at he
    nlinarith [ha (i - 1) him]
  · have hrp : 0 < r (i + 1) := by
      have h1 := hm (i - 1) him
      rw [hie] at h1
      linarith [hm i hin]
    have he := saturated_backward n a r v 0 hr hs i hin hrp
    nlinarith [ha i hin]

/-- 每个饱和种子都具有同一占据数比例，零种子也包含在内。 -/
theorem saturated_tail_relation (n : ℕ) (hn : 2 < n) (a r v : ℕ → ℝ) (t τ : ℝ)
    (ht : 0 ≤ t) (hτ : 0 < τ) (ha : ∀ i < n, 0 < a i)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hm : ∀ i < n, r i ≤ r (i + 1))
    (hs : Saturated n a r v t) (hr1 : r 1 = 0)
    (hplateau : ∃ k < n, a k = τ ∧ r k < r (k + 1)) :
    v 1 = (a 1 / τ) * v 2 := by
  by_cases hv : ∃ k ≤ n, v k ≠ 0
  · rcases eq_or_lt_of_le ht with ht0 | htp
    · have ht' : t = 0 := ht0.symm
      subst t
      have h1 := saturated_zero_parameter_interior n a r v ha hr hm hs 1 (by omega) (by omega)
      have h2 := saturated_zero_parameter_interior n a r v ha hr hm hs 2 (by omega) hn
      rw [h1, h2, mul_zero]
    · have ht' := saturated_parameter n a r v t τ htp hτ ha hr hm hs hv hplateau
      have he := saturated_forward n a r v t hr hs 1 (by omega) (by rw [hr1]; norm_num)
      rw [ht'] at he
      calc
        v 1 = (a 1 * v 2) / τ := by exact (eq_div_iff (ne_of_gt hτ)).2 (by linarith)
        _ = (a 1 / τ) * v 2 := by ring
  · push Not at hv
    rw [hv 1 (by omega), hv 2 (by omega), mul_zero]

theorem population_obstruction {α : Type*} (seeds : Finset α) (v : α → ℕ → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrel : ∀ k ∈ seeds, v k 1 = q * v k 2)
    (hcomplete1 : (∑ k ∈ seeds, v k 1 ^ 2) = 1)
    (hcomplete2 : (∑ k ∈ seeds, v k 2 ^ 2) = 1) : False := by
  have he : (∑ k ∈ seeds, v k 1 ^ 2) = q ^ 2 * (∑ k ∈ seeds, v k 2 ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hrel k hk]
    ring
  rw [hcomplete1, hcomplete2] at he
  nlinarith

theorem capR_monotone_step (c : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (i : ℕ) :
    capR c τ i ≤ capR c τ (i + 1) := by
  rw [capR_succ]
  exact le_add_of_nonneg_right (div_nonneg (le_max_right _ _) hτ.le)

/-- 正的截顶根保证至少存在一个真正被截顶的边，权重在该边严格增加。 -/
theorem cap_plateau (n : ℕ) (c : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hroot : (∑ i ∈ range n, cap (c i) τ) = τ) :
    ∃ k < n, capA c τ k = τ ∧ capR c τ k < capR c τ (k + 1) := by
  have hsum : 0 < ∑ i ∈ range n, cap (c i) τ := by rw [hroot]; exact hτ
  obtain ⟨k, hk, hkp⟩ := (sum_pos_iff_of_nonneg (fun _ _ => le_max_right _ _)).mp hsum
  have hkt : τ < c k := by
    by_contra h
    have hc : c k ≤ τ := le_of_not_gt h
    have hz : cap (c k) τ = 0 := max_eq_right (sub_nonpos.mpr hc)
    change max (c k - τ) 0 = 0 at hz
    linarith
  refine ⟨k, mem_range.mp hk, min_eq_right hkt.le, ?_⟩
  rw [capR_succ]
  exact lt_add_of_pos_right _ (div_pos hkp hτ)

theorem coeff_pos (n i : ℕ) (hi : i < n) : 0 < coeff n i := by
  unfold coeff
  apply Real.sqrt_pos.2
  have hiR : (i : ℝ) < n := by exact_mod_cast hi
  positivity

theorem coeff_zero_le_one (n : ℕ) (hn : 2 ≤ n) : coeff n 0 ≤ coeff n 1 := by
  have h0 := coeff_sq n 0 (by omega)
  have h1 := coeff_sq n 1 (by omega)
  have hp0 := coeff_nonneg n 0
  have hp1 := coeff_nonneg n 1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at h0 h1
  nlinarith

/-- 左侧首节点的权重为零是由真实系数和根方程推出的。 -/
theorem spin_capR_one (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    capR (coeff n) τ 1 = 0 := by
  have ht := cap_root_gt_first_inner_edge n hn τ hroot
  have hc := (coeff_zero_le_one n (by omega)).trans ht.le
  simp [capR, cap, max_eq_right (sub_nonpos.mpr hc)]

theorem spin_saturated_tail_relation (n : ℕ) (hn : 10 ≤ n) (τ t : ℝ)
    (v : ℕ → ℝ) (ht : 0 ≤ t)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ)
    (hs : Saturated n (capA (coeff n) τ) (capR (coeff n) τ) v t) :
    v 1 = (coeff n 1 / τ) * v 2 := by
  have hcτ := cap_root_gt_first_inner_edge n hn τ hroot
  have hτ : 0 < τ := (coeff_one_pos n hn).trans hcτ
  have ha : ∀ i < n, 0 < capA (coeff n) τ i := by
    intro i hi
    exact lt_min (coeff_pos n i hi) hτ
  have h := saturated_tail_relation n (by omega) (capA (coeff n) τ)
    (capR (coeff n) τ) v t τ ht hτ ha (capR_bounds n (coeff n) τ hτ hroot)
    (fun i _ => capR_monotone_step (coeff n) τ hτ i) hs
    (spin_capR_one n hn τ hroot) (cap_plateau n (coeff n) τ hτ hroot)
  simpa only [capA, min_eq_left hcτ.le] using h

/-- 对全部 n≥10，真实截顶证书的饱和种子不能形成完整家族。 -/
theorem no_complete_saturated_spin_family {α : Type*} (seeds : Finset α)
    (n : ℕ) (hn : 10 ≤ n) (τ : ℝ) (v : α → ℕ → ℝ) (t : α → ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ)
    (ht : ∀ k ∈ seeds, 0 ≤ t k)
    (hs : ∀ k ∈ seeds,
      Saturated n (capA (coeff n) τ) (capR (coeff n) τ) (v k) (t k))
    (hcomplete : ∀ i ≤ n, (∑ k ∈ seeds, v k i ^ 2) = 1) : False := by
  have hcτ := cap_root_gt_first_inner_edge n hn τ hroot
  have hτ : 0 < τ := (coeff_one_pos n hn).trans hcτ
  exact population_obstruction seeds v (coeff n 1 / τ)
    (div_nonneg (coeff_nonneg n 1) hτ.le) ((div_lt_one hτ).2 hcτ)
    (fun k hk => spin_saturated_tail_relation n hn τ (t k) (v k) (ht k hk) hroot (hs k hk))
    (hcomplete 1 (by omega)) (hcomplete 2 (by omega))

end FiniteCopy.Gap

