import Mathlib

open scoped BigOperators
open Filter Finset

namespace NHLowerBound

noncomputable def cap (x τ : ℝ) : ℝ := max (x - τ) 0

noncomputable def deficit {ι : Type*} (s : Finset ι) (c : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑ i ∈ s, (c i ^ 2 - c i * min (c i) τ)

theorem deficit_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (τ : ℝ) :
    deficit s c τ = ∑ i ∈ s, c i * cap (c i) τ := by
  apply Finset.sum_congr rfl
  intro i hi
  unfold cap
  by_cases h : c i ≤ τ
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

theorem cap_nonneg (x τ : ℝ) : 0 ≤ cap x τ := le_max_right _ _

theorem cap_root_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℝ) (τ : ℝ)
    (hroot : (∑ i ∈ s, cap (c i) τ) = τ) : 0 ≤ τ := by
  rw [← hroot]
  exact Finset.sum_nonneg fun _ _ => cap_nonneg _ _

theorem cap_root_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (τ J : ℝ)
    (hJ : 0 ≤ J) (hc : ∀ i ∈ s, c i ≤ J)
    (hroot : (∑ i ∈ s, cap (c i) τ) = τ) : τ ≤ J := by
  by_contra h
  have hlt : J < τ := lt_of_not_ge h
  have hz : (∑ i ∈ s, cap (c i) τ) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact max_eq_right (sub_nonpos.mpr ((hc i hi).trans (le_of_lt hlt)))
  linarith

theorem deficit_bounds {ι : Type*} (s : Finset ι) (c : ι → ℝ) (τ J : ℝ)
    (hJ : 0 ≤ J) (hc : ∀ i ∈ s, c i ≤ J)
    (hroot : (∑ i ∈ s, cap (c i) τ) = τ) :
    τ ^ 2 ≤ deficit s c τ ∧ deficit s c τ ≤ J * τ ∧ J * τ ≤ J ^ 2 := by
  have ht := cap_root_nonneg s c τ hroot
  have htJ := cap_root_le s c τ J hJ hc hroot
  rw [deficit_eq]
  constructor
  · calc
      τ ^ 2 = ∑ i ∈ s, τ * cap (c i) τ := by rw [← Finset.mul_sum, hroot]; ring
      _ ≤ ∑ i ∈ s, c i * cap (c i) τ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : c i ≤ τ
        · simp [cap, max_eq_right (sub_nonpos.mpr h)]
        · exact mul_le_mul_of_nonneg_right (le_of_not_ge h) (cap_nonneg _ _)
  · constructor
    · calc
        (∑ i ∈ s, c i * cap (c i) τ) ≤ ∑ i ∈ s, J * cap (c i) τ := by
          exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hc i hi) (cap_nonneg _ _)
        _ = J * τ := by rw [← Finset.mul_sum, hroot]
    · nlinarith

-- n=2j−1，因此 d=n+2 覆盖全部正自旋扇区。
noncomputable def J (n : ℕ) : ℝ := ((n : ℝ) + 2) / 2
noncomputable def coeff (n i : ℕ) : ℝ := Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) + 1 - i))
noncomputable def D (n : ℕ) (τ : ℝ) : ℝ := deficit (Finset.range (n + 1)) (coeff n) τ

theorem J_pos (n : ℕ) : 0 < J n := by unfold J; positivity

theorem coeff_sq (n i : ℕ) (hi : i < n + 1) :
    coeff n i ^ 2 = J n ^ 2 - ((i : ℝ) + 1 - J n) ^ 2 := by
  have hi' : (i : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp hi)
  rw [coeff, Real.sq_sqrt (mul_nonneg (by positivity) (by linarith))]
  unfold J
  ring

theorem coeff_le (n i : ℕ) (hi : i < n + 1) : coeff n i ≤ J n := by
  have h := coeff_sq n i hi
  have hp := J_pos n
  have hc : 0 ≤ coeff n i := Real.sqrt_nonneg _
  nlinarith [sq_nonneg ((i : ℝ) + 1 - J n)]

theorem spin_deficit_bounds (n : ℕ) (τ : ℝ)
    (hroot : (∑ i ∈ Finset.range (n + 1), cap (coeff n i) τ) = τ) :
    τ ^ 2 ≤ D n τ ∧ D n τ ≤ J n * τ ∧ J n * τ ≤ J n ^ 2 := by
  exact deficit_bounds _ _ _ _ (le_of_lt (J_pos n))
    (fun i hi => coeff_le n i (Finset.mem_range.mp hi)) hroot

theorem central_mem (n m k : ℕ) (hn : 2 * m ≤ n) (hk : k < m) :
    n / 2 + k < n + 1 := by
  have h := Nat.div_mul_le_self n 2
  omega

theorem central_lower (n m k : ℕ) (hm : 0 < m) (hn : 2 * m ≤ n) (hk : k < m) :
    J n - m ≤ coeff n (n / 2 + k) := by
  have hdiv := Nat.div_mul_le_self n 2
  have hrem := Nat.mod_lt n (by decide : 0 < 2)
  have hdecomp := Nat.mod_add_div n 2
  have hdivR : 2 * (n / 2 : ℕ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
  have hdivR' : (n : ℝ) < 2 * (n / 2 : ℕ) + 2 := by
    exact_mod_cast (show n < 2 * (n / 2) + 2 by omega)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : 2 * (m : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (k : ℝ) < m := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hs := coeff_sq n (n / 2 + k) (central_mem n m k hn hk)
  have hc : 0 ≤ coeff n (n / 2 + k) := Real.sqrt_nonneg _
  have hjm : 0 ≤ J n - m := by unfold J; linarith
  have hlo : -(m : ℝ) ≤ (n / 2 + k : ℕ) + 1 - J n := by
    push_cast
    unfold J
    linarith
  have hhi : (n / 2 + k : ℕ) + 1 - J n ≤ (m : ℝ) := by
    push_cast
    unfold J
    linarith
  have hsq : ((n / 2 + k : ℕ) + 1 - J n) ^ 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith
  nlinarith

theorem central_cap_bound (n m : ℕ) (τ : ℝ) (hm : 0 < m) (hn : 2 * m ≤ n)
    (hroot : (∑ i ∈ Finset.range (n + 1), cap (coeff n i) τ) = τ) :
    (m : ℝ) * (J n - m - τ) ≤ τ := by
  let s := (Finset.range m).image (fun k => n / 2 + k)
  have hsub : s ⊆ Finset.range (n + 1) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
    exact Finset.mem_range.mpr (central_mem n m k hn (Finset.mem_range.mp hk))
  calc
    (m : ℝ) * (J n - m - τ) = ∑ k ∈ Finset.range m, (J n - m - τ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range m, cap (coeff n (n / 2 + k)) τ := by
      apply Finset.sum_le_sum
      intro k hk
      exact le_trans (sub_le_sub_right (central_lower n m k hm hn (Finset.mem_range.mp hk)) τ)
        (le_max_left _ _)
    _ = ∑ i ∈ s, cap (coeff n i) τ := by
      dsimp only [s]
      rw [Finset.sum_image]
      intro a ha b hb hab
      dsimp only at hab
      omega
    _ ≤ ∑ i ∈ Finset.range (n + 1), cap (coeff n i) τ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => cap_nonneg _ _)
    _ = τ := hroot

theorem cap_ratio_tendsto (τ : ℕ → ℝ)
    (hroot : ∀ n, (∑ i ∈ Finset.range (n + 1), cap (coeff n i) (τ n)) = τ n) :
    Tendsto (fun n => τ n / J n) atTop (nhds 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha0
        (div_nonneg (cap_root_nonneg _ _ _ (hroot n)) (le_of_lt (J_pos n)))
    have ha0' : 0 ≤ a := le_of_not_gt ha0
    have hden : 0 < 1 - a := sub_pos.mpr ha
    obtain ⟨m, hm⟩ := exists_nat_gt (a / (1 - a) + 1)
    have hmposR : (0 : ℝ) < m := by have := div_nonneg ha0' (le_of_lt hden); linarith
    have hmpos : 0 < m := by exact_mod_cast hmposR
    have hdelta : 0 < (m : ℝ) - ((m : ℝ) + 1) * a := by
      have hh : a / (1 - a) < (m : ℝ) := by linarith
      have := (div_lt_iff₀ hden).mp hh
      nlinarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) ^ 2 / ((m : ℝ) - ((m : ℝ) + 1) * a))
    filter_upwards [eventually_ge_atTop (max (2 * m) (2 * N))] with n hn
    have hnm : 2 * m ≤ n := (le_max_left _ _).trans hn
    have hnN : 2 * N ≤ n := (le_max_right _ _).trans hn
    have hnNR : 2 * (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hJN : (N : ℝ) ≤ J n := by unfold J; linarith
    have hgap : (m : ℝ) ^ 2 < ((m : ℝ) - ((m : ℝ) + 1) * a) * J n := by
      have hh := (div_lt_iff₀ hdelta).mp hN
      nlinarith
    have hcap := central_cap_bound n m (τ n) hmpos hnm (hroot n)
    apply (lt_div_iff₀ (J_pos n)).mpr
    nlinarith
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_le_of_lt
      ((div_le_one (J_pos n)).mpr (cap_root_le _ _ _ _ (le_of_lt (J_pos n))
        (fun i hi => coeff_le n i (Finset.mem_range.mp hi)) (hroot n))) ha

theorem cap_root_unique {ι : Type*} (s : Finset ι) (c : ι → ℝ) (a b : ℝ)
    (ha : (∑ i ∈ s, cap (c i) a) = a) (hb : (∑ i ∈ s, cap (c i) b) = b) : a = b := by
  have hmono : ∀ x y : ℝ, x ≤ y → (∑ i ∈ s, cap (c i) y) ≤ ∑ i ∈ s, cap (c i) x := by
    intro x y hxy
    exact Finset.sum_le_sum fun i hi => max_le_max (sub_le_sub_left hxy _) le_rfl
  rcases lt_trichotomy a b with hab | hab | hab
  · have := hmono a b (le_of_lt hab)
    linarith
  · exact hab
  · have := hmono b a (le_of_lt hab)
    linarith

theorem cap_root_exists (n : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ (∑ i ∈ Finset.range (n + 1), cap (coeff n i) τ) = τ := by
  let f : ℝ → ℝ := fun t => (∑ i ∈ Finset.range (n + 1), cap (coeff n i) t) - t
  have hf : Continuous f := by unfold f cap; fun_prop
  have hf0 : 0 < f 0 := by
    simp only [f, sub_zero]
    apply Finset.sum_pos'
    · exact fun _ _ => cap_nonneg _ _
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hc : 0 < coeff n 0 := by
        unfold coeff
        simp only [Nat.cast_zero, zero_add, one_mul, sub_zero]
        positivity
      exact lt_of_lt_of_le hc (by simpa only [cap, sub_zero] using
        (le_max_left (coeff n 0) (0 : ℝ)))
  have hfJ : f (J n) ≤ 0 := by
    have hsum : (∑ i ∈ Finset.range (n + 1), cap (coeff n i) (J n)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact max_eq_right (sub_nonpos.mpr (coeff_le n i (Finset.mem_range.mp hi)))
    dsimp only [f]
    rw [hsum]
    linarith [J_pos n]
  obtain ⟨τ, hτ, hz⟩ := intermediate_value_Icc' (le_of_lt (J_pos n)) hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f (J n)) (f 0) from ⟨hfJ, le_of_lt hf0⟩)
  have hroot : (∑ i ∈ Finset.range (n + 1), cap (coeff n i) τ) = τ := by
    dsimp only [f] at hz
    linarith
  refine ⟨τ, ?_, hroot⟩
  rcases lt_or_eq_of_le hτ.1 with h | h
  · exact h
  · rw [← h] at hz
    linarith

theorem D_eq_sub_sums (n : ℕ) (τ : ℝ) :
    D n τ = (∑ i ∈ Finset.range (n + 1), coeff n i ^ 2) -
      ∑ i ∈ Finset.range (n + 1), coeff n i * min (coeff n i) τ := by
  unfold D deficit
  rw [Finset.sum_sub_distrib]

theorem deficit_ratio_tendsto (τ : ℕ → ℝ)
    (hroot : ∀ n, (∑ i ∈ Finset.range (n + 1), cap (coeff n i) (τ n)) = τ n) :
    Tendsto (fun n => D n (τ n) / J n ^ 2) atTop (nhds 1) := by
  have hl : Tendsto (fun n => (τ n / J n) ^ 2) atTop (nhds 1) := by
    simpa using (cap_ratio_tendsto τ hroot).pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    dsimp only
    rw [div_pow]
    exact div_le_div_of_nonneg_right (spin_deficit_bounds n (τ n) (hroot n)).1
      (sq_nonneg _)
  · intro n
    exact (div_le_one (sq_pos_of_pos (J_pos n))).mpr
      ((spin_deficit_bounds n (τ n) (hroot n)).2.1.trans
        (spin_deficit_bounds n (τ n) (hroot n)).2.2)

-- d=n+2，j=(n+1)/2。这是所需 D/(dj)→1/2 的完整离散极限。
theorem lower_bound_asymptotic (τ : ℕ → ℝ)
    (hroot : ∀ n, (∑ i ∈ Finset.range (n + 1), cap (coeff n i) (τ n)) = τ n) :
    Tendsto (fun n => D n (τ n) / (((n : ℝ) + 2) * (((n : ℝ) + 1) / 2)))
      atTop (nhds (1 / 2)) := by
  have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hfactor : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) / 2) atTop
      (nhds (1 / 2 : ℝ)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).add hsmall).div_const 2
  have hlim := (deficit_ratio_tendsto τ hroot).mul hfactor
  simp only [one_mul] at hlim
  convert hlim using 1
  ext n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  dsimp only [J]
  field_simp
  ring

-- 用已证存在性定义唯一截顶根，最终定理不再带根方程假设。
noncomputable def tau (n : ℕ) : ℝ := Classical.choose (cap_root_exists n)

theorem tau_pos (n : ℕ) : 0 < tau n := (Classical.choose_spec (cap_root_exists n)).1

theorem tau_spec (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), cap (coeff n i) (tau n)) = tau n :=
  (Classical.choose_spec (cap_root_exists n)).2

theorem tau_ratio_limit : Tendsto (fun n => tau n / J n) atTop (nhds 1) :=
  cap_ratio_tendsto tau tau_spec

theorem canonical_lower_bound_asymptotic :
    Tendsto (fun n => D n (tau n) / (((n : ℝ) + 2) * (((n : ℝ) + 1) / 2)))
      atTop (nhds (1 / 2)) := lower_bound_asymptotic tau tau_spec

end NHLowerBound
