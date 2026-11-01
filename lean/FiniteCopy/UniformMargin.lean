import FiniteCopy.FiniteGap

open scoped BigOperators
open Finset
open FiniteCopy.Algebra

noncomputable section

namespace FiniteCopy.Gap

/-- 紧集上的零缺陷约束给出统一的正余量，不预设极值取得。 -/
theorem compact_uniform_defect {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (D G : X → ℝ)
    (hD : Continuous D) (hG : Continuous G)
    (hD0 : ∀ x ∈ K, 0 ≤ D x) (hG1 : ∀ x ∈ K, G x ≤ 1)
    (hzero : ∀ x ∈ K, D x = 0 → G x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, δ * (G x - ε) ≤ D x := by
  let L := K ∩ {x | ε ≤ G x}
  have hL : IsCompact L := hK.inter_right (isClosed_le continuous_const hG)
  by_cases hne : L.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hL.exists_isMinOn hne hD.continuousOn
    have hzD : 0 < D z := by
      have hz0 := hD0 z hz.1
      have hzG : ε ≤ G z := hz.2
      by_contra h
      have hdz : D z = 0 := le_antisymm (le_of_not_gt h) hz0
      have := hzero z hz.1 hdz
      linarith
    refine ⟨D z, hzD, ?_⟩
    intro x hx
    by_cases hxe : ε ≤ G x
    · have hdx : D z ≤ D x := hmin ⟨hx, hxe⟩
      have hbound : G x - ε ≤ 1 := by linarith [hG1 x hx]
      calc
        D z * (G x - ε) ≤ D z * 1 := mul_le_mul_of_nonneg_left hbound hzD.le
        _ ≤ D x := by simpa using hdx
    · have hbound : G x - ε ≤ 0 := by linarith
      exact (mul_nonpos_of_nonneg_of_nonpos hzD.le hbound).trans (hD0 x hx)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have hxe : G x < ε := by
      by_contra h
      exact hne ⟨x, hx, le_of_not_gt h⟩
    have := hD0 x hx
    nlinarith

def unitSeeds (n : ℕ) : Set (ℕ → ℝ) :=
  {v | (∀ i, 0 ≤ v i ∧ v i ≤ 1) ∧ mass n v = 1}

theorem continuous_mass (n : ℕ) : Continuous (mass n) := by
  unfold mass
  fun_prop

theorem unitSeeds_compact (n : ℕ) : IsCompact (unitSeeds n) := by
  have hc : IsCompact (Set.univ.pi (fun _ : ℕ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : IsClosed {v : ℕ → ℝ | mass n v = 1} :=
    isClosed_eq (continuous_mass n) continuous_const
  convert hc.inter_right he using 1
  ext v
  simp only [unitSeeds, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Icc, Set.mem_setOf_eq]

def spinDefect (n : ℕ) (τ : ℝ) (v : ℕ → ℝ) : ℝ :=
  diagonalEnergy n (capA (coeff n) τ) (capR (coeff n) τ) v -
    moment n (coeff n) v ^ 2

def tailPopulation (q : ℝ) (v : ℕ → ℝ) : ℝ := v 1 ^ 2 - q ^ 2 * v 2 ^ 2

theorem continuous_spinDefect (n : ℕ) (τ : ℝ) : Continuous (spinDefect n τ) := by
  unfold spinDefect diagonalEnergy moment
  fun_prop

theorem continuous_tailPopulation (q : ℝ) : Continuous (tailPopulation q) := by
  unfold tailPopulation
  fun_prop

theorem unit_seed_moment_nonneg (n : ℕ) (v : ℕ → ℝ) (hv : v ∈ unitSeeds n) :
    0 ≤ moment n (coeff n) v := by
  apply sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (coeff_nonneg n i) (hv.1 i).1) (hv.1 (i+1)).1

theorem unit_seed_defect_nonneg (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ)
    (v : ℕ → ℝ) (hv : v ∈ unitSeeds n) : 0 ≤ spinDefect n τ v := by
  have hτ : 0 < τ := (coeff_one_pos n hn).trans (cap_root_gt_first_inner_edge n hn τ hroot)
  have h := seed_sos_bound n (capA (coeff n) τ) (capR (coeff n) τ) (coeff n) v
    (capR_bounds n (coeff n) τ hτ hroot) (fun i _ => cap_coefficient (coeff n) τ hτ i)
    (by rw [hv.2]; norm_num)
  rw [hv.2, div_one] at h
  exact sub_nonneg.mpr h

theorem unit_seed_defect_zero_tail (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ)
    (v : ℕ → ℝ) (hv : v ∈ unitSeeds n) (hD : spinDefect n τ v = 0) :
    tailPopulation (coeff n 1 / τ) v = 0 := by
  have hτ : 0 < τ := (coeff_one_pos n hn).trans (cap_root_gt_first_inner_edge n hn τ hroot)
  have hm : moment n (fun i => capA (coeff n) τ i *
      (1 - capR (coeff n) τ i + capR (coeff n) τ (i+1))) v = moment n (coeff n) v := by
    unfold moment
    apply sum_congr rfl
    intro i hi
    dsimp only
    rw [cap_coefficient (coeff n) τ hτ i]
  have hid := chain_sos_identity n (capA (coeff n) τ) (capR (coeff n) τ) v
    (moment n (coeff n) v)
  rw [hm, hv.2] at hid
  have hsz : sos n (capA (coeff n) τ) (capR (coeff n) τ) v
      (moment n (coeff n) v) = 0 := by
    unfold spinDefect at hD
    nlinarith
  have hsum : (∑ i ∈ range n, edgeSOS (capA (coeff n) τ) (capR (coeff n) τ) v
      (moment n (coeff n) v) i) = 0 := by
    simpa [sos, edgeSOS, capR_zero, capR_last n (coeff n) τ hτ hroot] using hsz
  have hs := saturated_of_sum_zero n (capA (coeff n) τ) (capR (coeff n) τ) v
    (moment n (coeff n) v) (capR_bounds n (coeff n) τ hτ hroot) hsum
  have hr := spin_saturated_tail_relation n hn τ (moment n (coeff n) v) v
    (unit_seed_moment_nonneg n v hv) hroot hs
  unfold tailPopulation
  rw [hr]
  ring

/-- 此 δ 对本扇区全部归一种子统一有效。 -/
theorem spin_uniform_defect (n : ℕ) (hn : 10 ≤ n) (τ ε : ℝ) (hε : 0 < ε)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    ∃ δ > 0, ∀ v ∈ unitSeeds n,
      δ * (tailPopulation (coeff n 1 / τ) v - ε) ≤ spinDefect n τ v := by
  apply compact_uniform_defect (unitSeeds n) (unitSeeds_compact n) (spinDefect n τ)
    (tailPopulation (coeff n 1 / τ)) (continuous_spinDefect n τ)
    (continuous_tailPopulation _) (unit_seed_defect_nonneg n hn τ hroot)
  · intro v hv
    unfold tailPopulation
    have h1 := hv.1 1
    nlinarith [mul_nonneg (sq_nonneg (coeff n 1 / τ)) (sq_nonneg (v 2))]
  · exact unit_seed_defect_zero_tail n hn τ hroot
  · exact hε

/-- 完备性把归一种子的权重总和固定为节点数。 -/
theorem weighted_unit_mass_sum {α : Type*} (seeds : Finset α) (n : ℕ)
    (v : α → ℕ → ℝ) (w : α → ℝ)
    (hv : ∀ k ∈ seeds, v k ∈ unitSeeds n)
    (hc : ∀ i ≤ n, (∑ k ∈ seeds, w k * v k i ^ 2) = 1) :
    (∑ k ∈ seeds, w k) = (n+1 : ℕ) := by
  calc
    _ = ∑ k ∈ seeds, w k * mass n (v k) := by
      apply sum_congr rfl
      intro k hk
      rw [(hv k hk).2, mul_one]
    _ = ∑ i ∈ range (n+1), ∑ k ∈ seeds, w k * v k i ^ 2 := by
      simp only [mass, mul_sum]
      rw [sum_comm]
    _ = ∑ i ∈ range (n+1), (1 : ℝ) := by
      apply sum_congr rfl
      intro i hi
      exact hc i (by have := mem_range.mp hi; omega)
    _ = (n+1 : ℕ) := by simp

theorem weighted_tail_sum {α : Type*} (seeds : Finset α) (n : ℕ) (hn : 2 ≤ n)
    (v : α → ℕ → ℝ) (w : α → ℝ) (q : ℝ)
    (hc : ∀ i ≤ n, (∑ k ∈ seeds, w k * v k i ^ 2) = 1) :
    (∑ k ∈ seeds, w k * tailPopulation q (v k)) = 1 - q ^ 2 := by
  unfold tailPopulation
  simp_rw [mul_sub]
  rw [sum_sub_distrib, hc 1 (by omega)]
  have he : (∑ k ∈ seeds, w k * (q ^ 2 * v k 2 ^ 2)) =
      q ^ 2 * ∑ k ∈ seeds, w k * v k 2 ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    ring
  rw [he, hc 2 hn, mul_one]

theorem weighted_diagonal_sum {α : Type*} (seeds : Finset α) (n : ℕ)
    (v : α → ℕ → ℝ) (a r c : ℕ → ℝ)
    (weights : α → ℝ)
    (hc : ∀ i ≤ n, (∑ k ∈ seeds, weights k * v k i ^ 2) = 1)
    (ha : ∀ i < n, a i * (1-r i+r (i+1)) = c i) :
    (∑ k ∈ seeds, weights k * diagonalEnergy n a r (v k)) =
      ∑ i ∈ range n, c i * a i := by
  unfold diagonalEnergy
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  have he : (∑ k ∈ seeds, weights k *
      (r (i+1) * a i ^ 2 * v k i ^ 2 + (1-r i) * a i ^ 2 * v k (i+1) ^ 2)) =
      r (i+1) * a i ^ 2 * (∑ k ∈ seeds, weights k * v k i ^ 2) +
      (1-r i) * a i ^ 2 * (∑ k ∈ seeds, weights k * v k (i+1) ^ 2) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    ring
  rw [he, hc i (by omega), hc (i+1) (by omega), ← ha i hin]
  ring

/-- 对任意有限个归一种子，完备性强迫一个与种子数无关的正缺陷。 -/
theorem normalized_spin_uniform_gap {α : Type*} (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    ∃ Δ > 0, ∀ (seeds : Finset α) (v : α → ℕ → ℝ) (w : α → ℝ),
      (∀ k ∈ seeds, 0 ≤ w k) →
      (∀ k ∈ seeds, v k ∈ unitSeeds n) →
      (∀ i ≤ n, (∑ k ∈ seeds, w k * v k i ^ 2) = 1) →
      (∑ k ∈ seeds, w k * moment n (coeff n) (v k) ^ 2) ≤
        (∑ i ∈ range n, coeff n i * capA (coeff n) τ i) - Δ := by
  let q := coeff n 1 / τ
  let g := 1 - q ^ 2
  let d : ℝ := (n+1 : ℕ)
  have hτ : 0 < τ := (coeff_one_pos n hn).trans (cap_root_gt_first_inner_edge n hn τ hroot)
  have hq0 : 0 ≤ q := div_nonneg (coeff_nonneg n 1) hτ.le
  have hq1 : q < 1 := (div_lt_one hτ).2 (cap_root_gt_first_inner_edge n hn τ hroot)
  have hg : 0 < g := by dsimp [g]; nlinarith
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨δ, hδ, hloc⟩ := spin_uniform_defect n hn τ (g/(2*d)) (by positivity) hroot
  refine ⟨δ*g/2, by positivity, ?_⟩
  intro seeds v w hw hv hc
  have hm := weighted_unit_mass_sum seeds n v w hv hc
  have hpop := weighted_tail_sum seeds n (by omega) v w q hc
  have hdiag := weighted_diagonal_sum seeds n v
    (capA (coeff n) τ) (capR (coeff n) τ) (coeff n) w hc
    (fun i _ => cap_coefficient (coeff n) τ hτ i)
  have hs : (∑ k ∈ seeds, w k * (δ * (tailPopulation q (v k) - g/(2*d)))) ≤
      ∑ k ∈ seeds, w k * spinDefect n τ (v k) := by
    apply sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hloc (v k) (hv k hk)) (hw k hk)
  have hleft : (∑ k ∈ seeds, w k * (δ * (tailPopulation q (v k) - g/(2*d)))) = δ*g/2 := by
    calc
      _ = δ * ((∑ k ∈ seeds, w k * tailPopulation q (v k)) -
          g/(2*d) * (∑ k ∈ seeds, w k)) := by
        simp only [mul_sub, mul_sum, sum_sub_distrib]
        congr 1 <;> apply sum_congr rfl <;> intro k hk <;> ring
      _ = δ * (g - g/(2*d)*d) := by rw [hpop, hm]
      _ = δ*g/2 := by field_simp; ring
  have hright : (∑ k ∈ seeds, w k * spinDefect n τ (v k)) =
      (∑ i ∈ range n, coeff n i * capA (coeff n) τ i) -
      (∑ k ∈ seeds, w k * moment n (coeff n) (v k) ^ 2) := by
    simp only [spinDefect, mul_sub, sum_sub_distrib, hdiag]
  rw [hleft, hright] at hs
  linarith

end FiniteCopy.Gap

