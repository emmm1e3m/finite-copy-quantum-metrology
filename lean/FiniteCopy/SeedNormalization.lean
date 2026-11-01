import FiniteCopy.UniformMargin

open scoped BigOperators
open Finset
open FiniteCopy.Algebra

noncomputable section

namespace FiniteCopy.Gap

def normalizeSeed (n : ℕ) (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i ≤ n then v i / Real.sqrt (mass n v) else 0

theorem normalizeSeed_at (n : ℕ) (v : ℕ → ℝ) (i : ℕ) (hi : i ≤ n) :
    normalizeSeed n v i = v i / Real.sqrt (mass n v) := by
  simp [normalizeSeed, hi]

theorem normalizeSeed_mass (n : ℕ) (v : ℕ → ℝ) (hm : 0 < mass n v) :
    mass n (normalizeSeed n v) = 1 := by
  have he : mass n (normalizeSeed n v) = mass n v / Real.sqrt (mass n v) ^ 2 := by
    unfold mass
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [normalizeSeed_at n v i (by have := mem_range.mp hi; omega), div_pow]
    rfl
  rw [he, Real.sq_sqrt hm.le, div_self (ne_of_gt hm)]

theorem normalizeSeed_mem (n : ℕ) (v : ℕ → ℝ) (hm : 0 < mass n v)
    (hv : ∀ i ≤ n, 0 ≤ v i) : normalizeSeed n v ∈ unitSeeds n := by
  refine ⟨?_, normalizeSeed_mass n v hm⟩
  intro i
  by_cases hi : i ≤ n
  · rw [normalizeSeed_at n v i hi]
    have hsq : v i ^ 2 ≤ mass n v :=
      single_le_sum (fun k _ => sq_nonneg (v k)) (mem_range.mpr (by omega))
    have hs := Real.sq_sqrt hm.le
    have hp := Real.sqrt_pos.2 hm
    constructor
    · exact div_nonneg (hv i hi) hp.le
    · apply (div_le_one hp).2
      nlinarith
  · simp [normalizeSeed, hi]

theorem normalizeSeed_population (n : ℕ) (v : ℕ → ℝ) (hm : 0 < mass n v)
    (i : ℕ) (hi : i ≤ n) : mass n v * normalizeSeed n v i ^ 2 = v i ^ 2 := by
  rw [normalizeSeed_at n v i hi, div_pow, Real.sq_sqrt hm.le]
  field_simp

theorem normalizeSeed_moment (n : ℕ) (c v : ℕ → ℝ) (hm : 0 < mass n v) :
    moment n c (normalizeSeed n v) = moment n c v / mass n v := by
  unfold moment
  rw [sum_div]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [normalizeSeed_at n v i (by omega), normalizeSeed_at n v (i+1) (by omega)]
  calc
    _ = (c i * v i * v (i+1)) / Real.sqrt (mass n v) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hm.le]

/-- 归一化保持原始种子商目标。 -/
theorem normalizeSeed_objective (n : ℕ) (c v : ℕ → ℝ) (hm : 0 < mass n v) :
    mass n v * moment n c (normalizeSeed n v) ^ 2 =
      moment n c v ^ 2 / mass n v := by
  rw [normalizeSeed_moment n c v hm]
  have hmass : mass n v ≠ 0 := ne_of_gt hm
  field_simp

/-- 真实自旋的统一有限种子缺陷；Δ 在种子家族选定之前产生。 -/
theorem finite_spin_uniform_gap {α : Type*} (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    ∃ Δ > 0, ∀ (seeds : Finset α) (v : α → ℕ → ℝ),
      (∀ k ∈ seeds, ∀ i ≤ n, 0 ≤ v k i) →
      (∀ k ∈ seeds, 0 < mass n (v k)) →
      (∀ i ≤ n, (∑ k ∈ seeds, v k i ^ 2) = 1) →
      (∑ k ∈ seeds, moment n (coeff n) (v k) ^ 2 / mass n (v k)) ≤
        (∑ i ∈ range n, coeff n i * capA (coeff n) τ i) - Δ := by
  obtain ⟨Δ, hΔ, hbound⟩ := normalized_spin_uniform_gap (α := α) n hn τ hroot
  refine ⟨Δ, hΔ, ?_⟩
  intro seeds v hv hm hc
  have hcomplete : ∀ i ≤ n,
      (∑ k ∈ seeds, mass n (v k) * normalizeSeed n (v k) i ^ 2) = 1 := by
    intro i hi
    calc
      _ = ∑ k ∈ seeds, v k i ^ 2 := by
        apply sum_congr rfl
        intro k hk
        exact normalizeSeed_population n (v k) (hm k hk) i hi
      _ = 1 := hc i hi
  have h := hbound seeds (fun k => normalizeSeed n (v k)) (fun k => mass n (v k))
    (fun k hk => (hm k hk).le) (fun k hk => normalizeSeed_mem n (v k) (hm k hk) (hv k hk))
    hcomplete
  have he : (∑ k ∈ seeds, mass n (v k) * moment n (coeff n) (normalizeSeed n (v k)) ^ 2) =
      ∑ k ∈ seeds, moment n (coeff n) (v k) ^ 2 / mass n (v k) := by
    apply sum_congr rfl
    intro k hk
    exact normalizeSeed_objective n (coeff n) (v k) (hm k hk)
  rwa [he] at h

/-- 同一正差传递到 Fisher trace 的实际有限种子定义。 -/
theorem finite_spin_fisher_uniform_gap {α : Type*} (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    ∃ ε > 0, ∀ (seeds : Finset α) (v : α → ℕ → ℝ),
      (∀ k ∈ seeds, ∀ i ≤ n, 0 ≤ v k i) →
      (∀ k ∈ seeds, 0 < mass n (v k)) →
      (∀ i ≤ n, (∑ k ∈ seeds, v k i ^ 2) = 1) →
      fisher seeds n (coeff n) v ≤
        4 / (n+1 : ℕ) * (∑ i ∈ range n, coeff n i * capA (coeff n) τ i) - ε := by
  obtain ⟨Δ, hΔ, hbound⟩ := finite_spin_uniform_gap (α := α) n hn τ hroot
  refine ⟨4 / (n+1 : ℕ) * Δ, by positivity, ?_⟩
  intro seeds v hv hm hc
  have h := mul_le_mul_of_nonneg_left (hbound seeds v hv hm hc)
    (show (0 : ℝ) ≤ 4 / (n+1 : ℕ) by positivity)
  simpa only [fisher, mul_sub] using h

/-- 用自然数重标有限种子，允许任意有限基数。 -/
def finiteSeedValues (n : ℕ) (c : ℕ → ℝ) : Set ℝ :=
  {z | ∃ (seeds : Finset ℕ) (v : ℕ → ℕ → ℝ),
    (∀ k ∈ seeds, ∀ i ≤ n, 0 ≤ v k i) ∧
    (∀ k ∈ seeds, 0 < mass n (v k)) ∧
    (∀ i ≤ n, (∑ k ∈ seeds, v k i ^ 2) = 1) ∧
    z = ∑ k ∈ seeds, moment n c (v k) ^ 2 / mass n (v k)}

theorem finiteSeedValues_nonempty (n : ℕ) (c : ℕ → ℝ) :
    (finiteSeedValues n c).Nonempty := by
  let v : ℕ → ℕ → ℝ := fun k i => if k = i then 1 else 0
  refine ⟨∑ k ∈ range (n+1), moment n c (v k) ^ 2 / mass n (v k),
    range (n+1), v, ?_, ?_, ?_, rfl⟩
  · intro k hk i hi
    dsimp [v]
    split_ifs <;> norm_num
  · intro k hk
    apply mass_pos_of_component n (v k) k (by have := mem_range.mp hk; omega)
    simp [v]
  · intro i hi
    simp [v, mem_range.mpr (show i < n+1 by omega)]

/-- 对全部有限种子目标的真实上确界严格不足，未使用“取得最大值”假设。 -/
theorem finite_seed_sup_strict (n : ℕ) (hn : 10 ≤ n) (τ : ℝ)
    (hroot : (∑ i ∈ range n, cap (coeff n i) τ) = τ) :
    sSup (finiteSeedValues n (coeff n)) <
      ∑ i ∈ range n, coeff n i * capA (coeff n) τ i := by
  obtain ⟨Δ, hΔ, hbound⟩ := finite_spin_uniform_gap (α := ℕ) n hn τ hroot
  have hs : sSup (finiteSeedValues n (coeff n)) ≤
      (∑ i ∈ range n, coeff n i * capA (coeff n) τ i) - Δ := by
    apply csSup_le (finiteSeedValues_nonempty n (coeff n))
    intro z hz
    rcases hz with ⟨seeds, v, hv, hm, hc, rfl⟩
    exact hbound seeds v hv hm hc
  linarith

end FiniteCopy.Gap

