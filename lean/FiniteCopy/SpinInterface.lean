import FiniteCopy.Algebra
import FiniteCopy.LowerBound

open scoped BigOperators
open Filter Finset

namespace NHLowerBound

open FiniteCopy.Algebra

-- 本文件统一采用 n=2j=d−1；LowerBound 内部索引为 n−1。
theorem coeff_eq_spinEdge_succ (n i : ℕ) : coeff n i = spinEdge (n + 1) i := by
  simp only [coeff, spinEdge, Nat.cast_add, Nat.cast_one]

noncomputable def spinTau (n : ℕ) : ℝ := if n = 0 then 0 else tau (n - 1)

noncomputable def spinD (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, spinEdge n i ^ 2) -
    ∑ i ∈ Finset.range n, spinEdge n i * min (spinEdge n i) (spinTau n)

noncomputable def spinL (n : ℕ) : ℝ := spinD n / ((n : ℝ) + 1)

@[simp] theorem spinTau_zero : spinTau 0 = 0 := by simp [spinTau]
@[simp] theorem spinTau_succ (n : ℕ) : spinTau (n + 1) = tau n := by simp [spinTau]
@[simp] theorem spinD_zero : spinD 0 = 0 := by simp [spinD]
@[simp] theorem spinL_zero : spinL 0 = 0 := by simp [spinL]

theorem spinD_succ (n : ℕ) : spinD (n + 1) = D n (tau n) := by
  rw [D_eq_sub_sums]
  simp only [spinD, spinTau_succ, coeff_eq_spinEdge_succ]

theorem spinTau_pos (n : ℕ) (hn : 0 < n) : 0 < spinTau n := by
  cases n with
  | zero => omega
  | succ n => simpa using tau_pos n

theorem spinTau_spec (n : ℕ) :
    (∑ i ∈ Finset.range n, max (spinEdge n i - spinTau n) 0) = spinTau n := by
  cases n with
  | zero => simp
  | succ n => simpa only [spinTau_succ, cap, coeff_eq_spinEdge_succ] using tau_spec n

theorem spinTau_unique (n : ℕ) (t : ℝ)
    (ht : (∑ i ∈ Finset.range n, max (spinEdge n i - t) 0) = t) :
    t = spinTau n := by
  exact cap_root_unique (Finset.range n) (spinEdge n) t (spinTau n) ht (spinTau_spec n)

theorem spinTau_existsUnique (n : ℕ) :
    ∃! t : ℝ, (∑ i ∈ Finset.range n, max (spinEdge n i - t) 0) = t := by
  exact ⟨spinTau n, spinTau_spec n, fun t ht => spinTau_unique n t ht⟩

-- 将已证明的真实根直接代入 013 的完整有限种子 SOS 证书。
theorem canonical_spin_variance_lower_bound {α : Type*} (seeds : Finset α)
    (n : ℕ) (v : α → ℕ → ℝ)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    spinL n ≤ variance seeds n (spinA n) (spinEdge n) v := by
  by_cases hn : n = 0
  · subst n
    rw [spinL_zero, (spin_zero_fisher_variance seeds v).2]
  · simpa only [spinL, spinD, Nat.cast_add, Nat.cast_one] using
      capped_spin_variance_lower_bound seeds n (spinTau n) v
        (spinTau_pos n (Nat.pos_of_ne_zero hn)) (spinTau_spec n) hv hm

theorem spinL_nonneg (n : ℕ) : 0 ≤ spinL n := by
  cases n with
  | zero => simp
  | succ n =>
      unfold spinL
      rw [spinD_succ]
      exact div_nonneg ((sq_nonneg _).trans (spin_deficit_bounds n (tau n) (tau_spec n)).1)
        (by positivity)

theorem spinL_upper (n : ℕ) : spinL n ≤ (n : ℝ) / 4 + 1 / 4 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hb := spin_deficit_bounds n (tau n) (tau_spec n)
      unfold spinL
      rw [spinD_succ]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (↑(n + 1) + 1))).mpr
      have h := hb.2.1.trans hb.2.2
      simp only [J, Nat.cast_add, Nat.cast_one] at *
      nlinarith

theorem canonical_spinTau_ratio_limit :
    Tendsto (fun n : ℕ => spinTau n / (((n : ℝ) + 1) / 2))
      atTop (nhds (1 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [spinTau_succ, J, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num] using tau_ratio_limit

theorem canonical_spinD_ratio_limit :
    Tendsto (fun n : ℕ => spinD n / (((n : ℝ) + 1) / 2) ^ 2)
      atTop (nhds (1 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [spinD_succ, J, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num] using deficit_ratio_tendsto tau tau_spec

theorem canonical_spin_lower_bound_asymptotic :
    Tendsto (fun n : ℕ => spinD n / (((n : ℝ) + 1) * ((n : ℝ) / 2)))
      atTop (nhds (1 / 2 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [spinD_succ, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num] using canonical_lower_bound_asymptotic

theorem canonical_spinL_ratio_limit :
    Tendsto (fun n : ℕ => spinL n / ((n : ℝ) / 2)) atTop (nhds (1 / 2 : ℝ)) := by
  simpa only [spinL, div_div] using canonical_spin_lower_bound_asymptotic

end NHLowerBound

