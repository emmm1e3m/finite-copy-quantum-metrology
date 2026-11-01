import FiniteCopy.NHOptimization
open scoped BigOperators
open Finset Filter Asymptotics

namespace FiniteCopy.NHOptimization
open FiniteCopy.Algebra NHLowerBound

noncomputable def canonicalA (n : ℕ) : ℕ → ℝ := capA (spinEdge n) (spinTau n)
noncomputable def canonicalR (n : ℕ) : ℕ → ℝ := capR (spinEdge n) (spinTau n)
noncomputable def spinS (n : ℕ) : ℝ := capSum n (spinEdge n) (canonicalA n)

theorem spinTau_nonneg (n : ℕ) : 0 ≤ spinTau n := by
  cases n with
  | zero => simp
  | succ n => exact (spinTau_pos _ (by omega)).le

theorem canonicalA_nonneg (n i : ℕ) : 0 ≤ canonicalA n i :=
  le_min (spinEdge_nonneg n i) (spinTau_nonneg n)

theorem canonicalA_last (n : ℕ) : canonicalA n n = 0 := by
  simp only [canonicalA, capA, spinEdge_last]
  exact min_eq_left (spinTau_nonneg n)

theorem spinEdge_pos {n i : ℕ} (hi : i < n) : 0 < spinEdge n i := by
  unfold spinEdge
  apply Real.sqrt_pos.mpr
  have : (i : ℝ) < n := by exact_mod_cast hi
  positivity

theorem canonicalA_pos {n i : ℕ} (hi : i < n) : 0 < canonicalA n i :=
  lt_min (spinEdge_pos hi) (spinTau_pos n (by omega))

theorem spinEdge_mono_left {n i k : ℕ} (hk : k ≤ i) (hi : 2*i+1 ≤ n) :
    spinEdge n k ≤ spinEdge n i := by
  have hki : (k : ℝ) ≤ i := by exact_mod_cast hk
  have hni : (2 : ℝ)*i+1 ≤ n := by exact_mod_cast hi
  have hmul : 0 ≤ ((i : ℝ)-k)*((n : ℝ)-1-i-k) :=
    mul_nonneg (by linarith) (by linarith)
  apply (sq_le_sq₀ (spinEdge_nonneg n k) (spinEdge_nonneg n i)).mp
  rw [spinEdge_sq n k (by omega), spinEdge_sq n i (by omega)]
  nlinarith

theorem spinEdge_mono_right {n i k : ℕ} (hik : i ≤ k) (hk : k ≤ n) (hi : n ≤ 2*i+1) :
    spinEdge n k ≤ spinEdge n i := by
  have hki : (i : ℝ) ≤ k := by exact_mod_cast hik
  have hni : (n : ℝ) ≤ 2*i+1 := by exact_mod_cast hi
  have hmul : 0 ≤ ((k : ℝ)-i)*((i : ℝ)+k+1-n) :=
    mul_nonneg (by linarith) (by linarith)
  apply (sq_le_sq₀ (spinEdge_nonneg n k) (spinEdge_nonneg n i)).mp
  rw [spinEdge_sq n k hk, spinEdge_sq n i (by omega)]
  nlinarith

theorem min_lt_min_same {a b t : ℝ} (h : min a t < min b t) : a < b ∧ a < t := by
  have ha : a ≤ t := by
    by_contra! ht
    rw [min_eq_right ht.le] at h
    exact (not_lt_of_ge (min_le_right b t)) h
  rw [min_eq_left ha] at h
  exact ⟨h.trans_le (min_le_left b t), h.trans_le (min_le_right b t)⟩

/-- 在严格上升的未截顶尾部，之前的截顶余量全部为零。 -/
theorem canonicalR_of_rise {n i : ℕ} (hi : i+1 ≤ n)
    (h : canonicalA n i < canonicalA n (i+1)) : canonicalR n (i+1) = 0 := by
  obtain ⟨hc, ht⟩ := min_lt_min_same h
  have hsq := (sq_lt_sq₀ (spinEdge_nonneg n i) (spinEdge_nonneg n (i+1))).mpr hc
  rw [spinEdge_sq n i (by omega), spinEdge_sq n (i+1) hi] at hsq
  push_cast at hsq
  have hmid : 2*i+1 ≤ n := by
    have : (2 : ℝ)*i+2 < n := by nlinarith
    have : 2*i+2 < n := by exact_mod_cast this
    omega
  unfold canonicalR capR
  have hz : (∑ k ∈ range (i+1), max (spinEdge n k-spinTau n) 0) = 0 := by
    apply sum_eq_zero
    intro k hk
    have hle := spinEdge_mono_left (n := n) (i := i) (k := k) (by simpa using mem_range.mp hk) hmid
    exact max_eq_right (sub_nonpos.mpr (hle.trans ht.le))
  rw [hz, zero_div]

/-- 在严格下降的未截顶尾部，之后的截顶余量全部为零。 -/
theorem canonicalR_of_fall {n i : ℕ} (hi : i+1 ≤ n)
    (h : canonicalA n (i+1) < canonicalA n i) : canonicalR n (i+1) = 1 := by
  obtain ⟨hc, ht⟩ := min_lt_min_same h
  have hsq := (sq_lt_sq₀ (spinEdge_nonneg n (i+1)) (spinEdge_nonneg n i)).mpr hc
  rw [spinEdge_sq n (i+1) hi, spinEdge_sq n i (by omega)] at hsq
  push_cast at hsq
  have hmid : n ≤ 2*(i+1)+1 := by
    have : (n : ℝ) < 2*i+2 := by nlinarith
    have : n < 2*i+2 := by exact_mod_cast this
    omega
  have hsum : (∑ k ∈ range (i+1), max (spinEdge n k-spinTau n) 0) =
      ∑ k ∈ range n, max (spinEdge n k-spinTau n) 0 := by
    apply sum_subset (range_mono hi)
    intro k hk hki
    have hle := spinEdge_mono_right (n := n) (i := i+1) (k := k)
      (by simp only [mem_range] at hki; omega) (by have := mem_range.mp hk; omega) hmid
    exact max_eq_right (sub_nonpos.mpr (hle.trans ht.le))
  unfold canonicalR capR
  rw [hsum, spinTau_spec, div_self (spinTau_pos n (by omega)).ne']

theorem canonicalR_bounds (n : ℕ) :
    ∀ i ≤ n, 0 ≤ canonicalR n i ∧ canonicalR n i ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    intro i hi
    have : i = 0 := by omega
    simp [this, canonicalR, capR_zero]
  · exact capR_bounds n (spinEdge n) (spinTau n)
      (spinTau_pos n (Nat.pos_of_ne_zero hn)) (spinTau_spec n)

theorem canonical_coefficient (n i : ℕ) (hi : i < n) :
    canonicalA n i * (1-canonicalR n i+canonicalR n (i+1)) = spinEdge n i :=
  cap_coefficient (spinEdge n) (spinTau n) (spinTau_pos n (by omega)) i

/-- 截顶平台上的两项相等，平台外的混合权重严格选择较大项。 -/
theorem canonical_max_support (n i : ℕ) (hi : i ≤ n) :
    max ((previous (canonicalA n) i)^2) ((canonicalA n i)^2) =
      canonicalR n i * (previous (canonicalA n) i)^2 +
        (1-canonicalR n i) * (canonicalA n i)^2 := by
  cases i with
  | zero =>
      simp only [previous, canonicalR, capR_zero, zero_pow (by decide : 2 ≠ 0),
        zero_mul, sub_zero, one_mul, zero_add]
      exact max_eq_right (sq_nonneg _)
  | succ i =>
      simp only [previous]
      rcases lt_trichotomy (canonicalA n i) (canonicalA n (i+1)) with h | h | h
      · rw [canonicalR_of_rise hi h]
        simp only [zero_mul, sub_zero, one_mul, zero_add]
        exact max_eq_right ((sq_le_sq₀ (canonicalA_nonneg n i) (canonicalA_nonneg n (i+1))).mpr h.le)
      · rw [h, max_self]
        ring
      · rw [canonicalR_of_fall hi h]
        simp only [one_mul, sub_self, zero_mul, add_zero]
        exact max_eq_left ((sq_le_sq₀ (canonicalA_nonneg n (i+1)) (canonicalA_nonneg n i)).mpr h.le)

theorem canonical_attains (n : ℕ) : chainObjective n (canonicalA n) = spinS n := by
  unfold chainObjective
  have hs := support_sum n (canonicalR n) (canonicalA n)
  rw [canonicalA_last] at hs
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hs
  calc
    _ = ∑ i ∈ range (n+1), (canonicalR n i * (previous (canonicalA n) i)^2 +
          (1-canonicalR n i)*(canonicalA n i)^2) := by
      apply sum_congr rfl
      intro i hi
      exact canonical_max_support n i (by simpa using mem_range.mp hi)
    _ = ∑ i ∈ range n, (1-canonicalR n i+canonicalR n (i+1))*(canonicalA n i)^2 := hs
    _ = spinS n := by
      unfold spinS capSum
      apply sum_congr rfl
      intro i hi
      rw [← canonical_coefficient n i (mem_range.mp hi)]
      ring

theorem spinS_nonneg (n : ℕ) : 0 ≤ spinS n := by
  unfold spinS capSum
  exact sum_nonneg (fun i _ => mul_nonneg (spinEdge_nonneg n i) (canonicalA_nonneg n i))

theorem spinS_pos {n : ℕ} (hn : 0 < n) : 0 < spinS n := by
  have h0 := mul_pos (spinEdge_pos (i := 0) hn) (canonicalA_pos (i := 0) hn)
  exact h0.trans_le (single_le_sum
    (fun i (_ : i ∈ range n) => mul_nonneg (spinEdge_nonneg n i) (canonicalA_nonneg n i))
    (mem_range.mpr hn))

theorem canonical_chain_cs (n : ℕ) (x : ℕ → ℝ) (hx : x n = 0) :
    (edgePairing n (spinEdge n) x)^2 ≤ spinS n * chainObjective n x :=
  chain_cs n (spinEdge n) (canonicalA n) (canonicalR n) x hx (canonicalR_bounds n)
    (fun i _ => canonicalA_nonneg n i) (canonical_coefficient n)

theorem canonical_ratio_eq (n i : ℕ) (hi : i < n) :
    spinEdge n i / canonicalA n i = 1-canonicalR n i+canonicalR n (i+1) := by
  apply (div_eq_iff (canonicalA_pos hi).ne').mpr
  rw [mul_comm]
  exact (canonical_coefficient n i hi).symm

theorem canonical_ratio_support (n : ℕ) (x : ℕ → ℝ) (hx : x n = 0) :
    (∑ i ∈ range n, (spinEdge n i / canonicalA n i) * (x i)^2) ≤ chainObjective n x := by
  have he : (∑ i ∈ range n, (spinEdge n i / canonicalA n i) * (x i)^2) =
      ∑ i ∈ range n, (1-canonicalR n i+canonicalR n (i+1)) * (x i)^2 := by
    apply sum_congr rfl
    intro i hi
    rw [canonical_ratio_eq n i (mem_range.mp hi)]
  rw [he]
  exact chain_support n (canonicalR n) x hx (canonicalR_bounds n)

theorem canonical_ratio_cs (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    (edgePairing n (spinEdge n) x)^2 / spinS n ≤
      ∑ i ∈ range n, (spinEdge n i / canonicalA n i) * (x i)^2 := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (range n)
    (fun i (_ : i ∈ range n) => mul_nonneg (spinEdge_nonneg n i) (canonicalA_nonneg n i))
    (fun i (hi : i ∈ range n) => mul_nonneg
      (div_nonneg (spinEdge_nonneg n i) (canonicalA_nonneg n i)) (sq_nonneg (x i)))
    (r := fun i => spinEdge n i * x i) (fun i hi => by
      have ha := (canonicalA_pos (mem_range.mp hi)).ne'
      apply le_of_eq
      field_simp)
  apply (div_le_iff₀ (spinS_pos hn)).mpr
  simpa only [edgePairing, spinS, capSum, mul_comm] using hcs

end FiniteCopy.NHOptimization

