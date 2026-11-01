import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter Asymptotics Finset

namespace FiniteCopy.Schur

def binom (N k : ℕ) : ℝ := (N.choose k : ℝ)

/-- k=0 对应最大自旋 j=N/2；k 的取值为 0,…,⌊N/2⌋。 -/
noncomputable def weight (N k : ℕ) : ℝ :=
  ((N : ℝ) + 1 - 2 * k) *
    (binom N k - if k = 0 then 0 else binom N (k - 1)) / 2 ^ N

noncomputable def spin (N k : ℕ) : ℝ := (N : ℝ) / 2 - k

theorem sum_parts (a q : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m + 1), a k * (q k - if k = 0 then 0 else q (k - 1))) =
    a m * q m + ∑ k ∈ range m, (a k - a (k + 1)) * q k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    ring

theorem weight_nonneg {N k : ℕ} (hk : k ≤ N / 2) : 0 ≤ weight N k := by
  unfold weight
  apply div_nonneg
  · apply mul_nonneg
    · have : 2 * k ≤ N := (Nat.mul_div_le N 2).trans' (Nat.mul_le_mul_left 2 hk)
      have : (2 : ℝ) * k ≤ N := by exact_mod_cast this
      linarith
    · by_cases h : k = 0
      · simp [h, binom]
      · have hlt : k - 1 < N / 2 := by omega
        have hchoose := Nat.choose_le_succ_of_lt_half_left hlt
        have hsucc : k - 1 + 1 = k := by omega
        rw [hsucc] at hchoose
        simp only [h, ↓reduceIte]
        exact sub_nonneg.mpr (by unfold binom; exact_mod_cast hchoose)
  · positivity

theorem half_sum_odd (m : ℕ) :
    (∑ k ∈ range (m + 1), binom (2 * m + 1) k) = (4 : ℝ) ^ m := by
  unfold binom
  exact_mod_cast Nat.sum_range_choose_halfway m

theorem half_sum_even (m : ℕ) :
    2 * (∑ k ∈ range m, binom (2 * m) k) + binom (2 * m) m = (4 : ℝ) ^ m := by
  have h := half_sum_odd m
  have hPascal : (∑ k ∈ range (m + 1), binom (2 * m + 1) k) =
      2 * (∑ k ∈ range m, binom (2 * m) k) + binom (2 * m) m := by
    rw [sum_range_succ']
    simp only [binom, Nat.choose_succ_succ, Nat.cast_add, sum_add_distrib,
      Nat.choose_zero_right, Nat.cast_one]
    have hshift := sum_range_succ' (fun k => ((2 * m).choose k : ℝ)) m
    have hend := sum_range_succ (fun k => ((2 * m).choose k : ℝ)) m
    simp only [Nat.choose_zero_right, Nat.cast_one] at hshift
    linarith
  rwa [hPascal] at h

theorem weight_sum_truncated (N m : ℕ) :
    (∑ k ∈ range (m + 1), weight N k) =
    (((N : ℝ) + 1 - 2 * m) * binom N m +
      2 * (∑ k ∈ range m, binom N k)) / 2 ^ N := by
  simp only [weight, ← sum_div]
  rw [sum_parts]
  congr 1
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro k _
  push_cast
  ring

theorem weight_sum_even (m : ℕ) :
    (∑ k ∈ range (m + 1), weight (2 * m) k) = 1 := by
  rw [weight_sum_truncated]
  have h := half_sum_even m
  have hp : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  push_cast
  rw [hp]
  have he : ((2 : ℝ) * m + 1 - 2 * m) = 1 := by ring
  rw [he, one_mul, add_comm, h]
  exact div_self (by positivity)

theorem weight_sum_odd (m : ℕ) :
    (∑ k ∈ range (m + 1), weight (2 * m + 1) k) = 1 := by
  rw [weight_sum_truncated]
  have h := half_sum_odd m
  rw [sum_range_succ] at h
  have hp : (2 : ℝ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num; ring
  push_cast
  rw [hp]
  apply (div_eq_one_iff_eq (by positivity)).mpr
  nlinarith

theorem weight_sum (N : ℕ) :
    (∑ k ∈ range (N / 2 + 1), weight N k) = 1 := by
  rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hN : N = 2 * m := by omega
    rw [hN, show 2 * m / 2 = m by omega]
    exact weight_sum_even m
  · have hN : N = 2 * m + 1 := by omega
    rw [hN, show (2 * m + 1) / 2 = m by omega]
    exact weight_sum_odd m

theorem choose_balance {N k : ℕ} (hk : k ≤ N) :
    ((N : ℝ) - k) * binom N k = (k + 1) * binom N (k + 1) := by
  have h := Nat.choose_succ_right_eq N k
  have h' : binom N (k + 1) * ((k : ℝ) + 1) =
      binom N k * ((N : ℝ) - k) := by
    unfold binom
    exact_mod_cast h
  linarith

theorem signed_sum (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ range (m + 1), ((N : ℝ) - 2 * k) * binom N k) =
    (m + 1) * binom N (m + 1) := by
  induction m with
  | zero => simp [binom]
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    have h := choose_balance hm
    push_cast at h ⊢
    nlinarith

theorem signed_square_sum (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ range (m + 1), ((N : ℝ) - 2 * k)^2 * binom N k) =
    N * (∑ k ∈ range (m + 1), binom N k) +
      (N - 2 * m - 1) * (m + 1) * binom N (m + 1) := by
  induction m with
  | zero =>
    have h := choose_balance (N := N) (k := 0) (by omega)
    simp only [sum_range_one, Nat.cast_zero, mul_zero, sub_zero, zero_add, one_mul] at h ⊢
    nlinarith
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    simp only [sum_range_succ]
    have h := choose_balance hm
    have hmul := congrArg (fun x : ℝ => ((N : ℝ) - 2 * m - 3) * x) h
    push_cast at h hmul ⊢
    nlinarith

noncomputable def firstMoment (N : ℕ) : ℝ :=
  ∑ k ∈ range (N / 2 + 1), weight N k * spin N k

noncomputable def casimirMoment (N : ℕ) : ℝ :=
  ∑ k ∈ range (N / 2 + 1), weight N k * (spin N k * (spin N k + 1))

theorem moment_parts (N m : ℕ) (f : ℝ → ℝ) :
    (∑ k ∈ range (m + 1), weight N k * f (spin N k)) =
    (((N : ℝ) + 1 - 2 * m) * f (spin N m) * binom N m +
      ∑ k ∈ range m, (((N : ℝ) + 1 - 2 * k) * f (spin N k) -
        ((N : ℝ) + 1 - 2 * (k + 1)) * f (spin N (k + 1))) * binom N k) / 2 ^ N := by
  have he : ∀ k, weight N k * f (spin N k) =
      (((N : ℝ) + 1 - 2 * k) * f (spin N k)) *
        (binom N k - if k = 0 then 0 else binom N (k - 1)) / 2 ^ N := by
    intro k
    unfold weight
    ring
  simp_rw [he]
  rw [← sum_div, sum_parts]
  push_cast
  rfl

theorem firstMoment_even_formula (m : ℕ) :
    firstMoment (2 * m) = (((2 : ℝ) * m + 1 / 2) * binom (2 * m) m) / 4 ^ m - 1 / 2 := by
  unfold firstMoment
  rw [show 2 * m / 2 = m by omega, moment_parts (2 * m) m (fun x => x)]
  have hb := choose_balance (N := 2 * m) (k := m) (by omega)
  have hs := signed_sum (2 * m) m (by omega)
  have hh := half_sum_even m
  rw [sum_range_succ] at hs
  have he : (∑ k ∈ range m,
      ((((2 * m : ℕ) : ℝ) + 1 - 2 * k) * spin (2 * m) k -
        ((((2 * m : ℕ) : ℝ) + 1 - 2 * (k + 1)) * spin (2 * m) (k + 1))) *
          binom (2 * m) k) =
      2 * (∑ k ∈ range m, (((2 * m : ℕ) : ℝ) - 2 * k) * binom (2 * m) k) -
        ∑ k ∈ range m, binom (2 * m) k := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    simp only [spin, Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  simp only [spin, Nat.cast_mul, Nat.cast_ofNat] at hb hs ⊢
  have hp : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  rw [hp]
  field_simp
  ring_nf at hs hb hh ⊢
  nlinarith

theorem firstMoment_odd_formula (m : ℕ) :
    firstMoment (2 * m + 1) = ((2 : ℝ) * m + 1) * binom (2 * m) m / 4 ^ m - 1 / 2 := by
  unfold firstMoment
  rw [show (2 * m + 1) / 2 = m by omega, moment_parts (2 * m + 1) m (fun x => x)]
  have hs := signed_sum (2 * m + 1) m (by omega)
  have hh := half_sum_odd m
  have hc : ((m : ℝ) + 1) * binom (2 * m + 1) (m + 1) =
      ((2 : ℝ) * m + 1) * binom (2 * m) m := by
    have h := Nat.add_one_mul_choose_eq (2 * m) m
    unfold binom
    rw [mul_comm (m + 1 : ℝ)]
    exact_mod_cast h.symm
  have he : (∑ k ∈ range m,
      ((((2 * m + 1 : ℕ) : ℝ) + 1 - 2 * k) * spin (2 * m + 1) k -
        (((2 * m + 1 : ℕ) : ℝ) + 1 - 2 * (k + 1)) * spin (2 * m + 1) (k + 1)) *
          binom (2 * m + 1) k) =
      2 * (∑ k ∈ range m, (((2 * m + 1 : ℕ) : ℝ) - 2 * k) * binom (2 * m + 1) k) -
        ∑ k ∈ range m, binom (2 * m + 1) k := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    simp only [spin, Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  rw [sum_range_succ] at hs hh
  have hp : (2 : ℝ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num; ring
  simp only [spin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hs ⊢
  rw [hp]
  field_simp
  ring_nf at hs hc hh ⊢
  nlinarith

theorem casimir_parts (N m : ℕ) :
    (∑ k ∈ range (m + 1), weight N k * (spin N k * (spin N k + 1))) =
    (((N : ℝ) + 1 - 2 * m) * (spin N m * (spin N m + 1)) * binom N m +
      (3 / 2) * ∑ k ∈ range m, ((N : ℝ) - 2 * k)^2 * binom N k) / 2 ^ N := by
  rw [moment_parts N m (fun x => x * (x + 1))]
  congr 1
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [spin, Nat.cast_add, Nat.cast_one]
  ring

theorem casimir_even (m : ℕ) : casimirMoment (2 * m) = 3 * (2 * m : ℕ) / 4 := by
  unfold casimirMoment
  rw [show 2 * m / 2 = m by omega, casimir_parts]
  have hs := signed_square_sum (2 * m) m (by omega)
  have hb := choose_balance (N := 2 * m) (k := m) (by omega)
  have hh := half_sum_even m
  have hhm := congrArg (fun x : ℝ => (m : ℝ) * x) hh
  rw [sum_range_succ, sum_range_succ] at hs
  simp only [spin, Nat.cast_mul, Nat.cast_ofNat] at hs hb ⊢
  have hp : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  rw [hp]
  field_simp
  ring_nf at hs hb hh hhm ⊢
  nlinarith

theorem casimir_odd (m : ℕ) : casimirMoment (2 * m + 1) = 3 * (2 * m + 1 : ℕ) / 4 := by
  unfold casimirMoment
  rw [show (2 * m + 1) / 2 = m by omega, casimir_parts]
  have hs := signed_square_sum (2 * m + 1) m (by omega)
  have hh := half_sum_odd m
  rw [sum_range_succ, sum_range_succ] at hs
  rw [sum_range_succ] at hh
  have hhm := congrArg (fun x : ℝ => ((2 : ℝ) * m + 1) * x) hh
  simp only [spin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hs ⊢
  have hp : (2 : ℝ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [hp]
  field_simp
  ring_nf at hs hh hhm ⊢
  nlinarith

theorem casimirMoment_eq (N : ℕ) : casimirMoment N = 3 * N / 4 := by
  rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hN : N = 2 * m := by omega
    rw [hN]
    exact casimir_even m
  · have hN : N = 2 * m + 1 := by omega
    rw [hN]
    exact casimir_odd m

noncomputable def average (s : ℕ → Finset ℕ) (p : ℕ → ℕ → ℝ)
    (f : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ s N, p N i * f i

/-- 有限个小自旋可吸收到一个固定常数。 -/
theorem littleO_global_bound {r : ℕ → ℝ}
    (hr : r =o[atTop] (fun i : ℕ => (i : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, |r i| ≤ ε * i + M := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hr.bound hε)
  refine ⟨∑ i ∈ range K, |r i|, sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro i
  by_cases hi : K ≤ i
  · have h := hK i hi
    simp only [Real.norm_eq_abs, Nat.abs_cast] at h
    exact h.trans (le_add_of_nonneg_right (sum_nonneg (fun _ _ => abs_nonneg _)))
  · have hi' : i ∈ range K := mem_range.mpr (lt_of_not_ge hi)
    have h := single_le_sum (fun k (_ : k ∈ range K) => abs_nonneg (r k)) hi'
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg _)))

/-- 正规化非负有限权重的固定序列平均：一阶矩的 O(a_N) 界即可。 -/
theorem weighted_littleO {s : ℕ → Finset ℕ} {p : ℕ → ℕ → ℝ}
    {r a : ℕ → ℝ} {A : ℝ}
    (hp : ∀ N i, i ∈ s N → 0 ≤ p N i)
    (hnorm : ∀ N, ∑ i ∈ s N, p N i = 1)
    (ha : Tendsto a atTop atTop) (hA : 0 < A)
    (hmean : ∀ᶠ N in atTop, average s p (fun i => (i : ℝ)) N ≤ A * a N)
    (hr : r =o[atTop] (fun i : ℕ => (i : ℝ))) :
    average s p r =o[atTop] a := by
  apply IsLittleO.of_bound
  intro c hc
  have he : 0 < c / (2 * A) := div_pos hc (by positivity)
  obtain ⟨M, hM, hbound⟩ := littleO_global_bound hr he
  have hconst : (fun _ : ℕ => M) =o[atTop] a := by
    apply isLittleO_const_left.mpr
    right
    exact tendsto_norm_atTop_atTop.comp ha
  filter_upwards [hmean, hconst.bound (show 0 < c / 2 by positivity),
      ha.eventually (eventually_ge_atTop (0 : ℝ))] with N hm hconstN haN
  simp only [Real.norm_eq_abs, abs_of_nonneg haN, abs_of_nonneg hM] at hconstN ⊢
  calc
    |average s p r N| ≤ ∑ i ∈ s N, p N i * |r i| := by
      unfold average
      exact (abs_sum_le_sum_abs _ _).trans_eq
        (sum_congr rfl (fun i hi => by rw [abs_mul, abs_of_nonneg (hp N i hi)]))
    _ ≤ ∑ i ∈ s N, p N i * (c / (2 * A) * i + M) :=
      sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbound i) (hp N i hi))
    _ = c / (2 * A) * average s p (fun i => (i : ℝ)) N + M := by
      simp only [mul_add, sum_add_distrib, average]
      rw [← sum_mul, hnorm, one_mul, mul_sum]
      congr 1
      exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ c / (2 * A) * (A * a N) + c / 2 * a N :=
      add_le_add (mul_le_mul_of_nonneg_left hm he.le) hconstN
    _ = c * a N := by field_simp; ring

theorem sqrt_nat_tendsto : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- 已平均的方差一阶渐近给出风险首项；没有假定 Schur 均值结论。 -/
theorem risk_scaled_limit {Z : ℕ → ℝ} {a : ℝ}
    (hZ : Tendsto (fun N => Z N / Real.sqrt N) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => Real.sqrt N *
      (4 * N / (2 * N - 4 * Z N) - 2)) atTop (𝓝 (4 * a)) := by
  have hinv : Tendsto (fun N : ℕ => 1 / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop sqrt_nat_tendsto
  have hZN : Tendsto (fun N : ℕ => Z N / N) atTop (𝓝 0) := by
    convert hZ.mul hinv using 1
    · ext N
      rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    · ring
  have hden : Tendsto (fun N : ℕ => 1 - 2 * (Z N / N)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub (hZN.const_mul 2) using 1 <;> norm_num
  have hden0 : ∀ᶠ N : ℕ in atTop, 1 - 2 * (Z N / N) ≠ 0 :=
    hden.eventually_ne (by norm_num)
  have hres := (hZ.const_mul 4).div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hres
  apply hres.congr'
  filter_upwards [hden0, eventually_ge_atTop 1] with N hd hN
  change (4 * (Z N / Real.sqrt N)) / (1 - 2 * (Z N / N)) =
    Real.sqrt N * (4 * N / (2 * N - 4 * Z N) - 2)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs2 : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hd' : 2 * (N : ℝ) - 4 * Z N ≠ 0 := by
    intro h
    apply hd
    field_simp
    linarith
  have hd'' : (N : ℝ) - Z N * 2 ≠ 0 := by
    intro h
    apply hd
    field_simp
    linarith
  field_simp [hn, hs, hd', hd'']
  rw [hs2]
  ring

noncomputable def centralRatio (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

theorem centralRatio_nonneg (n : ℕ) : 0 ≤ centralRatio n := by
  unfold centralRatio
  positivity

theorem wallis_central_identity (n : ℕ) :
    Real.Wallis.W n * (centralRatio n)^2 * (2 * n + 1) = 1 := by
  have hf : (Nat.centralBinom n : ℝ) * (n.factorial : ℝ)^2 =
      ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have hn : 2 * n - n = n := by omega
    rw [hn] at h
    norm_cast
    simpa [Nat.centralBinom, pow_two, mul_assoc] using h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hc : (Nat.centralBinom n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  have hp : (2 : ℝ) ^ (4 * n) = (4 ^ n)^2 := by
    rw [show 4 * n = 2 * (2 * n) by omega, pow_mul, pow_mul]
    norm_num
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [Real.Wallis.W_eq_factorial_ratio, ← hf, centralRatio, hp]
  field_simp

/-- 从 mathlib 的 Wallis 极限推出中央二项式渐近，无额外极限假设。 -/
theorem centralRatio_sqrt_limit :
    Tendsto (fun n : ℕ => centralRatio n * Real.sqrt n)
      atTop (𝓝 (Real.sqrt (1 / Real.pi))) := by
  have hquot : Tendsto (fun n : ℕ => ((n : ℝ) / (2 * n + 1)) / Real.Wallis.W n)
      atTop (𝓝 (1 / Real.pi)) := by
    convert Stirling.tendsto_self_div_two_mul_self_add_one.div
      Real.Wallis.tendsto_W_nhds_pi_div_two (by positivity : Real.pi / 2 ≠ 0) using 1
    field_simp
  have h := Real.continuous_sqrt.tendsto (1 / Real.pi) |>.comp hquot
  apply h.congr
  intro n
  have hid := wallis_central_identity n
  have hw := Real.Wallis.W_pos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc := centralRatio_nonneg n
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hn]
  field_simp
  nlinarith [hid]

theorem central_affine_limit (b c : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (((2 : ℝ) * n + c) * centralRatio n - 1 / 2) /
      Real.sqrt (2 * n + b)) atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have his : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop sqrt_nat_tendsto
  have hnum : Tendsto (fun n : ℕ =>
      (2 + c * (1 / n)) * (centralRatio n * Real.sqrt n) - (1 / 2) * (1 / Real.sqrt n))
      atTop (𝓝 (2 * Real.sqrt (1 / Real.pi))) := by
    convert ((tendsto_const_nhds.add (hinv.const_mul c)).mul centralRatio_sqrt_limit).sub
      (his.const_mul (1 / 2)) using 1 <;> ring
  have hden : Tendsto (fun n : ℕ => Real.sqrt (2 + b * (1 / n))) atTop (𝓝 (Real.sqrt 2)) := by
    apply Real.continuous_sqrt.tendsto (2 : ℝ) |>.comp
    convert tendsto_const_nhds.add (hinv.const_mul b) using 1 <;> ring
  have h := hnum.div hden (by positivity : Real.sqrt 2 ≠ 0)
  have hconst : 2 * Real.sqrt (1 / Real.pi) / Real.sqrt 2 = Real.sqrt (2 / Real.pi) := by
    rw [show (2 : ℝ) / Real.pi = 2 * (1 / Real.pi) by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
    have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by positivity)
    field_simp
    nlinarith
  rw [hconst] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change ((2 + c * (1 / (n : ℝ))) * (centralRatio n * Real.sqrt n) -
      (1 / 2) * (1 / Real.sqrt n)) / Real.sqrt (2 + b * (1 / (n : ℝ))) =
    (((2 : ℝ) * n + c) * centralRatio n - 1 / 2) / Real.sqrt (2 * n + b)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hs2 : (Real.sqrt n)^2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hroot : Real.sqrt (2 * (n : ℝ) + b) =
      Real.sqrt n * Real.sqrt (2 + b * (1 / n)) := by
    rw [← Real.sqrt_mul hn0.le]
    congr 1
    field_simp
  have hr0 : Real.sqrt (2 + b * (1 / (n : ℝ))) ≠ 0 := by positivity
  rw [hroot]
  field_simp [hs0, hr0, hn0.ne']
  rw [hs2]
  ring

/-- 两个奇偶子序列共同收敛即可恢复全部副本数。 -/
theorem tendsto_even_odd {f : ℕ → ℝ} {a : ℝ}
    (he : Tendsto (fun n => f (2 * n)) atTop (𝓝 a))
    (ho : Tendsto (fun n => f (2 * n + 1)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨Ke, heK⟩ := eventually_atTop.mp (he.eventually hs)
  obtain ⟨Ko, hoK⟩ := eventually_atTop.mp (ho.eventually hs)
  apply eventually_atTop.mpr
  refine ⟨2 * max Ke Ko + 1, ?_⟩
  intro N hN
  rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hNm : N = 2 * m := by omega
    rw [hNm]
    exact heK m (by omega)
  · have hNm : N = 2 * m + 1 := by omega
    rw [hNm]
    exact hoK m (by omega)

/-- 题设实际二项式 Schur 权重的第一矩极限，同时覆盖整数及半整数自旋。 -/
theorem firstMoment_sqrt_limit :
    Tendsto (fun N : ℕ => firstMoment N / Real.sqrt N)
      atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  apply tendsto_even_odd
  · convert central_affine_limit 0 (1 / 2) (by norm_num) using 1
    ext n
    rw [firstMoment_even_formula]
    simp only [centralRatio, Nat.centralBinom, binom, Nat.cast_mul, Nat.cast_ofNat, add_zero]
    ring
  · convert central_affine_limit 1 1 (by norm_num) using 1
    ext n
    rw [firstMoment_odd_formula]
    simp only [centralRatio, Nat.centralBinom, binom, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    ring

/-- 固定自旋序列以 n=2j 编号；二项式重数仍以 k 编号。 -/
noncomputable def schurAverage (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range (N / 2 + 1), weight N k * f (N - 2 * k)

theorem spinIndex_eq {N k : ℕ} (hk : k ≤ N / 2) :
    ((N - 2 * k : ℕ) : ℝ) = 2 * spin N k := by
  have hle : 2 * k ≤ N := (Nat.mul_div_le N 2).trans' (Nat.mul_le_mul_left 2 hk)
  rw [Nat.cast_sub hle]
  simp only [spin, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem schurAverage_nat (N : ℕ) :
    schurAverage (fun n => (n : ℝ)) N = 2 * firstMoment N := by
  unfold schurAverage firstMoment
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [spinIndex_eq (by simpa using (mem_range.mp hk))]
  ring

theorem schurAverage_casimir (N : ℕ) :
    schurAverage (fun n => ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1)) N = 3 * N / 4 := by
  rw [← casimirMoment_eq N]
  unfold schurAverage casimirMoment
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [spinIndex_eq (by simpa using (mem_range.mp hk))]
  ring

theorem schurAverage_spinSquare (N : ℕ) :
    schurAverage (fun n => ((n : ℝ) / 2)^2) N = 3 * N / 4 - firstMoment N := by
  rw [← casimirMoment_eq N]
  unfold schurAverage casimirMoment firstMoment
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [spinIndex_eq (by simpa using (mem_range.mp hk))]
  ring

/-- 将逐扇区 Fisher 恒等式平均后，二阶矩项严格等于 2N。 -/
theorem schurAverage_fisher (v : ℕ → ℝ) (N : ℕ) :
    schurAverage (fun n => (8 / 3 : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) - 4 * v n) N =
      2 * N - 4 * schurAverage v N := by
  have hlin : schurAverage
      (fun n => (8 / 3 : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) - 4 * v n) N =
      (8 / 3) * schurAverage (fun n => ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1)) N -
        4 * schurAverage v N := by
    unfold schurAverage
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    dsimp only
    ring
  rw [hlin, schurAverage_casimir]
  ring

theorem schurAverage_abs_bound {r : ℕ → ℝ} {ε M : ℝ}
    (hbound : ∀ n, |r n| ≤ ε * n + M) (N : ℕ) :
    |schurAverage r N| ≤ ε * schurAverage (fun n => (n : ℝ)) N + M := by
  have hp : ∀ k ∈ range (N / 2 + 1), 0 ≤ weight N k :=
    fun k hk => weight_nonneg (by simpa using (mem_range.mp hk))
  calc
    |schurAverage r N| ≤ ∑ k ∈ range (N / 2 + 1), weight N k * |r (N - 2 * k)| := by
      unfold schurAverage
      exact (abs_sum_le_sum_abs _ _).trans_eq
        (sum_congr rfl (fun k hk => by rw [abs_mul, abs_of_nonneg (hp k hk)]))
    _ ≤ ∑ k ∈ range (N / 2 + 1), weight N k * (ε * (N - 2 * k : ℕ) + M) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hbound _) (hp k hk))
    _ = ε * schurAverage (fun n => (n : ℝ)) N + M := by
      simp only [mul_add, sum_add_distrib, schurAverage]
      rw [← sum_mul, weight_sum, one_mul, mul_sum]
      congr 1
      exact sum_congr rfl (fun _ _ => by ring)

/-- 实际 Schur 权重的固定逐自旋 little-o 平均，不把第一矩渐近作为假设。 -/
theorem schurAverage_littleO {r : ℕ → ℝ}
    (hr : r =o[atTop] (fun n : ℕ => (n : ℝ))) :
    schurAverage r =o[atTop] (fun N : ℕ => Real.sqrt N) := by
  let A : ℝ := 2 * (Real.sqrt (2 / Real.pi) + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hmean : ∀ᶠ N : ℕ in atTop,
      schurAverage (fun n => (n : ℝ)) N ≤ A * Real.sqrt N := by
    filter_upwards [firstMoment_sqrt_limit.eventually_lt_const
        (show Real.sqrt (2 / Real.pi) < Real.sqrt (2 / Real.pi) + 1 by linarith),
      eventually_ge_atTop 1] with N hN hn
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    have hm := (div_lt_iff₀ hs).mp hN
    rw [schurAverage_nat]
    dsimp [A]
    linarith
  apply IsLittleO.of_bound
  intro c hc
  have he : 0 < c / (2 * A) := div_pos hc (by positivity)
  obtain ⟨M, hM, hbound⟩ := littleO_global_bound hr he
  have hconst : (fun _ : ℕ => M) =o[atTop] (fun N : ℕ => Real.sqrt N) := by
    apply isLittleO_const_left.mpr
    right
    exact tendsto_norm_atTop_atTop.comp sqrt_nat_tendsto
  filter_upwards [hmean, hconst.bound (show 0 < c / 2 by positivity)] with N hm hconstN
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hM] at hconstN ⊢
  calc
    |schurAverage r N| ≤ c / (2 * A) * schurAverage (fun n => (n : ℝ)) N + M :=
      schurAverage_abs_bound hbound N
    _ ≤ c / (2 * A) * (A * Real.sqrt N) + c / 2 * Real.sqrt N :=
      add_le_add (mul_le_mul_of_nonneg_left hm he.le) hconstN
    _ = c * Real.sqrt N := by field_simp; ring

theorem schurAverage_decompose (v : ℕ → ℝ) (α : ℝ) (N : ℕ) :
    schurAverage v N = α * firstMoment N +
      schurAverage (fun n => v n - α * (n : ℝ) / 2) N := by
  unfold schurAverage firstMoment
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [spinIndex_eq (by simpa using (mem_range.mp hk))]
  ring

theorem schurAverage_asymptotic {v : ℕ → ℝ} {α : ℝ}
    (hv : (fun n => v n - α * (n : ℝ) / 2) =o[atTop] (fun n : ℕ => (n : ℝ))) :
    Tendsto (fun N : ℕ => schurAverage v N / Real.sqrt N)
      atTop (𝓝 (α * Real.sqrt (2 / Real.pi))) := by
  have hr := (schurAverage_littleO hv).tendsto_div_nhds_zero
  convert (firstMoment_sqrt_limit.const_mul α).add hr using 1
  · ext N
    rw [schurAverage_decompose v α N]
    ring
  · ring

/-- 组合 Schur 风险的首项：待物理归约识别后即可用于原模型风险。 -/
theorem schurRisk_scaled_limit {v : ℕ → ℝ}
    (hv : (fun n => v n - (n : ℝ) / 4) =o[atTop] (fun n : ℕ => (n : ℝ))) :
    Tendsto (fun N : ℕ => Real.sqrt N *
      (4 * N / (2 * N - 4 * schurAverage v N) - 2))
      atTop (𝓝 (Real.sqrt (8 / Real.pi))) := by
  have hv' : (fun n => v n - (1 / 2 : ℝ) * (n : ℝ) / 2) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by convert hv using 1 <;> ext n <;> ring
  have h := risk_scaled_limit (schurAverage_asymptotic hv')
  have hc : 4 * ((1 / 2 : ℝ) * Real.sqrt (2 / Real.pi)) = Real.sqrt (8 / Real.pi) := by
    rw [show (8 : ℝ) / Real.pi = 4 * (2 / Real.pi) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rwa [hc] at h

/-- 实际二项式平均后的逐扇区 Fisher 表达式所对应的风险首项。 -/
theorem averagedFisher_risk_scaled_limit {v : ℕ → ℝ}
    (hv : (fun n => v n - (n : ℝ) / 4) =o[atTop] (fun n : ℕ => (n : ℝ))) :
    Tendsto (fun N : ℕ => Real.sqrt N *
      (4 * N / schurAverage
        (fun n => (8 / 3 : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) - 4 * v n) N - 2))
      atTop (𝓝 (Real.sqrt (8 / Real.pi))) := by
  simp_rw [schurAverage_fisher]
  exact schurRisk_scaled_limit hv

end FiniteCopy.Schur

