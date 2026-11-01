import Mathlib

open scoped BigOperators

noncomputable section

namespace FiniteCopy.Algebra

/-- 有 n 条边、n+1 个顶点的有限链；只读取 0,...,n 的向量值。 -/
def mass (n : ℕ) (v : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (n + 1), v i ^ 2

def moment (n : ℕ) (c v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, c i * v i * v (i + 1)

/-- 对角能量按边的两个端点展开，自动覆盖两端点。 -/
def diagonalEnergy (n : ℕ) (a r v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (r (i + 1) * a i ^ 2 * v i ^ 2 + (1 - r i) * a i ^ 2 * v (i + 1) ^ 2)

/-- 包含缺失端边的零系数项，n=0 也成立。 -/
def sos (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ) : ℝ :=
  r 0 * (t * v 0) ^ 2 + (1 - r n) * (t * v n) ^ 2 +
    ∑ i ∈ Finset.range n,
      ((1 - r i) * (t * v i - a i * v (i + 1)) ^ 2 +
      r (i + 1) * (t * v (i + 1) - a i * v i) ^ 2)

theorem chain_sos_identity (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ) :
    sos n a r v t = diagonalEnergy n a r v + t ^ 2 * mass n v -
      2 * t * moment n (fun i ↦ a i * (1 - r i + r (i + 1))) v := by
  induction n with
  | zero => simp [sos, diagonalEnergy, mass, moment]; ring
  | succ n ih =>
    simp only [sos, diagonalEnergy, mass, moment, Finset.sum_range_succ] at ih ⊢
    nlinarith [ih]

theorem sos_nonneg (n : ℕ) (a r v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1) : 0 ≤ sos n a r v t := by
  unfold sos
  apply add_nonneg
  · exact add_nonneg (mul_nonneg (hr 0 (Nat.zero_le n)).1 (sq_nonneg _))
      (mul_nonneg (sub_nonneg.mpr (hr n le_rfl).2) (sq_nonneg _))
  · apply Finset.sum_nonneg
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr (hr i (by omega)).2) (sq_nonneg _))
      (mul_nonneg (hr (i + 1) (by omega)).1 (sq_nonneg _))

theorem chain_sos_certificate (n : ℕ) (a r c v : ℕ → ℝ) (t : ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i) :
    0 ≤ diagonalEnergy n a r v + t ^ 2 * mass n v - 2 * t * moment n c v := by
  have hm : moment n (fun i ↦ a i * (1 - r i + r (i + 1))) v = moment n c v := by
    unfold moment
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only; rw [hc i (Finset.mem_range.mp hi)]
  rw [← hm, ← chain_sos_identity]
  exact sos_nonneg n a r v t hr

/-- 非零种子的单项商上界。 -/
theorem seed_sos_bound (n : ℕ) (a r c v : ℕ → ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i)
    (hv : 0 < mass n v) :
    moment n c v ^ 2 / mass n v ≤ diagonalEnergy n a r v := by
  have h := chain_sos_certificate n a r c v (moment n c v / mass n v) hr hc
  have hn : mass n v ≠ 0 := ne_of_gt hv
  have he : (moment n c v / mass n v) ^ 2 * mass n v -
      2 * (moment n c v / mass n v) * moment n c v =
      -(moment n c v ^ 2 / mass n v) := by field_simp; ring
  linarith




/-- 平方完成给出的切线不等式。 -/
theorem tangent_lower (h s q : ℝ) (hs : 0 < s) :
    2 * q * h - q ^ 2 * s ≤ h ^ 2 / s := by
  apply (le_div_iff₀ hs).2
  nlinarith [sq_nonneg (h - q * s)]

theorem tangent_upper (A h s q : ℝ) (hs : 0 < s) :
    A - h ^ 2 / s ≤ A + q ^ 2 * s - 2 * q * h := by
  linarith [tangent_lower h s q hs]

/-- 首顶点的左邻边系数为零。 -/
def previous (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => c i

def midpoint (c : ℕ → ℝ) (i : ℕ) : ℝ := (previous c i + c i) / 2

def gradient (n : ℕ) (c v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, c i * (v (i + 1) - v i) ^ 2

def lambda (a r : ℕ → ℝ) (i : ℕ) : ℝ :=
  previous (fun k ↦ (1 - r k) * a k ^ 2) i + r (i + 1) * a i ^ 2

theorem diagonalEnergy_eq (n : ℕ) (a r v : ℕ → ℝ) (ha : a n = 0) :
    diagonalEnergy n a r v = ∑ i ∈ Finset.range (n + 1), lambda a r i * v i ^ 2 := by
  have aux : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), lambda a r i * v i ^ 2) =
        diagonalEnergy n a r v + r (n + 1) * a n ^ 2 * v n ^ 2 := by
    intro k
    induction k with
    | zero => simp [lambda, previous, diagonalEnergy]
    | succ k ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      simp only [diagonalEnergy, Finset.sum_range_succ, lambda, previous] at ih ⊢
      nlinarith [ih]
  rw [aux n, ha]
  ring

theorem neighbor_sum (n : ℕ) (c v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), (previous c i + c i) * v i ^ 2) =
      (∑ i ∈ Finset.range n, c i * (v i ^ 2 + v (i + 1) ^ 2)) + c n * v n ^ 2 := by
  induction n with
  | zero => simp [previous]
  | succ n ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    simp only [previous] at *
    nlinarith [ih]

theorem gradient_identity (n : ℕ) (c v : ℕ → ℝ) (hc : c n = 0) :
    moment n c v = (∑ i ∈ Finset.range (n + 1), midpoint c i * v i ^ 2) -
      gradient n c v / 2 := by
  have h := neighbor_sum n c v
  rw [hc] at h
  have hm : (∑ i ∈ Finset.range (n + 1), midpoint c i * v i ^ 2) =
      (∑ i ∈ Finset.range (n + 1), (previous c i + c i) * v i ^ 2) / 2 := by
    simp only [midpoint, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have he : gradient n c v =
      (∑ i ∈ Finset.range n, c i * (v i ^ 2 + v (i + 1) ^ 2)) - 2 * moment n c v := by
    simp only [gradient, moment, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hm, he]
  linarith

/-- 节点系数的精确平方差恒等式；上游只须提供两个邻边平方。 -/
theorem coefficient_correction (A c p : ℝ) (hA : A = (c ^ 2 + p ^ 2) / 2) :
    A - ((p + c) / 2) ^ 2 = (c - p) ^ 2 / 4 := by
  rw [hA]
  ring

/-- 自旋坐标下的同一恒等式，包含两个极端 m=±j。 -/
theorem spin_coefficient_correction (j m c p : ℝ)
    (hc : c ^ 2 = (j - m) * (j + m + 1))
    (hp : p ^ 2 = (j + m) * (j - m + 1)) :
    j * (j + 1) - m ^ 2 - ((p + c) / 2) ^ 2 = (c - p) ^ 2 / 4 := by
  nlinarith [hc, hp]

/-- U 的逐点被积函数；在积分前分解成三个非负能量。 -/
theorem energy_identity (n : ℕ) (A c v : ℕ → ℝ) (q : ℝ)
    (hc : c n = 0)
    (hA : ∀ i ≤ n, A i = (c i ^ 2 + previous c i ^ 2) / 2) :
    (∑ i ∈ Finset.range (n + 1), (A i + q ^ 2) * v i ^ 2) - 2 * q * moment n c v =
      (∑ i ∈ Finset.range (n + 1), (midpoint c i - q) ^ 2 * v i ^ 2) +
      q * gradient n c v +
      (∑ i ∈ Finset.range (n + 1), (c i - previous c i) ^ 2 / 4 * v i ^ 2) := by
  rw [gradient_identity n c v hc]
  have hp : ∀ i ∈ Finset.range (n + 1),
      (A i + q ^ 2) * v i ^ 2 =
        (midpoint c i - q) ^ 2 * v i ^ 2 +
        2 * q * (midpoint c i * v i ^ 2) +
        (c i - previous c i) ^ 2 / 4 * v i ^ 2 := by
    intro i hi
    rw [hA i (by have := Finset.mem_range.mp hi; omega)]
    unfold midpoint
    ring
  simp_rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- 完备性固定所有对角二次型的总和。 -/
theorem complete_quadratic_sum {α : Type*} (seeds : Finset α) (n : ℕ)
    (A : ℕ → ℝ) (v : α → ℕ → ℝ)
    (hv : ∀ i ≤ n, ∑ a ∈ seeds, v a i ^ 2 = 1) :
    (∑ a ∈ seeds, ∑ i ∈ Finset.range (n + 1), A i * v a i ^ 2) =
      ∑ i ∈ Finset.range (n + 1), A i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum, hv i (by have := Finset.mem_range.mp hi; omega), mul_one]

/-- 完备有限种子的质量之和正好等于维数。 -/
theorem complete_mass_sum {α : Type*} (seeds : Finset α) (n : ℕ)
    (v : α → ℕ → ℝ)
    (hv : ∀ i ≤ n, ∑ a ∈ seeds, v a i ^ 2 = 1) :
    (∑ a ∈ seeds, mass n (v a)) = (n + 1 : ℕ) := by
  have h := complete_quadratic_sum seeds n (fun _ ↦ 1) v hv
  simpa [mass] using h

/-- 任意完整有限种子族的 SOS 上界。 -/
theorem complete_seed_sos_bound {α : Type*} (seeds : Finset α) (n : ℕ)
    (a r c : ℕ → ℝ) (v : α → ℕ → ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    (∑ k ∈ seeds, moment n c (v k) ^ 2 / mass n (v k)) ≤
      ∑ i ∈ Finset.range n, c i * a i := by
  calc
    _ ≤ ∑ k ∈ seeds, diagonalEnergy n a r (v k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact seed_sos_bound n a r c (v k) hr hc (hm k hk)
    _ = ∑ i ∈ Finset.range n, c i * a i := by
      simp only [diagonalEnergy]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hv i (by omega), hv (i + 1) (by omega), ← hc i hin]
      ring

/-- Fisher trace 和共同方差的有限种子代数；物理识别由 POVM 模块提供。 -/
def fisher {α : Type*} (seeds : Finset α) (n : ℕ)
    (c : ℕ → ℝ) (v : α → ℕ → ℝ) : ℝ :=
  4 / (n + 1 : ℕ) * ∑ k ∈ seeds, moment n c (v k) ^ 2 / mass n (v k)

def variance {α : Type*} (seeds : Finset α) (n : ℕ)
    (A c : ℕ → ℝ) (v : α → ℕ → ℝ) : ℝ :=
  (∑ k ∈ seeds, ((∑ i ∈ Finset.range (n + 1), A i * v k i ^ 2) -
    moment n c (v k) ^ 2 / mass n (v k))) / (n + 1 : ℕ)

theorem fisher_variance_identity {α : Type*} (seeds : Finset α) (n : ℕ)
    (A c : ℕ → ℝ) (v : α → ℕ → ℝ)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1) :
    fisher seeds n c v =
      4 / (n + 1 : ℕ) * (∑ i ∈ Finset.range (n + 1), A i) -
      4 * variance seeds n A c v := by
  unfold fisher variance
  rw [Finset.sum_sub_distrib, complete_quadratic_sum seeds n A v hv]
  ring

theorem complete_fisher_bound {α : Type*} (seeds : Finset α) (n : ℕ)
    (a r c : ℕ → ℝ) (v : α → ℕ → ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    fisher seeds n c v ≤ 4 / (n + 1 : ℕ) * ∑ i ∈ Finset.range n, c i * a i := by
  unfold fisher
  exact mul_le_mul_of_nonneg_left (complete_seed_sos_bound seeds n a r c v hr hc hv hm)
    (by positivity)



/-- 论文的自旋边系数，j=n/2，m=i-n/2。 -/
def spinEdge (n i : ℕ) : ℝ := Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) - i))

def spinA (n i : ℕ) : ℝ :=
  ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) - ((i : ℝ) - (n : ℝ) / 2) ^ 2

theorem spinEdge_last (n : ℕ) : spinEdge n n = 0 := by simp [spinEdge]

theorem spinEdge_nonneg (n i : ℕ) : 0 ≤ spinEdge n i := Real.sqrt_nonneg _

theorem spinEdge_sq (n i : ℕ) (hi : i ≤ n) :
    spinEdge n i ^ 2 = ((i : ℝ) + 1) * ((n : ℝ) - i) := by
  unfold spinEdge
  apply Real.sq_sqrt
  have hn : (i : ℝ) ≤ n := by exact_mod_cast hi
  positivity

theorem spinA_neighbors (n i : ℕ) (hi : i ≤ n) :
    spinA n i = (spinEdge n i ^ 2 + previous (spinEdge n) i ^ 2) / 2 := by
  rw [spinEdge_sq n i hi]
  cases i with
  | zero => simp [spinA, previous]; ring
  | succ i =>
    simp only [previous]
    rw [spinEdge_sq n i (by omega)]
    simp only [spinA, Nat.cast_add, Nat.cast_one]
    ring

theorem spinA_correction (n i : ℕ) (hi : i ≤ n) :
    spinA n i - midpoint (spinEdge n) i ^ 2 =
      (spinEdge n i - previous (spinEdge n) i) ^ 2 / 4 := by
  exact coefficient_correction _ _ _ (spinA_neighbors n i hi)

theorem sum_real_indices (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_real_indices_sq (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 精确维数因子：sum A=(2/3)j(j+1)d。 -/
theorem spinA_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), spinA n i) =
      (2 / 3 : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) * ((n : ℝ) + 1) := by
  have hp : ∀ i, spinA n i = (n : ℝ) / 2 + (n : ℝ) * i - (i : ℝ) ^ 2 := by
    intro i
    unfold spinA
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_real_indices n, sum_real_indices_sq n]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem spin_energy_identity (n : ℕ) (v : ℕ → ℝ) (q : ℝ) :
    (∑ i ∈ Finset.range (n + 1), (spinA n i + q ^ 2) * v i ^ 2) -
      2 * q * moment n (spinEdge n) v =
      (∑ i ∈ Finset.range (n + 1), (midpoint (spinEdge n) i - q) ^ 2 * v i ^ 2) +
      q * gradient n (spinEdge n) v +
      (∑ i ∈ Finset.range (n + 1),
        (spinEdge n i - previous (spinEdge n) i) ^ 2 / 4 * v i ^ 2) := by
  exact energy_identity n (spinA n) (spinEdge n) v q (spinEdge_last n) (spinA_neighbors n)

theorem gradient_nonneg (n : ℕ) (c v : ℕ → ℝ)
    (hc : ∀ i < n, 0 ≤ c i) : 0 ≤ gradient n c v := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hc i (Finset.mem_range.mp hi)) (sq_nonneg _)

theorem energy_nonneg (n : ℕ) (A c v : ℕ → ℝ) (q : ℝ)
    (hcn : c n = 0) (hc : ∀ i < n, 0 ≤ c i) (hq : 0 ≤ q)
    (hA : ∀ i ≤ n, A i = (c i ^ 2 + previous c i ^ 2) / 2) :
    0 ≤ (∑ i ∈ Finset.range (n + 1), (A i + q ^ 2) * v i ^ 2) -
      2 * q * moment n c v := by
  rw [energy_identity n A c v q hcn hA]
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact mul_nonneg hq (gradient_nonneg n c v hc)
  · apply Finset.sum_nonneg
    intro i hi
    positivity

theorem seed_variance_upper_energy (n : ℕ) (A c v : ℕ → ℝ) (q : ℝ)
    (hm : 0 < mass n v) (hc : c n = 0)
    (hA : ∀ i ≤ n, A i = (c i ^ 2 + previous c i ^ 2) / 2) :
    (∑ i ∈ Finset.range (n + 1), A i * v i ^ 2) - moment n c v ^ 2 / mass n v ≤
      (∑ i ∈ Finset.range (n + 1), (midpoint c i - q) ^ 2 * v i ^ 2) +
      q * gradient n c v +
      (∑ i ∈ Finset.range (n + 1), (c i - previous c i) ^ 2 / 4 * v i ^ 2) := by
  rw [← energy_identity n A c v q hc hA]
  have he : (∑ i ∈ Finset.range (n + 1), (A i + q ^ 2) * v i ^ 2) =
      (∑ i ∈ Finset.range (n + 1), A i * v i ^ 2) + q ^ 2 * mass n v := by
    simp only [add_mul, Finset.sum_add_distrib, mass, Finset.mul_sum]
  rw [he]
  exact tangent_upper _ _ _ _ hm

/-- 用真实自旋系数完成论文的T=(8/3)j(j+1)-4V恒等式。 -/
theorem spin_fisher_variance_identity {α : Type*} (seeds : Finset α) (n : ℕ)
    (v : α → ℕ → ℝ)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1) :
    fisher seeds n (spinEdge n) v =
      (8 / 3 : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2 + 1) -
      4 * variance seeds n (spinA n) (spinEdge n) v := by
  rw [fisher_variance_identity seeds n (spinA n) (spinEdge n) v hv, spinA_sum]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring



/-- 截顶方程直接给出 SOS 权重，不使用 c/a 的额外除零条件。 -/
def capA (c : ℕ → ℝ) (τ : ℝ) (i : ℕ) : ℝ := min (c i) τ

def capR (c : ℕ → ℝ) (τ : ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range k, max (c i - τ) 0) / τ

theorem capR_zero (c : ℕ → ℝ) (τ : ℝ) : capR c τ 0 = 0 := by simp [capR]

theorem capR_last (n : ℕ) (c : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hcap : (∑ i ∈ Finset.range n, max (c i - τ) 0) = τ) : capR c τ n = 1 := by
  simp [capR, hcap, ne_of_gt hτ]

theorem capR_bounds (n : ℕ) (c : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hcap : (∑ i ∈ Finset.range n, max (c i - τ) 0) = τ) :
    ∀ k ≤ n, 0 ≤ capR c τ k ∧ capR c τ k ≤ 1 := by
  intro k hk
  constructor
  · unfold capR
    exact div_nonneg (Finset.sum_nonneg (fun i _ ↦ le_max_right _ _)) (le_of_lt hτ)
  · unfold capR
    apply (div_le_one hτ).2
    calc
      _ ≤ ∑ i ∈ Finset.range n, max (c i - τ) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          (fun i _ _ ↦ le_max_right (c i - τ) 0)
      _ = τ := hcap

theorem capR_succ (c : ℕ → ℝ) (τ : ℝ) (i : ℕ) :
    capR c τ (i + 1) = capR c τ i + max (c i - τ) 0 / τ := by
  simp only [capR, Finset.sum_range_succ, add_div]

theorem cap_coefficient (c : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ) (i : ℕ) :
    capA c τ i * (1 - capR c τ i + capR c τ (i + 1)) = c i := by
  rw [capR_succ]
  unfold capA
  by_cases hi : c i ≤ τ
  · rw [min_eq_left hi, max_eq_right (sub_nonpos.mpr hi)]
    simp
  · have hi' : τ ≤ c i := le_of_not_ge hi
    rw [min_eq_right hi', max_eq_left (sub_nonneg.mpr hi')]
    field_simp
    ring

/-- 从截顶方程到完整有限种子 Fisher 上界的端到端有限代数。 -/
theorem capped_complete_fisher_bound {α : Type*} (seeds : Finset α) (n : ℕ)
    (c : ℕ → ℝ) (τ : ℝ) (v : α → ℕ → ℝ) (hτ : 0 < τ)
    (hcap : (∑ i ∈ Finset.range n, max (c i - τ) 0) = τ)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    fisher seeds n c v ≤ 4 / (n + 1 : ℕ) *
      ∑ i ∈ Finset.range n, c i * min (c i) τ := by
  exact complete_fisher_bound seeds n (capA c τ) (capR c τ) c v
    (capR_bounds n c τ hτ hcap) (fun i _ ↦ cap_coefficient c τ hτ i) hv hm

theorem lambda_sum (n : ℕ) (a r c : ℕ → ℝ) (ha : a n = 0)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i) :
    (∑ i ∈ Finset.range (n + 1), lambda a r i) =
      ∑ i ∈ Finset.range n, c i * a i := by
  have hd := diagonalEnergy_eq n a r (fun _ ↦ 1) ha
  simp only [one_pow, mul_one] at hd
  rw [← hd]
  unfold diagonalEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hc i (Finset.mem_range.mp hi)]
  ring

theorem complete_variance_lower_bound {α : Type*} (seeds : Finset α) (n : ℕ)
    (A a r c : ℕ → ℝ) (v : α → ℕ → ℝ)
    (hr : ∀ i ≤ n, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i < n, a i * (1 - r i + r (i + 1)) = c i)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    ((∑ i ∈ Finset.range (n + 1), A i) -
      (∑ i ∈ Finset.range n, c i * a i)) / (n + 1 : ℕ) ≤ variance seeds n A c v := by
  unfold variance
  rw [Finset.sum_sub_distrib, complete_quadratic_sum seeds n A v hv]
  exact div_le_div_of_nonneg_right
    (sub_le_sub_left (complete_seed_sos_bound seeds n a r c v hr hc hv hm) _)
    (by positivity)

/-- 对角自旋能量总和等于全部边系数平方和。 -/
theorem spinA_sum_eq_edge_sq (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), spinA n i) = ∑ i ∈ Finset.range n, spinEdge n i ^ 2 := by
  have hn := neighbor_sum n (fun i ↦ spinEdge n i ^ 2) (fun _ ↦ 1)
  have hp : ∀ i, previous (fun i ↦ spinEdge n i ^ 2) i = previous (spinEdge n) i ^ 2 := by
    intro i
    cases i <;> simp [previous]
  simp only [one_pow, mul_one, spinEdge_last, zero_pow (by decide : 2 ≠ 0),
    add_zero] at hn
  simp_rw [hp] at hn
  have hs : (∑ i ∈ Finset.range (n + 1), spinA n i) =
      (∑ i ∈ Finset.range (n + 1),
        (previous (spinEdge n) i ^ 2 + spinEdge n i ^ 2)) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [spinA_neighbors n i (by have := Finset.mem_range.mp hi; omega)]
    ring
  rw [hs, hn]
  simp only [← Finset.sum_mul]
  ring

/-- 原稿 D/d 下界，输入为真实自旋系数及正截顶根。 -/
theorem capped_spin_variance_lower_bound {α : Type*} (seeds : Finset α) (n : ℕ)
    (τ : ℝ) (v : α → ℕ → ℝ) (hτ : 0 < τ)
    (hcap : (∑ i ∈ Finset.range n, max (spinEdge n i - τ) 0) = τ)
    (hv : ∀ i ≤ n, ∑ k ∈ seeds, v k i ^ 2 = 1)
    (hm : ∀ k ∈ seeds, 0 < mass n (v k)) :
    ((∑ i ∈ Finset.range n, spinEdge n i ^ 2) -
      (∑ i ∈ Finset.range n, spinEdge n i * min (spinEdge n i) τ)) / (n + 1 : ℕ) ≤
      variance seeds n (spinA n) (spinEdge n) v := by
  rw [← spinA_sum_eq_edge_sq]
  exact complete_variance_lower_bound seeds n (spinA n) (capA (spinEdge n) τ)
    (capR (spinEdge n) τ) (spinEdge n) v
    (capR_bounds n (spinEdge n) τ hτ hcap)
    (fun i _ ↦ cap_coefficient (spinEdge n) τ hτ i) hv hm



/-- 非零种子自动具有正质量。 -/
theorem mass_pos_of_component (n : ℕ) (v : ℕ → ℝ) (i : ℕ)
    (hi : i ≤ n) (hvi : v i ≠ 0) : 0 < mass n v := by
  have hs : v i ^ 2 ≤ mass n v :=
    Finset.single_le_sum (fun k _ ↦ sq_nonneg (v k)) (Finset.mem_range.mpr (by omega))
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hvi) hs

theorem spinEdge_physical (n i : ℕ) :
    spinEdge n i = Real.sqrt
      (((n : ℝ) / 2 - ((i : ℝ) - (n : ℝ) / 2)) *
        ((n : ℝ) / 2 + ((i : ℝ) - (n : ℝ) / 2) + 1)) := by
  unfold spinEdge
  congr 1
  ring

theorem spinEdge_circle (n i : ℕ) (hi : i ≤ n) :
    spinEdge n i ^ 2 = (((n : ℝ) + 1) / 2) ^ 2 -
      ((i : ℝ) - (n : ℝ) / 2 + 1 / 2) ^ 2 := by
  rw [spinEdge_sq n i hi]
  ring

theorem spin_zero_fisher_variance {α : Type*} (seeds : Finset α) (v : α → ℕ → ℝ) :
    fisher seeds 0 (spinEdge 0) v = 0 ∧ variance seeds 0 (spinA 0) (spinEdge 0) v = 0 := by
  simp [fisher, variance, moment, spinA]

end FiniteCopy.Algebra
