import FiniteCopy.Construction
import FiniteCopy.SpinInterface
import FiniteCopy.GlobalBounds

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace CopyQuantumMetrology.ContinuousEnergy

open FiniteCopy.Algebra GlobalBounds NHLowerBound

/-- 实际有限自旋高斯列的自然数零延拓，便于直接调用链式 SOS。 -/
def spinV (n : ℕ) (eps t : ℝ) (i : ℕ) : ℝ :=
  if h : i < n + 1 then spinColumn n eps t ⟨i, h⟩ else 0

theorem spinV_eq (n : ℕ) (eps t : ℝ) (i : ℕ) (hi : i ≤ n) :
    spinV n eps t i = spinColumn n eps t ⟨i, by omega⟩ := by
  simp [spinV, show i < n + 1 by omega]

theorem spinV_continuous (n : ℕ) (eps : ℝ) (i : ℕ) :
    Continuous (fun t => spinV n eps t i) := by
  unfold spinV
  split_ifs with hi
  · exact spinColumn_continuous n eps ⟨i, hi⟩
  · exact continuous_const

theorem spinV_integrable_sq (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    Integrable (fun t => spinV n eps t i ^ 2) := by
  unfold spinV
  split_ifs with hi
  · exact spinColumn_integrable_sq n heps ⟨i, hi⟩
  · simp

theorem spinV_normalized (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : ℕ) (hi : i ≤ n) :
    (∫ t, spinV n eps t i ^ 2) = 1 := by
  simp_rw [spinV_eq n eps _ i hi]
  exact spinColumn_normalized n heps ⟨i, by omega⟩

theorem spinMass_pos (n : ℕ) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    0 < mass n (spinV n eps t) := by
  apply mass_pos_of_component n (spinV n eps t) 0 (by omega)
  rw [spinV_eq n eps t 0 (by omega)]
  exact (spinColumn_pos n heps t _).ne'

def I (n : ℕ) (eps : ℝ) (i : ℕ) : ℝ :=
  ∫ t, (midpoint (spinEdge n) i - q (spinJ n) t) ^ 2 * spinV n eps t i ^ 2

def G (n : ℕ) (eps : ℝ) (i : ℕ) : ℝ :=
  ∫ t, q (spinJ n) t * spinEdge n i * (spinV n eps t (i+1) - spinV n eps t i) ^ 2

def R (n i : ℕ) : ℝ := (spinEdge n i - previous (spinEdge n) i) ^ 2 / 4

def U (n : ℕ) (eps : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range (n+1), I n eps i) + (∑ i ∈ Finset.range n, G n eps i) +
    ∑ i ∈ Finset.range (n+1), R n i) / ((n : ℝ) + 1)

def diagonal (n : ℕ) (eps t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), spinA n i * spinV n eps t i ^ 2

def quotient (n : ℕ) (eps t : ℝ) : ℝ :=
  moment n (spinEdge n) (spinV n eps t) ^ 2 / mass n (spinV n eps t)

def varianceDensity (n : ℕ) (eps t : ℝ) : ℝ := diagonal n eps t - quotient n eps t

def W (n : ℕ) (eps : ℝ) : ℝ := (∫ t, varianceDensity n eps t) / ((n : ℝ) + 1)

def upperDensity (n : ℕ) (eps t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n+1),
    (midpoint (spinEdge n) i - q (spinJ n) t)^2 * spinV n eps t i^2) +
  (∑ i ∈ Finset.range n,
    q (spinJ n) t * spinEdge n i * (spinV n eps t (i+1) - spinV n eps t i)^2) +
  ∑ i ∈ Finset.range (n+1), R n i * spinV n eps t i^2

theorem q_right_eq_spinEdge (n i : ℕ) (hi : i ≤ n) :
    q (spinJ n) ((i : ℝ) - (n : ℝ) / 2 + 1 / 2) = spinEdge n i := by
  have h := spinEdge_circle n i hi
  unfold q spinJ
  rw [← h, max_eq_left (sq_nonneg _), Real.sqrt_sq (spinEdge_nonneg n i)]

theorem q_left_eq_previous (n i : ℕ) (hi : i ≤ n) :
    q (spinJ n) ((i : ℝ) - (n : ℝ) / 2 - 1 / 2) = previous (spinEdge n) i := by
  cases i with
  | zero =>
      have he : (0 : ℝ) - (n : ℝ) / 2 - 1 / 2 = -spinJ n := by unfold spinJ; ring
      rw [Nat.cast_zero, he]
      simp [q, previous]
  | succ i =>
      have he : ((i+1 : ℕ) : ℝ) - (n : ℝ) / 2 - 1 / 2 =
          (i : ℝ) - (n : ℝ) / 2 + 1 / 2 := by push_cast; ring
      rw [he]
      exact q_right_eq_spinEdge n i (by omega)

theorem midpoint_eq_k (n i : ℕ) (hi : i ≤ n) :
    midpoint (spinEdge n) i = k (spinJ n) ((i : ℝ) - (n : ℝ) / 2) := by
  unfold FiniteCopy.Algebra.midpoint k
  rw [q_right_eq_spinEdge n i hi, q_left_eq_previous n i hi]

theorem I_eq_gaussian (n : ℕ) (eps : ℝ) (i : Fin (n+1)) :
    I n eps i = ∫ t, (k (spinJ n) (spinM n i) - q (spinJ n) t)^2 *
      column (spinM n i) (spinWidth n eps i) t^2 := by
  have hi : (i : ℕ) ≤ n := by omega
  unfold I
  simp_rw [spinV_eq n eps _ i hi, midpoint_eq_k n i hi]
  rfl

theorem I_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    Integrable (fun t => (midpoint (spinEdge n) i - q (spinJ n) t)^2 *
      spinV n eps t i^2) :=
  integrable_energy (spinV_integrable_sq n heps i) (fun _ => sq_nonneg _) _ _

theorem spinV_difference_integrable_sq (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    Integrable (fun t => (spinV n eps t (i+1) - spinV n eps t i)^2) := by
  apply (((spinV_integrable_sq n heps (i+1)).add (spinV_integrable_sq n heps i)).const_mul 2).mono'
  · exact ((spinV_continuous n eps (i+1)).sub (spinV_continuous n eps i)).pow 2
      |>.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (spinV n eps t (i+1) + spinV n eps t i)]

theorem q_le_spinJ (n : ℕ) (t : ℝ) : q (spinJ n) t ≤ spinJ n := by
  nlinarith [q_sq_le (spinJ n) t, spinJ_pos n, q_nonneg (spinJ n) t]

theorem G_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    Integrable (fun t => q (spinJ n) t * spinEdge n i *
      (spinV n eps t (i+1) - spinV n eps t i)^2) := by
  apply ((spinV_difference_integrable_sq n heps i).const_mul (spinJ n * spinEdge n i)).mono'
  · exact (((continuous_q (spinJ n)).mul continuous_const).mul
      (((spinV_continuous n eps (i+1)).sub (spinV_continuous n eps i)).pow 2)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (q_nonneg (spinJ n) t) (spinEdge_nonneg n i)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (q_le_spinJ n t) (spinEdge_nonneg n i)) (sq_nonneg _)

theorem diagonal_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Integrable (diagonal n eps) :=
  integrable_finsetSum _ (fun i _ => (spinV_integrable_sq n heps i).const_mul _)

theorem diagonalEnergy_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) (a r : ℕ → ℝ) :
    Integrable (fun t => diagonalEnergy n a r (spinV n eps t)) := by
  exact integrable_finsetSum _ (fun i _ =>
    ((spinV_integrable_sq n heps i).const_mul _).add
      ((spinV_integrable_sq n heps (i+1)).const_mul _))

theorem quotient_nonneg (n : ℕ) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    0 ≤ quotient n eps t := div_nonneg (sq_nonneg _) (spinMass_pos n heps t).le

theorem quotient_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Integrable (quotient n eps) := by
  have hcont : Continuous (quotient n eps) := by
    have hv := spinV_continuous n eps
    have hm : Continuous (fun t => moment n (spinEdge n) (spinV n eps t)) := by
      unfold moment
      fun_prop
    have hs : Continuous (fun t => mass n (spinV n eps t)) := by
      unfold mass
      fun_prop
    exact (hm.pow 2).div hs (fun t => (spinMass_pos n heps t).ne')
  apply (diagonalEnergy_integrable n heps (spinEdge n) (fun _ => 1/2)).mono'
    hcont.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (quotient_nonneg n heps t)]
  exact seed_sos_bound n (spinEdge n) (fun _ => 1/2) (spinEdge n) (spinV n eps t)
    (fun i hi => by norm_num) (fun i hi => by ring) (spinMass_pos n heps t)

theorem varianceDensity_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Integrable (varianceDensity n eps) :=
  (diagonal_integrable n heps).sub (quotient_integrable n heps)

theorem upperDensity_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    Integrable (upperDensity n eps) := by
  exact ((integrable_finsetSum _ (fun i _ => I_integrable n heps i)).add
    (integrable_finsetSum _ (fun i _ => G_integrable n heps i))).add
      (integrable_finsetSum _ (fun i _ => (spinV_integrable_sq n heps i).const_mul _))

theorem integral_diagonal (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    (∫ t, diagonal n eps t) = ∑ i ∈ Finset.range (n+1), spinA n i := by
  unfold diagonal
  rw [integral_finsetSum _ (fun i _ => (spinV_integrable_sq n heps i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, spinV_normalized n heps i (by simpa using hi), mul_one]

theorem integral_diagonalEnergy (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (a r c : ℕ → ℝ) (hc : ∀ i < n, a i * (1-r i+r (i+1)) = c i) :
    (∫ t, diagonalEnergy n a r (spinV n eps t)) = ∑ i ∈ Finset.range n, c i * a i := by
  have hint (i : ℕ) : Integrable (fun t =>
      r (i+1) * a i ^ 2 * spinV n eps t i ^ 2 +
        (1-r i) * a i ^ 2 * spinV n eps t (i+1) ^ 2) :=
    ((spinV_integrable_sq n heps i).const_mul _).add
      ((spinV_integrable_sq n heps (i+1)).const_mul _)
  unfold diagonalEnergy
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  rw [integral_add ((spinV_integrable_sq n heps i).const_mul _)
      ((spinV_integrable_sq n heps (i+1)).const_mul _),
    integral_const_mul, integral_const_mul,
    spinV_normalized n heps i (by omega), spinV_normalized n heps (i+1) (by omega),
    ← hc i hi']
  ring

theorem integral_upperDensity (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    (∫ t, upperDensity n eps t) =
      (∑ i ∈ Finset.range (n+1), I n eps i) + (∑ i ∈ Finset.range n, G n eps i) +
        ∑ i ∈ Finset.range (n+1), R n i := by
  have hi : Integrable (fun t => ∑ i ∈ Finset.range (n+1),
      (FiniteCopy.Algebra.midpoint (spinEdge n) i - q (spinJ n) t)^2 * spinV n eps t i^2) :=
    integrable_finsetSum _ (fun i _ => I_integrable n heps i)
  have hg : Integrable (fun t => ∑ i ∈ Finset.range n,
      q (spinJ n) t * spinEdge n i * (spinV n eps t (i+1) - spinV n eps t i)^2) :=
    integrable_finsetSum _ (fun i _ => G_integrable n heps i)
  have hr : Integrable (fun t => ∑ i ∈ Finset.range (n+1), R n i * spinV n eps t i^2) :=
    integrable_finsetSum _ (fun i _ => (spinV_integrable_sq n heps i).const_mul _)
  have hsum := integral_add (hi.add hg) hr
  simp only [Pi.add_apply] at hsum
  unfold upperDensity
  rw [hsum, integral_add hi hg,
    integral_finsetSum _ (fun i _ => I_integrable n heps i),
    integral_finsetSum _ (fun i _ => G_integrable n heps i),
    integral_finsetSum _ (fun i _ => (spinV_integrable_sq n heps i).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, spinV_normalized n heps i (by simpa using hi), mul_one]

theorem varianceDensity_le_upper (n : ℕ) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    varianceDensity n eps t ≤ upperDensity n eps t := by
  have h := seed_variance_upper_energy n (spinA n) (spinEdge n) (spinV n eps t)
    (q (spinJ n) t) (spinMass_pos n heps t) (spinEdge_last n) (spinA_neighbors n)
  simpa only [varianceDensity, diagonal, quotient, upperDensity, R, FiniteCopy.Algebra.gradient,
    Finset.mul_sum, mul_assoc] using h

theorem W_le_U (n : ℕ) {eps : ℝ} (heps : 0 < eps) : W n eps ≤ U n eps := by
  have h := integral_mono (varianceDensity_integrable n heps) (upperDensity_integrable n heps)
    (varianceDensity_le_upper n heps)
  rw [integral_upperDensity n heps] at h
  exact div_le_div_of_nonneg_right h (by positivity)

theorem spinL_le_W (n : ℕ) {eps : ℝ} (heps : 0 < eps) : spinL n ≤ W n eps := by
  by_cases hn : n = 0
  · subst n
    simp [spinL_zero, W, varianceDensity, diagonal, quotient, moment, spinA]
  have ht := spinTau_pos n (Nat.pos_of_ne_zero hn)
  have hr := capR_bounds n (spinEdge n) (spinTau n) ht (spinTau_spec n)
  have hc (i : ℕ) (hi : i < n) := cap_coefficient (spinEdge n) (spinTau n) ht i
  have h := integral_mono (quotient_integrable n heps)
    (diagonalEnergy_integrable n heps (capA (spinEdge n) (spinTau n))
      (capR (spinEdge n) (spinTau n)))
    (fun t => seed_sos_bound n (capA (spinEdge n) (spinTau n))
      (capR (spinEdge n) (spinTau n)) (spinEdge n) (spinV n eps t) hr hc
      (spinMass_pos n heps t))
  rw [integral_diagonalEnergy n heps _ _ _ hc] at h
  unfold W varianceDensity
  rw [integral_sub (diagonal_integrable n heps) (quotient_integrable n heps),
    integral_diagonal n heps, spinA_sum_eq_edge_sq]
  exact div_le_div_of_nonneg_right (sub_le_sub_left h _) (by positivity)

theorem continuous_gaussian_sandwich (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    spinL n ≤ W n eps ∧ W n eps ≤ U n eps := ⟨spinL_le_W n heps, W_le_U n heps⟩

end CopyQuantumMetrology.ContinuousEnergy
