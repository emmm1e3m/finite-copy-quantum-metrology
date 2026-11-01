import FiniteCopy.Gaussian
import FiniteCopy.QuantumModel
import FiniteCopy.Phase
import FiniteCopy.EnergyAsymptotics
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped BigOperators ComplexOrder

noncomputable section
namespace CopyQuantumMetrology

/-- n=2j，有限自旋格点使用 n+1 个坐标。 -/
def spinJ (n : ℕ) : ℝ := ((n : ℝ) + 1) / 2

def spinM (n : ℕ) (i : Fin (n+1)) : ℝ := (i : ℕ) - (n : ℝ) / 2

lemma spinJ_pos (n : ℕ) : 0 < spinJ n := by
  unfold spinJ
  positivity

lemma spinM_bounds (n : ℕ) (i : Fin (n+1)) :
    -(spinJ n) + 1/2 ≤ spinM n i ∧ spinM n i ≤ spinJ n - 1/2 := by
  have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
  have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  dsimp [spinJ, spinM]
  constructor <;> linarith

lemma spin_radial_pos (n : ℕ) (i : Fin (n+1)) :
    0 < spinJ n ^ 2 - spinM n i ^ 2 := by
  obtain ⟨hl, hu⟩ := spinM_bounds n i
  have hp : 0 < spinJ n - spinM n i := by linarith
  have hm : 0 < spinJ n + spinM n i := by linarith
  nlinarith [mul_pos hp hm]

/-- 与正文 J a_epsilon(m/J) 完全相同的正宽度。 -/
def spinWidth (n : ℕ) (eps : ℝ) (i : Fin (n+1)) : ℝ :=
  (spinJ n ^ 2 - spinM n i ^ 2) /
    (2 * spinJ n * Real.sqrt ((spinM n i / spinJ n)^2 + eps^2))

lemma spinWidth_pos (n : ℕ) {eps : ℝ} (heps : 0 < eps) (i : Fin (n+1)) :
    0 < spinWidth n eps i := by
  apply div_pos (spin_radial_pos n i)
  have hj := spinJ_pos n
  positivity

lemma spinWidth_eq_paper (n : ℕ) (eps : ℝ) (i : Fin (n+1)) :
    spinWidth n eps i =
      spinJ n * (1 - (spinM n i / spinJ n)^2) /
        (2 * Real.sqrt ((spinM n i / spinJ n)^2 + eps^2)) := by
  have hj : spinJ n ≠ 0 := (spinJ_pos n).ne'
  unfold spinWidth
  field_simp

def spinColumn (n : ℕ) (eps : ℝ) (t : ℝ) (i : Fin (n+1)) : ℝ :=
  column (spinM n i) (spinWidth n eps i) t

theorem spinColumn_pos (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (t : ℝ) (i : Fin (n+1)) : 0 < spinColumn n eps t i := by
  exact column_pos _ _ (spinWidth_pos n heps i)

theorem spinColumn_integrable_sq (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (i : Fin (n+1)) : Integrable (fun t => spinColumn n eps t i ^ 2) := by
  exact integrable_column_sq _ (spinWidth_pos n heps i)

theorem spinColumn_normalized (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (i : Fin (n+1)) : (∫ t, spinColumn n eps t i ^ 2) = 1 := by
  exact integral_column_sq _ (spinWidth_pos n heps i)

theorem spinColumn_continuous (n : ℕ) (eps : ℝ) (i : Fin (n+1)) :
    Continuous (fun t => spinColumn n eps t i) := by
  unfold spinColumn column
  fun_prop

theorem spinColumn_cross_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    (i j : Fin (n+1)) :
    Integrable (fun t => spinColumn n eps t i * spinColumn n eps t j) := by
  have hi : MemLp (fun t => spinColumn n eps t i) 2 volume :=
    (memLp_two_iff_integrable_sq (spinColumn_continuous n eps i).aestronglyMeasurable).2
      (spinColumn_integrable_sq n heps i)
  have hj : MemLp (fun t => spinColumn n eps t j) 2 volume :=
    (memLp_two_iff_integrable_sq (spinColumn_continuous n eps j).aestronglyMeasurable).2
      (spinColumn_integrable_sq n heps j)
  exact hi.integrable_mul hj

def spinEffect (n : ℕ) (eps : ℝ) {L : ℕ} [NeZero L]
    (t : ℝ) (k : ZMod L) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  effect (fun i => (spinColumn n eps t i : ℂ)) (fun i => -(i.val : ZMod L)) k

theorem spinEffect_positive (n : ℕ) (eps : ℝ) {L : ℕ} [NeZero L]
    (t : ℝ) (k : ZMod L) : (spinEffect n eps t k).PosSemidef :=
  effect_positive _ _ _

theorem spinEffect_complete (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    {L : ℕ} [NeZero L] (hL : n+1 ≤ L) :
    (fun i j => ∫ t, ∑ k : ZMod L, spinEffect n eps t k i j) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := by
  exact real_continuous_phase_complete volume (spinColumn n eps) _
    (PhaseMoments.fin_neg_zmod_injective hL) (spinColumn_normalized n heps)

theorem spinEffect_integrable (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    {L : ℕ} [NeZero L] (k : ZMod L) (i j : Fin (n+1)) :
    Integrable (fun t => spinEffect n eps t k i j) := by
  apply effect_integrable volume
  intro i j
  convert (spinColumn_cross_integrable n heps i j).ofReal using 1
  ext t
  simp

theorem spinEffect_complete_separated (n : ℕ) {eps : ℝ} (heps : 0 < eps)
    {L : ℕ} [NeZero L] (hL : n+1 ≤ L) :
    (fun i j => ∑ k : ZMod L, ∫ t, spinEffect n eps t k i j) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := by
  ext i j
  rw [← integral_finsetSum _ (fun k _ => spinEffect_integrable n heps k i j)]
  exact congrFun (congrFun (spinEffect_complete n heps hL) i) j

/-- 显式对数宽度对应的每个有限自旋测量，无渐近或归一化假设。 -/
theorem logarithmic_gaussian_measurement (n : ℕ) {L : ℕ} [NeZero L]
    (hL : n+1 ≤ L) :
    (∀ t k, (spinEffect n (epsilon (spinJ n)) t (k : ZMod L)).PosSemidef) ∧
    (∀ k i j, Integrable (fun t => spinEffect n (epsilon (spinJ n)) t
      (k : ZMod L) i j)) ∧
    (fun i j => ∑ k : ZMod L, ∫ t, spinEffect n (epsilon (spinJ n)) t k i j) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := by
  have heps := epsilon_pos (spinJ_pos n).le
  exact ⟨spinEffect_positive n _, spinEffect_integrable n heps,
    spinEffect_complete_separated n heps hL⟩

end CopyQuantumMetrology
