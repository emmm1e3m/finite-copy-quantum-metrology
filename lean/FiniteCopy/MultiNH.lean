import FiniteCopy.SpinNH
open scoped BigOperators
open Finset Filter Asymptotics

namespace FiniteCopy.NHOptimization
open FiniteCopy.Algebra NHLowerBound

noncomputable def weightedCapacity {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ) : ℝ :=
  ∑ j ∈ s, w j * spinS (n j)

noncomputable def multiObjective {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (x : ι → ℕ → ℝ) : ℝ := ∑ j ∈ s, w j * chainObjective (n j) (x j)

def multiFeasible {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (x : ι → ℕ → ℝ) : Prop :=
  (∀ j ∈ s, x j (n j) = 0) ∧ (∀ j ∈ s, ∀ i < n j, 0 ≤ x j i) ∧
    (∑ j ∈ s, w j * edgePairing (n j) (spinEdge (n j)) (x j)) = 1

def multiValues {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ) : Set ℝ :=
  {y | ∃ x : ι → ℕ → ℝ, multiFeasible s n w x ∧ multiObjective s n w x = y}

/-- 第二层加权 Cauchy--Schwarz；零自旋扇区不需要除以 S。 -/
theorem multi_cs {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (x : ι → ℕ → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (hx : ∀ j ∈ s, x j (n j) = 0) :
    (∑ j ∈ s, w j * edgePairing (n j) (spinEdge (n j)) (x j))^2 ≤
      weightedCapacity s n w * multiObjective s n w x := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun j hj => mul_nonneg (hw j hj) (spinS_nonneg (n j)))
    (fun j hj => mul_nonneg (hw j hj) (chainObjective_nonneg (n j) (x j)))
  intro j hj
  have h := mul_le_mul_of_nonneg_left (canonical_chain_cs (n j) (x j) (hx j hj)) (sq_nonneg (w j))
  convert h using 1 <;> ring

theorem multi_lower_bound {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hD : 0 < weightedCapacity s n w)
    (x : ι → ℕ → ℝ) (hx : multiFeasible s n w x) :
    1 / weightedCapacity s n w ≤ multiObjective s n w x := by
  have h := multi_cs s n w x hw hx.1
  rw [hx.2.2] at h
  apply (div_le_iff₀ hD).mpr
  nlinarith

/-- 完整达到点：所有扇区使用同一个归一化因子。 -/
noncomputable def minimizingEdges {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (j : ι) (i : ℕ) : ℝ := (1 / weightedCapacity s n w) * canonicalA (n j) i

theorem minimizingEdges_feasible {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (hD : 0 < weightedCapacity s n w) :
    multiFeasible s n w (minimizingEdges s n w) := by
  constructor
  · intro j _
    simp [minimizingEdges, canonicalA_last]
  constructor
  · intro j _ i _
    exact mul_nonneg (by positivity) (canonicalA_nonneg (n j) i)
  · unfold minimizingEdges
    simp_rw [edgePairing_scale]
    have he : ∀ j, edgePairing (n j) (spinEdge (n j)) (canonicalA (n j)) = spinS (n j) :=
      fun _ => rfl
    simp_rw [he]
    calc
      _ = (1 / weightedCapacity s n w) * weightedCapacity s n w := by
        unfold weightedCapacity
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = 1 := by field_simp

theorem minimizingEdges_value {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (hD : 0 < weightedCapacity s n w) :
    multiObjective s n w (minimizingEdges s n w) = 1 / weightedCapacity s n w := by
  unfold multiObjective minimizingEdges
  simp_rw [chainObjective_scale, canonical_attains]
  calc
    _ = (1 / weightedCapacity s n w)^2 * weightedCapacity s n w := by
      unfold weightedCapacity
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = 1 / weightedCapacity s n w := by field_simp

theorem multi_minimum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hD : 0 < weightedCapacity s n w) :
    IsLeast (multiValues s n w) (1 / weightedCapacity s n w) := by
  constructor
  · exact ⟨minimizingEdges s n w, minimizingEdges_feasible s n w hD,
      minimizingEdges_value s n w hD⟩
  · rintro z ⟨x, hx, rfl⟩
    exact multi_lower_bound s n w hw hD x hx

theorem multi_infimum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hD : 0 < weightedCapacity s n w) :
    sInf (multiValues s n w) = 1 / weightedCapacity s n w :=
  (multi_minimum s n w hw hD).csInf_eq

end FiniteCopy.NHOptimization

