import FiniteCopy.MultiNH
open scoped BigOperators
open Finset Filter Asymptotics

namespace FiniteCopy.NHOptimization
open FiniteCopy.Algebra NHLowerBound

noncomputable def schurSectorWeight (N k : ℕ) : ℝ :=
  Schur.weight N k / ((N-2*k : ℕ)+1 : ℕ)

noncomputable def schurCapacity (N : ℕ) : ℝ :=
  weightedCapacity (range (N/2+1)) (fun k => N-2*k) (schurSectorWeight N)

/-- 原始有限凸优化的值，而非闭式公式的重命名。 -/
noncomputable def reducedNH (N : ℕ) : ℝ :=
  N * sInf (multiValues (range (N/2+1)) (fun k => N-2*k) (schurSectorWeight N))

theorem spinS_div_dimension (n : ℕ) :
    spinS n / ((n : ℝ)+1) =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - spinL n := by
  have hsum : (∑ i ∈ range n, spinEdge n i^2) =
      (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) * ((n : ℝ)+1) :=
    (spinA_sum_eq_edge_sq n).symm.trans (spinA_sum n)
  unfold spinS capSum canonicalA capA spinL spinD
  rw [hsum]
  field_simp
  ring

theorem schurSectorWeight_nonneg (N k : ℕ) (hk : k ∈ range (N/2+1)) :
    0 ≤ schurSectorWeight N k := by
  apply div_nonneg
  · exact Schur.weight_nonneg (by simpa using mem_range.mp hk)
  · positivity

theorem schurSectorWeight_zero_pos (N : ℕ) : 0 < schurSectorWeight N 0 := by
  unfold schurSectorWeight Schur.weight Schur.binom
  simp only [Nat.choose_zero_right, Nat.cast_one, ↓reduceIte, sub_zero,
    Nat.cast_zero, mul_zero, Nat.sub_zero, Nat.cast_add]
  positivity

theorem schurCapacity_pos (N : ℕ) (hN : 0 < N) : 0 < schurCapacity N := by
  have h0 : 0 < schurSectorWeight N 0 * spinS (N-2*0) := by
    simpa using mul_pos (schurSectorWeight_zero_pos N) (spinS_pos hN)
  exact h0.trans_le (single_le_sum
    (fun k hk => mul_nonneg (schurSectorWeight_nonneg N k hk) (spinS_nonneg (N-2*k)))
    (show 0 ∈ range (N/2+1) by simp))

theorem schurCapacity_eq (N : ℕ) :
    schurCapacity N = (N : ℝ)/2 - Schur.schurAverage spinL N := by
  have hrepr : schurCapacity N =
      Schur.schurAverage (fun n => spinS n/((n : ℝ)+1)) N := by
    unfold schurCapacity weightedCapacity schurSectorWeight Schur.schurAverage
    apply sum_congr rfl
    intro k _
    push_cast
    ring
  rw [hrepr]
  have hlin : Schur.schurAverage (fun n => spinS n/((n : ℝ)+1)) N =
      (2/3 : ℝ) * Schur.schurAverage (fun n => ((n : ℝ)/2)*((n : ℝ)/2+1)) N -
        Schur.schurAverage spinL N := by
    unfold Schur.schurAverage
    simp_rw [spinS_div_dimension]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [hlin, Schur.schurAverage_casimir]
  ring

theorem schur_multi_minimum (N : ℕ) (hN : 0 < N) :
    IsLeast (multiValues (range (N/2+1)) (fun k => N-2*k) (schurSectorWeight N))
      (1 / schurCapacity N) :=
  multi_minimum _ _ _ (schurSectorWeight_nonneg N) (schurCapacity_pos N hN)

/-- 真实 max 链凸优化的精确值，经真实 Schur 权重接到闭式 NH 表达式。 -/
theorem reducedNH_formula (N : ℕ) (hN : 0 < N) :
    reducedNH N = 4*N / (2*N-4*Schur.schurAverage spinL N) := by
  have hD := schurCapacity_pos N hN
  have hi := (schur_multi_minimum N hN).csInf_eq
  unfold reducedNH
  rw [hi]
  have hfour : (2 : ℝ)*N-4*Schur.schurAverage spinL N = 4*schurCapacity N := by
    rw [schurCapacity_eq]
    ring
  rw [hfour]
  field_simp

end FiniteCopy.NHOptimization

