import FiniteCopy.ActualPaths
open scoped BigOperators
open Finset

namespace FiniteCopy.EndpointCounting
open CopyQuantumMetrology.SpinPaths

theorem reindex_count_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ range (N+1), (endpointCount N n : ℝ)*f n) =
      ∑ k ∈ range (N/2+1), (ballot N k : ℝ)*f (N-2*k) := by
  let s := (range (N/2+1)).image (fun k => N-2*k)
  have hsub : s ⊆ range (N+1) := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
    exact mem_range.mpr (by omega)
  have hs : (∑ n ∈ s, (endpointCount N n : ℝ)*f n) =
      ∑ n ∈ range (N+1), (endpointCount N n : ℝ)*f n := by
    apply sum_subset hsub
    intro n _ hn
    have hno : ¬∃k : ℕ, N=n+2*k := by
      rintro ⟨k,hk⟩
      apply hn
      exact mem_image.mpr ⟨k, mem_range.mpr (by omega), by omega⟩
    rw [endpointCount_zero_of_no_endpoint N n hno]
    simp
  rw [← hs]
  dsimp only [s]
  rw [sum_image (s := range (N/2+1)) (g := fun k => N-2*k) (by
    intro k hk l hl he
    have hk' : k < N/2+1 := mem_range.mp hk
    have hl' : l < N/2+1 := mem_range.mp hl
    change N-2*k=N-2*l at he
    omega)]
  apply sum_congr rfl
  intro k hk
  rw [endpointCount_ballot N (N-2*k) k (by have := mem_range.mp hk; omega)]

theorem ballot_dimension_weight (N k : ℕ) (hk : k ≤ N/2) :
    (ballot N k : ℝ) * (((N-2*k : ℕ) : ℝ)+1) / 2^N = Schur.weight N k := by
  have hp : prevChoose N k ≤ N.choose k := prevChoose_le (by omega)
  have hsub : 2*k ≤ N := by omega
  have hprev : (prevChoose N k : ℝ) =
      if k=0 then 0 else (N.choose (k-1) : ℝ) := by
    unfold prevChoose
    split_ifs <;> simp
  unfold ballot Schur.weight Schur.binom
  rw [Nat.cast_sub hp, Nat.cast_sub hsub, hprev]
  push_cast
  ring

/-- 039真实CG路径上的任意端点函数平均，严格等于016实际Schur权重平均。 -/
theorem path_schur_average (N : ℕ) (f : ℕ → ℝ) :
    (∑ b : B N, (((spin N b : ℝ)+1)/2^N) * f (spin N b)) =
      Schur.schurAverage f N := by
  rw [sum_paths_by_endpoint N (fun n => (((n : ℝ)+1)/2^N)*f n), reindex_count_sum]
  unfold Schur.schurAverage
  apply sum_congr rfl
  intro k hk
  calc
    _ = ((ballot N k : ℝ) * (((N-2*k : ℕ) : ℝ)+1) / 2^N) * f (N-2*k) := by ring
    _ = _ := by rw [ballot_dimension_weight N k (by simpa using mem_range.mp hk)]

end FiniteCopy.EndpointCounting
