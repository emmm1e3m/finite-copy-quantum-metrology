import FiniteCopy.PathSchur
import FiniteCopy.RiskTerminal
open scoped BigOperators
open Finset

namespace FiniteCopy.EndpointCounting
open CopyQuantumMetrology CopyQuantumMetrology.SpinPaths

noncomputable def pathWeight (N : ℕ) (b : B N) : ℝ := ((spin N b : ℝ)+1)/2^N

theorem pathWeight_pos (N : ℕ) (b : B N) : 0 < pathWeight N b := by
  unfold pathWeight
  positivity

theorem pathWeight_sum (N : ℕ) : (∑ b : B N, pathWeight N b) = 1 := by
  have h := path_schur_average N (fun _ => (1 : ℝ))
  simpa [pathWeight, Schur.schurAverage, Schur.weight_sum] using h

theorem path_dimension_sum (N : ℕ) : (∑ b : B N, (spin N b+1)) = 2^N := by
  have h := pathWeight_sum N
  unfold pathWeight at h
  rw [← sum_div] at h
  have hr := (div_eq_one_iff_eq (by positivity : (2 : ℝ)^N ≠ 0)).mp h
  exact_mod_cast hr

/-- 035终端中的hcap已由实际CG路径及已证多重度直接实例化。 -/
theorem path_cap_bound (N : ℕ) :
    (∑ b : B N, pathWeight N b * Risk.capFisherBound (spin N b)) =
      Schur.schurAverage Risk.capFisherBound N :=
  path_schur_average N Risk.capFisherBound

theorem path_cap_denominator (N : ℕ) :
    (∑ b : B N, pathWeight N b * Risk.capFisherBound (spin N b)) =
      2*N-4*Schur.schurAverage NHLowerBound.spinL N := by
  rw [path_cap_bound, Risk.schur_capFisherBound]

theorem path_cap_risk_expression (N : ℕ) :
    4*N / (∑ b : B N, pathWeight N b * Risk.capFisherBound (spin N b)) =
      4*N / (2*N-4*Schur.schurAverage NHLowerBound.spinL N) := by
  rw [path_cap_denominator]

end FiniteCopy.EndpointCounting
