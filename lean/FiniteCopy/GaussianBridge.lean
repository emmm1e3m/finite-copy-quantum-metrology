import FiniteCopy.RiskBridge
import FiniteCopy.GaussianVariance

open scoped BigOperators
open Finset

namespace FiniteCopy.EndpointCounting
open CopyQuantumMetrology CopyQuantumMetrology.SpinPaths

/-- 任意固定正宽度序列的真实Gaussian Fisher，按实际CG路径平均。 -/
theorem path_gaussian_denominator (N : ℕ) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n) :
    (∑ b : B N, pathWeight N b * (2*gaussianFisher (spin N b) (eps (spin N b)))) =
      2*N-4*Schur.schurAverage (fun n => gaussianVariance n (eps n) (n+3)) N := by
  unfold pathWeight
  rw [path_schur_average N (fun n => 2*gaussianFisher n (eps n))]
  have he : (fun n : ℕ => 2*gaussianFisher n (eps n)) =
      (fun n : ℕ => (8/3 : ℝ)*((n : ℝ)/2)*((n : ℝ)/2+1)-4*gaussianVariance n (eps n) (n+3)) := by
    funext n
    exact gaussian_fisher_variance n (heps n) (by omega : 3 ≤ n+3) (by omega)
  rw [he]
  exact Schur.schurAverage_fisher _ N

theorem path_gaussian_risk_expression (N : ℕ) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n) :
    4*N / (∑ b : B N, pathWeight N b * (2*gaussianFisher (spin N b) (eps (spin N b)))) =
      4*N / (2*N-4*Schur.schurAverage (fun n => gaussianVariance n (eps n) (n+3)) N) := by
  rw [path_gaussian_denominator N eps heps]

end FiniteCopy.EndpointCounting
