import FiniteCopy.RaisingIdentification
import FiniteCopy.BlockNH
import FiniteCopy.RiskBridge

open scoped BigOperators
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator
open CopyQuantumMetrology.SpinPaths
open FiniteCopy.NHOptimization FiniteCopy.EndpointCounting

-- NH约束中的两轴对应真实张量模型在原点的两个导数。
theorem originalNH_derivative_x (N : ℕ) :
    HasDerivAt (fun x : ℝ => CopyQuantumMetrology.TensorModel.rhoTensor N x 0)
      ((2/(2:ℂ)^N) • axisX (physicalRaising N)) 0 := by
  rw [axisX_physicalRaising]
  exact CopyQuantumMetrology.TensorModel.rhoTensor_hasDerivAt_x N

theorem originalNH_derivative_y (N : ℕ) :
    HasDerivAt (fun y : ℝ => CopyQuantumMetrology.TensorModel.rhoTensor N 0 y)
      ((2/(2:ℂ)^N) • axisY (physicalRaising N)) 0 := by
  rw [axisY_physicalRaising]
  exact CopyQuantumMetrology.TensorModel.rhoTensor_hasDerivAt_y N

def pathCapacity (N : ℕ) : ℝ := ∑ b : B N, spinS (spin N b)

lemma pathCapacity_pos (N : ℕ) (hN : 0<N) : 0<pathCapacity N := by
  have hc : Fintype.card {b : B N // spin N b=N}=1 := by
    simpa using actual_path_multiplicity_card N 0 (Nat.zero_le (N/2))
  have hn : Nonempty {b : B N // spin N b=N} :=
    Fintype.card_pos_iff.mp (by rw [hc]; omega)
  obtain ⟨b⟩ := hn
  have hb : 0<spinS (spin N b.val) := by
    rw [b.property]
    exact spinS_pos hN
  exact hb.trans_le (Finset.single_le_sum
    (fun c _ => spinS_nonneg (spin N c)) (Finset.mem_univ b.val))

lemma capFisherBound_spinS (n : ℕ) :
    Risk.capFisherBound n = (4 / (n+1 : ℕ))*spinS n := rfl

lemma schur_cap_pathCapacity (N : ℕ) :
    Schur.schurAverage Risk.capFisherBound N = 4*pathCapacity N/(2:ℝ)^N := by
  rw [← path_cap_bound]
  unfold pathCapacity
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  rw [capFisherBound_spinS]
  unfold pathWeight
  push_cast
  have hd : (spin N b:ℝ)+1 ≠ 0 := by positivity
  have hp : (2:ℝ)^N ≠ 0 := by positivity
  field_simp

-- 原模型的NH值：优化全部第一矩和全部实对称Hermitian算子块。
def actualNHRisk (N : ℕ) : ℝ := nhRisk (N:ℝ) ((2:ℝ)^N) (physicalRaising N)

theorem originalNH_values (N : ℕ) :
    nhValues ((2:ℝ)^N) (physicalRaising N) =
      nhValues ((2:ℝ)^N) (blockRaising (spin N) (fun b => Algebra.spinEdge (spin N b))) := by
  rw [physicalRaising_block_transport,
    nhValues_unitary (frameUnitary N) (frameUnitary_left N) (frameUnitary_right N)]

theorem originalNH_minimum (N : ℕ) (hN : 0<N) :
    IsLeast (nhValues ((2:ℝ)^N) (physicalRaising N))
      (((2:ℝ)^N)^2/pathCapacity N) := by
  rw [originalNH_values]
  exact block_NH_minimum (spin N) ((2:ℝ)^N) (by positivity) (pathCapacity_pos N hN)

theorem actualNHRisk_eq_capacity (N : ℕ) (hN : 0<N) :
    actualNHRisk N = (N:ℝ)*(2:ℝ)^N/pathCapacity N := by
  unfold actualNHRisk
  rw [physicalRaising_block_transport,
    nhRisk_unitary (frameUnitary N) (frameUnitary_left N) (frameUnitary_right N)]
  exact block_NH_risk (spin N) (N:ℝ) ((2:ℝ)^N) (by positivity) (pathCapacity_pos N hN)

theorem originalNH_formula (N : ℕ) (hN : 0<N) :
    actualNHRisk N = 4*(N:ℝ)/Schur.schurAverage Risk.capFisherBound N := by
  rw [actualNHRisk_eq_capacity N hN, schur_cap_pathCapacity]
  have hS : pathCapacity N ≠ 0 := ne_of_gt (pathCapacity_pos N hN)
  have hD : (2:ℝ)^N ≠ 0 := by positivity
  field_simp

theorem originalNH_deficit (N : ℕ) (hN : 0<N) :
    actualNHRisk N = 4*(N:ℝ)/(2*N-4*Schur.schurAverage NHLowerBound.spinL N) := by
  rw [originalNH_formula N hN, Risk.schur_capFisherBound]

end FiniteCopy.NHOperator
