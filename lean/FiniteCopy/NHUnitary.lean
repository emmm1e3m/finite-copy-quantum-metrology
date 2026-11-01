import FiniteCopy.UnitaryTransport
import FiniteCopy.NHModel
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator

section Unitary
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (U : Matrix ι κ ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1)

include hU in
lemma squareSum_transport (X Y : Mat κ) :
    squareSum (transport U X) (transport U Y) = transport U (squareSum X Y) := by
  simp only [squareSum, transport_add, transport_mul U hU]

include hU in
lemma commutator_transport (X Y : Mat κ) :
    commutator (transport U X) (transport U Y) = transport U (commutator X Y) := by
  simp only [commutator, transport_smul, transport_sub, transport_mul U hU]

include hU in
lemma nhAuxValues_transport_subset (X Y : Mat κ) :
    nhAuxValues X Y ⊆ nhAuxValues (transport U X) (transport U Y) := by
  rintro v ⟨T,hT,hminus,hplus,hv⟩
  refine ⟨transport U T, transport_hermitian U T hT, ?_, ?_, ?_⟩
  · rw [commutator_transport U hU, ← transport_sub]
    exact transport_positive U _ hminus
  · rw [commutator_transport U hU, ← transport_add]
    exact transport_positive U _ hplus
  · rw [squareSum_transport U hU, ← transport_add, transport_trace U hU]
    exact hv

include hU hU' in
theorem nhAuxValues_unitary (X Y : Mat κ) :
    nhAuxValues (transport U X) (transport U Y) = nhAuxValues X Y := by
  apply Set.Subset.antisymm
  · intro v hv
    have h := nhAuxValues_transport_subset Uᴴ (by simpa using hU') _ _ hv
    simpa only [transport_inverse U hU] using h
  · exact nhAuxValues_transport_subset U hU X Y

lemma nhBlockValues_eq_aux (X Y : Mat κ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    nhBlockValues X Y = nhAuxValues X Y :=
  Set.Subset.antisymm (nhBlock_to_aux X Y hX hY) (nhAux_to_block X Y hX hY)

include hU hU' in
theorem nhBlockValues_unitary (X Y : Mat κ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    nhBlockValues (transport U X) (transport U Y) = nhBlockValues X Y := by
  rw [nhBlockValues_eq_aux _ _ (transport_hermitian U X hX) (transport_hermitian U Y hY),
    nhBlockValues_eq_aux X Y hX hY, nhAuxValues_unitary U hU hU']

lemma axisX_transport (C : Mat κ) : axisX (transport U C) = transport U (axisX C) := by
  simp only [axisX, transport_real_smul, transport_add, transport_adjoint]

lemma axisY_transport (C : Mat κ) : axisY (transport U C) = transport U (axisY C) := by
  simp only [axisY, transport_smul, transport_sub, transport_adjoint]

include hU in
theorem FirstMomentFeasible.transport {D : ℝ} {C X Y : Mat κ}
    (h : FirstMomentFeasible D C X Y) :
    FirstMomentFeasible D (NHOperator.transport U C) (NHOperator.transport U X)
      (NHOperator.transport U Y) := by
  refine ⟨transport_hermitian U X h.hermitianX, transport_hermitian U Y h.hermitianY,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [transport_trace U hU]; exact h.meanX
  · rw [transport_trace U hU]; exact h.meanY
  · rw [axisX_transport, transport_trace_product U hU]; exact h.xx
  · rw [axisY_transport, transport_trace_product U hU]; exact h.xy
  · rw [axisX_transport, transport_trace_product U hU]; exact h.yx
  · rw [axisY_transport, transport_trace_product U hU]; exact h.yy

include hU hU' in
lemma nhValues_transport_subset (D : ℝ) (C : Mat κ) :
    nhValues D C ⊆ nhValues D (transport U C) := by
  rintro v ⟨X,Y,hF,hv⟩
  refine ⟨transport U X, transport U Y, hF.transport U hU, ?_⟩
  rwa [nhBlockValues_unitary U hU hU' X Y hF.hermitianX hF.hermitianY]

include hU hU' in
theorem nhValues_unitary (D : ℝ) (C : Mat κ) :
    nhValues D (transport U C) = nhValues D C := by
  apply Set.Subset.antisymm
  · intro v hv
    have h := nhValues_transport_subset Uᴴ (by simpa using hU') (by simpa using hU) D _ hv
    simpa only [transport_inverse U hU] using h
  · exact nhValues_transport_subset U hU hU' D C

include hU hU' in
theorem nhRisk_unitary (N D : ℝ) (C : Mat κ) :
    nhRisk N D (transport U C) = nhRisk N D C := by
  simp only [nhRisk, nhValues_unitary U hU hU']

end Unitary
end FiniteCopy.NHOperator

