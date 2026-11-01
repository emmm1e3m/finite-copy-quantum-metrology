import FiniteCopy.UnitaryTransport
import FiniteCopy.Resolution

open scoped BigOperators
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator
open CopyQuantumMetrology CopyQuantumMetrology.ClebschGordan
open CopyQuantumMetrology.SpinPaths CopyQuantumMetrology.TensorModel

def physicalRaising (N : ℕ) : NMatrix N := collectiveX N+Complex.I • collectiveY N
def frameUnitary (N : ℕ) : Matrix (Bits N) (Space N) ℂ := (actualFrame N).basis
def diagonalRaising (N : ℕ) : Mat (Space N) :=
  Matrix.blockDiagonal' (fun b : B N => complexR (spin N b))

theorem frameUnitary_left (N : ℕ) : (frameUnitary N)ᴴ*frameUnitary N=1 :=
  (actualFrame N).left

theorem frameUnitary_right (N : ℕ) : frameUnitary N*(frameUnitary N)ᴴ=1 :=
  (actualFrame N).right

lemma complexR_from_axes (n : ℕ) : complexR n = Jx n+Complex.I • Jy n := by
  ext i j
  simp [Jx,Jy,Matrix.smul_apply,smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma diagonalRaising_from_axes (N : ℕ) : diagonalRaising N =
    diagOp (signature N) 0+Complex.I • diagOp (signature N) 1 := by
  unfold diagonalRaising diagOp
  simp only [spinOp, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [← Matrix.blockDiagonal'_smul, ← Matrix.blockDiagonal'_add]
  congr 1
  funext b
  exact complexR_from_axes (spin N b)

lemma collective_transport (N : ℕ) (a : Fin 2) : collectiveAxes N a =
    transport (frameUnitary N) (diagOp (signature N) a) := by
  calc
    _ = collectiveAxes N a * (frameUnitary N*(frameUnitary N)ᴴ) := by
      rw [frameUnitary_right, Matrix.mul_one]
    _ = (collectiveAxes N a * frameUnitary N)*(frameUnitary N)ᴴ := by
      rw [Matrix.mul_assoc]
    _ = _ := by
      rw [show collectiveAxes N a * frameUnitary N = frameUnitary N*diagOp (signature N) a
        from (actualFrame N).intertwine a]
      rfl

theorem physicalRaising_transport (N : ℕ) : physicalRaising N =
    transport (frameUnitary N) (diagonalRaising N) := by
  rw [diagonalRaising_from_axes, transport_add, transport_smul,
    ← collective_transport, ← collective_transport]
  simp [physicalRaising, collectiveAxes]

end FiniteCopy.NHOperator
