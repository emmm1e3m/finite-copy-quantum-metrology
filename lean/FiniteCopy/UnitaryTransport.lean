import FiniteCopy.MatrixDual
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace FiniteCopy.NHOperator

section Transport
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (U : Matrix ι κ ℂ)

def transport (A : Mat κ) : Mat ι := U*A*Uᴴ

lemma transport_add (A B : Mat κ) : transport U (A+B) = transport U A+transport U B := by
  simp only [transport, Matrix.mul_add, Matrix.add_mul]

lemma transport_sub (A B : Mat κ) : transport U (A-B) = transport U A-transport U B := by
  simp only [transport, Matrix.mul_sub, Matrix.sub_mul]

lemma transport_smul (z : ℂ) (A : Mat κ) : transport U (z • A) = z • transport U A := by
  simp only [transport, Matrix.mul_smul, Matrix.smul_mul]

lemma transport_real_smul (z : ℝ) (A : Mat κ) : transport U (z • A) = z • transport U A := by
  simp only [transport, Matrix.mul_smul, Matrix.smul_mul]

lemma transport_adjoint (A : Mat κ) : (transport U A)ᴴ = transport U Aᴴ := by
  simp only [transport, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma transport_hermitian (A : Mat κ) (hA : A.IsHermitian) : (transport U A).IsHermitian := by
  change (transport U A)ᴴ = transport U A
  rw [transport_adjoint, hA.eq]

lemma transport_positive (A : Mat κ) (hA : A.PosSemidef) : (transport U A).PosSemidef :=
  hA.mul_mul_conjTranspose_same U

variable (hU : Uᴴ*U=1)
include hU

lemma transport_mul (A B : Mat κ) : transport U (A*B) = transport U A*transport U B := by
  unfold transport
  calc
    _ = U*A*(Uᴴ*U)*B*Uᴴ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma transport_trace (A : Mat κ) : tr (transport U A) = tr A := by
  unfold tr transport
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma transport_trace_product (A B : Mat κ) :
    tr (transport U A*transport U B) = tr (A*B) := by
  rw [← transport_mul U hU, transport_trace U hU]

lemma transport_inverse (A : Mat κ) : transport Uᴴ (transport U A) = A := by
  simp only [transport, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (Uᴴ*U)*A*(Uᴴ*U) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hU, Matrix.one_mul, Matrix.mul_one]

end Transport
end FiniteCopy.NHOperator
