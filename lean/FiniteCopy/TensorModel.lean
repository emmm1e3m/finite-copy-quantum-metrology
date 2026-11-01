import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.Elementwise
open Matrix

noncomputable section
namespace CopyQuantumMetrology.TensorModel

-- 计算基按每个量子比特 m=-1/2,+1/2 升序排列，与 SpinPhase 一致。
abbrev Qubit := Fin 2
abbrev Bits (N : ℕ) := Fin N → Qubit
abbrev QMatrix := Matrix Qubit Qubit ℂ
abbrev NMatrix (N : ℕ) := Matrix (Bits N) (Bits N) ℂ

def sigmaX : QMatrix := !![0, 1; 1, 0]
def sigmaY : QMatrix := !![0, Complex.I; -Complex.I, 0]
def sigmaZ : QMatrix := !![-1, 0; 0, 1]

-- 逐位矩阵元乘积是真实的 Kronecker 张量幂。
def tensorPower (N : ℕ) (A : QMatrix) : NMatrix N :=
  fun b c => ∏ r, A (b r) (c r)

def rho (x y : ℝ) : QMatrix :=
  (2 : ℂ)⁻¹ • ((1 : QMatrix) + (x : ℂ) • sigmaX + (y : ℂ) • sigmaY)

def rhoTensor (N : ℕ) (x y : ℝ) : NMatrix N := tensorPower N (rho x y)

-- 第 r 个张量因子上的真实局部算子；其余因子为单位矩阵。
def onSite (N : ℕ) (r : Fin N) (A : QMatrix) : NMatrix N :=
  fun b c => A (b r) (c r) * ∏ s ∈ Finset.univ.erase r, (1 : QMatrix) (b s) (c s)

def collective (N : ℕ) (A : QMatrix) : NMatrix N :=
  (2 : ℂ)⁻¹ • ∑ r, onSite N r A

def collectiveX (N : ℕ) : NMatrix N := collective N sigmaX
def collectiveY (N : ℕ) : NMatrix N := collective N sigmaY
def collectiveZ (N : ℕ) : NMatrix N := collective N sigmaZ

@[simp] theorem tensorPower_one (N : ℕ) : tensorPower N (1 : QMatrix) = 1 := by
  classical
  ext b c
  by_cases h : b = c
  · subst c
    simp [tensorPower]
  · have hex : ∃ r, b r ≠ c r := by
      by_contra hh
      push Not at hh
      exact h (funext hh)
    obtain ⟨r, hr⟩ := hex
    have hz : ∏ s : Fin N, (1 : QMatrix) (b s) (c s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])
    simpa [tensorPower, Matrix.one_apply, h] using hz

theorem tensorPower_smul (N : ℕ) (a : ℂ) (A : QMatrix) :
    tensorPower N (a • A) = a ^ N • tensorPower N A := by
  ext b c
  simp [tensorPower, Finset.prod_mul_distrib]

theorem tensorPower_succ (N : ℕ) (A : QMatrix) (b c : Bits (N+1)) :
    tensorPower (N+1) A b c =
      (A ⊗ₖ tensorPower N A) (b 0, fun i => b i.succ) (c 0, fun i => c i.succ) := by
  simp [tensorPower, Fin.prod_univ_succ, Matrix.kroneckerMap_apply]

@[simp] theorem rho_zero : rho 0 0 = (2 : ℂ)⁻¹ • (1 : QMatrix) := by
  simp [rho]

theorem rhoTensor_zero (N : ℕ) : rhoTensor N 0 0 = ((2 : ℂ)^N)⁻¹ • 1 := by
  simp [rhoTensor, tensorPower_smul, inv_pow]

-- 先证明任意单比特方向 A 的真实矩阵导数，再实例化两个参数。
theorem unnormalized_derivative_entry (N : ℕ) (A : QMatrix) (b c : Bits N) :
    HasDerivAt (fun t : ℝ => tensorPower N ((1 : QMatrix) + (t : ℂ) • A) b c)
      ((∑ r, onSite N r A) b c) 0 := by
  classical
  have h (r : Fin N) : HasDerivAt
      (fun t : ℝ => ((1 : QMatrix) + (t : ℂ) • A) (b r) (c r))
      (A (b r) (c r)) 0 := by
    convert (hasDerivAt_const (0 : ℝ) ((1 : QMatrix) (b r) (c r))).add
      ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (A (b r) (c r))) using 1 <;> simp <;> rfl
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun r _ => h r)
  simpa [tensorPower, onSite, Matrix.sum_apply, mul_comm] using hp


theorem unnormalized_derivative (N : ℕ) (A : QMatrix) :
    HasDerivAt (fun t : ℝ => tensorPower N ((1 : QMatrix) + (t : ℂ) • A))
      (∑ r, onSite N r A) 0 := by
  apply hasDerivAt_pi.mpr
  intro b
  apply hasDerivAt_pi.mpr
  intro c
  exact unnormalized_derivative_entry N A b c

theorem normalized_derivative (N : ℕ) (A : QMatrix) :
    HasDerivAt (fun t : ℝ => tensorPower N
      ((2 : ℂ)⁻¹ • ((1 : QMatrix) + (t : ℂ) • A)))
      (((2 : ℂ)^N)⁻¹ • (∑ r, onSite N r A)) 0 := by
  apply hasDerivAt_pi.mpr
  intro b
  apply hasDerivAt_pi.mpr
  intro c
  simpa only [tensorPower_smul, inv_pow, Matrix.smul_apply, smul_eq_mul] using
    (unnormalized_derivative_entry N A b c).const_mul (((2 : ℂ)^N)⁻¹)

theorem rhoTensor_hasDerivAt_x (N : ℕ) :
    HasDerivAt (fun x : ℝ => rhoTensor N x 0)
      ((2 / (2 : ℂ)^N) • collectiveX N) 0 := by
  simpa [rhoTensor, rho, collectiveX, collective, smul_smul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using normalized_derivative N sigmaX

theorem rhoTensor_hasDerivAt_y (N : ℕ) :
    HasDerivAt (fun y : ℝ => rhoTensor N 0 y)
      ((2 / (2 : ℂ)^N) • collectiveY N) 0 := by
  simpa [rhoTensor, rho, collectiveY, collective, smul_smul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using normalized_derivative N sigmaY


-- 张量矩阵的迹由真实矩阵元求和计算。
theorem trace_tensorPower (N : ℕ) (A : QMatrix) :
    Matrix.trace (tensorPower N A) = (Matrix.trace A)^N := by
  classical
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  exact (Fintype.sum_pow (fun i : Qubit => A i i) N).symm

@[simp] theorem trace_rho (x y : ℝ) : Matrix.trace (rho x y) = 1 := by
  norm_num [rho, sigmaX, sigmaY, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

@[simp] theorem trace_rhoTensor (N : ℕ) (x y : ℝ) :
    Matrix.trace (rhoTensor N x y) = 1 := by
  simp [rhoTensor, trace_tensorPower]

-- 张量因子为 PSD 时，真实张量幂仍为 PSD。
theorem tensorPower_posSemidef (N : ℕ) (A : QMatrix) (hA : A.PosSemidef) :
    (tensorPower N A).PosSemidef := by
  induction N with
  | zero =>
    have he : tensorPower 0 A = (1 : NMatrix 0) := by
      ext b c
      have he : b = c := Subsingleton.elim _ _
      simp [tensorPower, Matrix.one_apply, he]
    rw [he]
    exact Matrix.PosSemidef.one
  | succ N ih =>
    have he : tensorPower (N+1) A =
        (A ⊗ₖ tensorPower N A).submatrix
          (fun b => (b 0, fun i => b i.succ)) (fun b => (b 0, fun i => b i.succ)) := by
      ext b c
      exact tensorPower_succ N A b c
    rw [he]
    exact (hA.kronecker ih).submatrix _

end CopyQuantumMetrology.TensorModel











