import FiniteCopy.QuantumModel
import FiniteCopy.Phase

open scoped BigOperators ComplexOrder
open MeasureTheory Matrix Complex

noncomputable section
namespace CopyQuantumMetrology

variable {n L : ℕ} [NeZero L]

-- 实际自旋 j=n/2 的相邻跃迁系数；坐标为 m=i-n/2。
def spinCoefficient (n : ℕ) (r : Fin n) : ℝ :=
  Real.sqrt (((r : ℕ) + 1 : ℝ) * ((n : ℝ) - (r : ℕ)))

def raisingMatrix (c : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ∑ r : Fin n, Matrix.single r.succ r.castSucc (c r : ℂ)

def loweringMatrix (c : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ∑ r : Fin n, Matrix.single r.castSucc r.succ (c r : ℂ)

def spinX (c : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (2 : ℂ)⁻¹ • (raisingMatrix c + loweringMatrix c)

def spinY (c : Fin n → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (-Complex.I / 2) • (raisingMatrix c - loweringMatrix c)

def seedMass (v : Fin (n+1) → ℝ) : ℝ := ∑ i, v i ^ 2

def seedMoment (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) : ℝ :=
  ∑ r, c r * v r.castSucc * v r.succ

def spinFrequency (i : Fin (n+1)) : ZMod L := -(i.val : ZMod L)

def phaseVector (v : Fin (n+1) → ℝ) (k : ZMod L) : Fin (n+1) → ℂ :=
  rotatedSeed (fun i => (v i : ℂ)) spinFrequency k

lemma quadratic_raising (c : Fin n → ℝ) (v : Fin (n+1) → ℂ) :
    quadratic (raisingMatrix c) v = ∑ r, (c r : ℂ) * v r.castSucc * star (v r.succ) := by
  rw [← trace_mul_rankOne]
  simp only [raisingMatrix, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma quadratic_lowering (c : Fin n → ℝ) (v : Fin (n+1) → ℂ) :
    quadratic (loweringMatrix c) v = ∑ r, (c r : ℂ) * v r.succ * star (v r.castSucc) := by
  rw [← trace_mul_rankOne]
  simp only [loweringMatrix, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma phaseVector_adjacent (v : Fin (n+1) → ℝ) (k : ZMod L) (r : Fin n) :
    phaseVector v k r.castSucc * star (phaseVector v k r.succ) =
      ZMod.stdAddChar k * (v r.castSucc * v r.succ : ℝ) := by
  have he : spinFrequency (L := L) r.castSucc - spinFrequency r.succ = 1 := by
    simp [spinFrequency, Fin.val_succ, Nat.cast_add]
  change (phase k (spinFrequency r.castSucc) * (v r.castSucc : ℂ)) *
      star (phase k (spinFrequency r.succ) * (v r.succ : ℂ)) = _
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (phase k (spinFrequency r.castSucc) * star (phase k (spinFrequency r.succ))) *
        (v r.castSucc : ℂ) * (v r.succ : ℂ) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [phase_product, he]; simp [phase]; push_cast; ring

lemma quadratic_raising_phase (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) (k : ZMod L) :
    quadratic (raisingMatrix c) (phaseVector v k) =
      (seedMoment c v : ℂ) * ZMod.stdAddChar k := by
  rw [quadratic_raising]
  simp_rw [mul_assoc, phaseVector_adjacent]
  simp only [seedMoment, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma quadratic_lowering_phase (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) (k : ZMod L) :
    quadratic (loweringMatrix c) (phaseVector v k) =
      (seedMoment c v : ℂ) * star (ZMod.stdAddChar k) := by
  have h := congrArg star (quadratic_raising_phase c v k)
  rw [quadratic_raising] at h
  simp only [star_sum, star_mul, star_star, Complex.star_def, Complex.conj_ofReal, map_map, Complex.conj_conj] at h
  rw [quadratic_lowering]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro r hr
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  · simp only [Complex.star_def]
    ring

lemma quadratic_add (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (v : Fin (n+1) → ℂ) : quadratic (A+B) v = quadratic A v + quadratic B v := by
  simp [quadratic, mul_add, add_mul, Finset.sum_add_distrib]

lemma quadratic_sub (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (v : Fin (n+1) → ℂ) : quadratic (A-B) v = quadratic A v - quadratic B v := by
  simp [quadratic, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma quadratic_smul (a : ℂ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (v : Fin (n+1) → ℂ) : quadratic (a • A) v = a * quadratic A v := by
  simp only [quadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem spinX_phase_quadratic (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) (k : ZMod L) :
    (quadratic (spinX c) (phaseVector v k)).re = seedMoment c v * PhaseMoments.cx k := by
  rw [spinX, quadratic_smul, quadratic_add, quadratic_raising_phase, quadratic_lowering_phase]
  simp [PhaseMoments.cx, Complex.mul_re, Complex.inv_re, Complex.normSq_ofNat]
  <;> ring

theorem spinY_phase_quadratic (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) (k : ZMod L) :
    (quadratic (spinY c) (phaseVector v k)).re = seedMoment c v * PhaseMoments.cy k := by
  rw [spinY, quadratic_smul, quadratic_sub, quadratic_raising_phase, quadratic_lowering_phase]
  simp [PhaseMoments.cy, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.normSq_ofNat]
  <;> ring

theorem phaseVector_mass (v : Fin (n+1) → ℝ) (k : ZMod L) :
    vectorMass (phaseVector v k) = seedMass v := by
  simp [vectorMass, seedMass, phaseVector, rotatedSeed, phase,
    Complex.normSq_mul, ZMod.stdAddChar_apply, Complex.normSq_ofReal, pow_two]

end CopyQuantumMetrology


