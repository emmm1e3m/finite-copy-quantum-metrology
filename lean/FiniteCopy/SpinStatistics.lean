import FiniteCopy.SpinPhase

open scoped BigOperators ComplexOrder
open MeasureTheory Matrix Complex
noncomputable section
namespace CopyQuantumMetrology
variable {n L : ℕ} [NeZero L]

-- Bool 的 false/true 分别对应 x/y 坐标。
def phaseDirection (k : ZMod L) (b : Bool) : ℝ :=
  if b then PhaseMoments.cy k else PhaseMoments.cx k

def spinObservable (c : Fin n → ℝ) (b : Bool) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  if b then spinY c else spinX c

def spinReference (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  ((n+1 : ℝ)⁻¹) • 1

def spinTangent (c : Fin n → ℝ) (b : Bool) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (2 / (n+1 : ℝ)) • spinObservable c b

def seedPhaseEffect (v : Fin (n+1) → ℝ) (k : ZMod L) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  effect (fun i => (v i : ℂ)) spinFrequency k

def phaseScore (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) (k : ZMod L) (b : Bool) : ℝ :=
  2 * seedMoment c v / seedMass v * phaseDirection k b

def phaseProbability (v : Fin (n+1) → ℝ) : ℝ := seedMass v / ((L : ℝ) * (n+1))

def seedFisher (c : Fin n → ℝ) (v : Fin (n+1) → ℝ) : ℝ :=
  2 * seedMoment c v ^ 2 / ((n+1 : ℝ) * seedMass v)

lemma born_smul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ E : Matrix ι ι ℂ) (a : ℝ) : born ρ (a • E) = a * born ρ E := by
  simp only [born, Matrix.mul_smul, Matrix.trace_smul]
  change RCLike.re (a • Matrix.trace (ρ * E)) = _
  rw [RCLike.smul_re]
  rfl

lemma seedPhaseEffect_eq (v : Fin (n+1) → ℝ) (k : ZMod L) :
    seedPhaseEffect v k = (L : ℝ)⁻¹ • rankOne (phaseVector v k) := rfl

lemma spinObservable_quadratic (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (k : ZMod L) (b : Bool) :
    (quadratic (spinObservable c b) (phaseVector v k)).re =
      seedMoment c v * phaseDirection k b := by
  cases b
  · exact spinX_phase_quadratic c v k
  · exact spinY_phase_quadratic c v k

-- 概率与切向均由实际复矩阵迹计算。
theorem spin_born_reference (v : Fin (n+1) → ℝ) (k : ZMod L) :
    born (spinReference n) (seedPhaseEffect v k) = phaseProbability (L := L) v := by
  rw [seedPhaseEffect_eq, born_smul_right]
  simp only [spinReference, born_maximallyMixed_rankOne, phaseVector_mass, phaseProbability]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem spin_born_tangent (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (k : ZMod L) (b : Bool) :
    born (spinTangent c b) (seedPhaseEffect v k) =
      2 * seedMoment c v * phaseDirection k b / ((L : ℝ) * (n+1)) := by
  rw [seedPhaseEffect_eq, born_smul_right]
  simp only [spinTangent, born_tangent_rankOne, spinObservable_quadratic]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem spin_born_score (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (hv : seedMass v ≠ 0) (k : ZMod L) (b : Bool) :
    born (spinTangent c b) (seedPhaseEffect v k) /
      born (spinReference n) (seedPhaseEffect v k) = phaseScore c v k b := by
  rw [spin_born_reference, spin_born_tangent]
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  dsimp [phaseProbability, phaseScore]
  field_simp

theorem phaseDirection_sum (hL : 3 ≤ L) (b : Bool) :
    ∑ k : ZMod L, phaseDirection k b = 0 := by
  cases b
  · exact PhaseMoments.cx_sum hL
  · exact PhaseMoments.cy_sum hL

theorem phaseDirection_second (hL : 3 ≤ L) (a b : Bool) :
    ∑ k : ZMod L, phaseDirection k a * phaseDirection k b =
      if a = b then (L : ℝ) / 2 else 0 := by
  cases a <;> cases b
  · simpa [phaseDirection, ← sq] using PhaseMoments.cx_square_sum hL
  · simpa [phaseDirection] using PhaseMoments.cx_cy_sum hL
  · simpa [phaseDirection, mul_comm] using PhaseMoments.cx_cy_sum hL
  · simpa [phaseDirection, ← sq] using PhaseMoments.cy_square_sum hL

-- 相位消去在逐个连续标签上成立，因此无需假设待证的积分均值。
theorem phaseScore_mean (hL : 3 ≤ L) (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (b : Bool) : ∑ k : ZMod L, phaseProbability (L := L) v * phaseScore c v k b = 0 := by
  simp only [phaseScore, ← mul_assoc, ← Finset.mul_sum, phaseDirection_sum hL, mul_zero]

theorem phaseScore_second (hL : 3 ≤ L) (c : Fin n → ℝ) (v : Fin (n+1) → ℝ)
    (hv : seedMass v ≠ 0) (a b : Bool) :
    ∑ k : ZMod L, phaseProbability (L := L) v * phaseScore c v k a * phaseScore c v k b =
      if a = b then seedFisher c v else 0 := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have he (k : ZMod L) :
      phaseProbability (L := L) v * phaseScore c v k a * phaseScore c v k b =
      (phaseProbability (L := L) v * (2 * seedMoment c v / seedMass v)^2) *
        (phaseDirection k a * phaseDirection k b) := by
    dsimp [phaseScore]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, phaseDirection_second hL]
  by_cases hab : a = b
  · simp only [hab, ite_true, seedFisher, phaseProbability]
    field_simp
    <;> ring
  · simp [hab]

lemma spinCoefficient_pos (r : Fin n) : 0 < spinCoefficient n r := by
  apply Real.sqrt_pos.2
  have hr : (r.val : ℝ) < n := by exact_mod_cast r.isLt
  positivity

lemma seedMass_pos (v : Fin (n+1) → ℝ) (hv : ∀ i, 0 < v i) : 0 < seedMass v := by
  apply Finset.sum_pos
  · intro i hi
    exact sq_pos_of_pos (hv i)
  · exact Finset.univ_nonempty

lemma seedMoment_pos (hn : 0 < n) (v : Fin (n+1) → ℝ) (hv : ∀ i, 0 < v i) :
    0 < seedMoment (spinCoefficient n) v := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply Finset.sum_pos
  · intro r hr
    exact mul_pos (mul_pos (spinCoefficient_pos r) (hv r.castSucc)) (hv r.succ)
  · exact Finset.univ_nonempty

lemma spin_seedFisher_pos (hn : 0 < n) (v : Fin (n+1) → ℝ)
    (hv : ∀ i, 0 < v i) : 0 < seedFisher (spinCoefficient n) v := by
  dsimp [seedFisher]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos (seedMoment_pos hn v hv)))
    (mul_pos (by positivity) (seedMass_pos v hv))

end CopyQuantumMetrology

