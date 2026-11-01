import FiniteCopy.SchemeBridge
open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.SeedPOVM

def rawSeed {n k : ℕ} (S : Scheme n k) (a : Fin k) (i : Fin (n+1)) : ℝ :=
  Real.sqrt ((n+1 : ℝ) * S.q a) * S.amplitude a i

lemma rawSeed_sq {n k : ℕ} (S : Scheme n k) (a : Fin k) (i : Fin (n+1)) :
    rawSeed S a i ^ 2 = (n+1) * S.q a * S.p a i := by
  rw [rawSeed, mul_pow, Real.sq_sqrt (mul_nonneg (by positivity) (S.q_nonneg a)),
    S.amplitude_sq]

lemma rawSeed_nonneg {n k : ℕ} (S : Scheme n k) (a : Fin k) (i : Fin (n+1)) :
    0 ≤ rawSeed S a i := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma rawSeed_complete {n k : ℕ} (S : Scheme n k) (i : Fin (n+1)) :
    (∑ a, rawSeed S a i ^ 2) = 1 := by
  simp_rw [rawSeed_sq, mul_assoc]
  rw [← Finset.mul_sum, S.population_mean]
  field_simp

lemma rawSeed_mass {n k : ℕ} (S : Scheme n k) (a : Fin k) :
    seedMass (rawSeed S a) = (n+1) * S.q a := by
  unfold seedMass
  simp_rw [rawSeed_sq]
  rw [← Finset.mul_sum, (S.p_simplex a).2, mul_one]

lemma rawSeed_moment {n k : ℕ} (S : Scheme n k) (a : Fin k) :
    seedMoment (spinCoefficient n) (rawSeed S a) = (n+1) * S.q a * S.gamma a := by
  simp only [Scheme.gamma, seedMoment]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hs := Real.sq_sqrt (mul_nonneg (by positivity : (0 : ℝ) ≤ n+1) (S.q_nonneg a))
  dsimp [rawSeed]
  calc
    _ = (Real.sqrt ((n+1 : ℝ) * S.q a))^2 *
      (spinCoefficient n r * S.amplitude a r.castSucc * S.amplitude a r.succ) := by ring
    _ = _ := by rw [hs]

def rawSeedFisher {n k : ℕ} (v : Fin k → Fin (n+1) → ℝ) : ℝ :=
  (4/(n+1 : ℝ)) * ∑ a, seedMoment (spinCoefficient n) (v a)^2 / seedMass (v a)

lemma rawSeedFisher_eq {n k : ℕ} (S : Scheme n k) :
    rawSeedFisher (rawSeed S) = S.totalFisher := by
  have he (a : Fin k) : seedMoment (spinCoefficient n) (rawSeed S a)^2 /
      seedMass (rawSeed S a) = (n+1) * (S.q a * S.gamma a^2) := by
    rw [rawSeed_mass, rawSeed_moment]
    by_cases hq : S.q a = 0
    · simp [hq]
    · have hd : (n+1 : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring
  simp_rw [rawSeedFisher, he]
  rw [← Finset.mul_sum]
  unfold Scheme.totalFisher Scheme.value
  field_simp

def realRankOne {n : ℕ} (v : Fin (n+1) → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  rankOne (fun i => (v i : ℂ))

lemma realRankOne_positive {n : ℕ} (v : Fin (n+1) → ℝ) : (realRankOne v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

lemma realRankOne_trace {n : ℕ} (v : Fin (n+1) → ℝ) : traceReal (realRankOne v) = seedMass v := by
  unfold traceReal realRankOne
  rw [trace_rankOne]
  simp [vectorMass, seedMass, Complex.normSq_ofReal, sq]

lemma realRankOne_coherence {n : ℕ} (v : Fin (n+1) → ℝ) :
    coherence n (Algebra.spinEdge n) (realRankOne v) =
      (seedMoment (spinCoefficient n) v : ℂ) := by
  unfold coherence seedMoment
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  have h0 : vertex n r.val = r.castSucc := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (Nat.le_of_lt r.isLt)]
  have h1 : vertex n (r.val+1) = r.succ := by
    apply Fin.ext
    simp [vertex, Nat.min_eq_left (show r.val+1 ≤ n by omega)]
  rw [h0, h1]
  simp [realRankOne, rankOne, Matrix.vecMulVec_apply, Pi.star_apply,
    spinCoefficient_eq_spinEdge, mul_assoc]

lemma realRankOne_fisher {n : ℕ} (v : Fin (n+1) → ℝ) :
    fisherDensity n (Algebra.spinEdge n) (realRankOne v) =
      (4/(n+1 : ℝ)) * seedMoment (spinCoefficient n) v^2 / seedMass v := by
  rw [fisherDensity_formula _ _ _ (realRankOne_positive v).isHermitian,
    realRankOne_trace, realRankOne_coherence, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp

-- 原始非负列方案，允许零列并将零质量的商按实除法解释为零。
def rawSeedValues (n : ℕ) : Set ℝ :=
  {r | ∃ k, ∃ v : Fin k → Fin (n+1) → ℝ,
    (∀ a i, 0 ≤ v a i) ∧ (∀ i, ∑ a, v a i ^ 2 = 1) ∧ r = rawSeedFisher v}

theorem rawSeedValue_le_dual (n : ℕ) (lam : Fin (n+1) → ℝ)
    (hlam : IsDualCertificate n lam) (r : ℝ) (hr : r ∈ rawSeedValues n) :
    r ≤ dualValue n lam := by
  obtain ⟨k, v, hv, hc, rfl⟩ := hr
  have hb (a : Fin k) := psd_fisher_le_dual n lam hlam (realRankOne (v a))
    (realRankOne_positive (v a))
  simp_rw [realRankOne_fisher] at hb
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hb a)
  have hl : (∑ a, (4/(n+1 : ℝ)) * seedMoment (spinCoefficient n) (v a)^2 /
      seedMass (v a)) = rawSeedFisher v := by
    unfold rawSeedFisher
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum]
  have hr : (∑ a, (∑ i, lam i * (realRankOne (v a) i i).re) / (n+1)) = dualValue n lam := by
    rw [← Finset.sum_div, Finset.sum_comm]
    unfold dualValue
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [realRankOne, rankOne, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp_rw [← sq]
    rw [← Finset.mul_sum, hc, mul_one]
  rwa [hl, hr] at h

end FiniteCopy.Optimization
