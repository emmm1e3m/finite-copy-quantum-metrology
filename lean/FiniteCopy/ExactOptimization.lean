import FiniteCopy.SchemeBridge
import FiniteCopy.GaussianFisherMember
import FiniteCopy.UniformSupport

open scoped BigOperators Topology ComplexOrder
open MeasureTheory Matrix Filter Asymptotics
noncomputable section
namespace FiniteCopy.Optimization
open CopyQuantumMetrology FiniteCopy.POVM FiniteCopy.Risk FiniteCopy.SeedPOVM

-- 紧凸几何在完整单纯形上运行，种子个数为 d；权重为零表示更小支撑。
theorem exists_optimalScheme (n : ℕ) : Nonempty (OptimalScheme n) := by
  obtain ⟨p, q, lam, hp, hq, hqsum, hmean, hdual, heq⟩ :=
    ConvexRoof.exists_uniform_support (n+1) (by omega) (simplexObjective n)
      (simplexObjective_continuous n).continuousOn
  let S : Scheme n (n+1) :=
    { p := p
      q := q
      p_simplex := hp
      q_nonneg := hq
      q_sum := hqsum
      population_mean := by
        intro i
        simpa only [Nat.cast_add, Nat.cast_one] using hmean i }
  refine ⟨⟨S, lam, hdual, ?_⟩⟩
  rw [← scheme_objective S]
  simpa only [S, dualValue, Nat.cast_add, Nat.cast_one] using heq

def optimalCertificate (n : ℕ) : OptimalScheme n := Classical.choice (exists_optimalScheme n)
def optimalScheme (n : ℕ) : Scheme n (n+1) := (optimalCertificate n).scheme

theorem optimalScheme_totalFisher (n : ℕ) : (optimalScheme n).totalFisher = sectorFisher n := by
  let C := optimalCertificate n
  have hmem : dualValue n C.coefficient ∈ fisherValues n := by
    rw [← C.attained]
    exact scheme_fisher_mem C.scheme
  exact C.attained.trans (sectorFisher_eq_of_certificate n C.coefficient C.majorant hmem).symm

theorem sectorFisher_isGreatest (n : ℕ) : IsGreatest (fisherValues n) (sectorFisher n) := by
  refine ⟨?_, fun r hr => le_csSup (fisherValues_bddAbove n) hr⟩
  rw [← optimalScheme_totalFisher]
  exact scheme_fisher_mem _

theorem commonVarianceRoof_isLeast (n : ℕ) :
    IsLeast (varianceValues n) (commonVarianceRoof n) := by
  let C := optimalCertificate n
  have hV : (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      dualValue n C.coefficient / 4 ∈ varianceValues n := by
    rw [← C.attained]
    simpa only [Scheme.totalFisher, mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ)≠0)] using
      scheme_variance_mem C.scheme
  rw [commonVarianceRoof_eq_of_certificate n C.coefficient C.majorant hV]
  exact least_variance_of_certificate n C.coefficient C.majorant hV

-- 两个独立定义的真实优化对象精确相等，而且最大与最小均取得。
theorem exact_sector_reduction (n : ℕ) :
    sectorFisher n = (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) -
      4 * commonVarianceRoof n := by
  let C := optimalCertificate n
  apply exact_reduction_of_certificate n C.coefficient C.majorant
  · rw [← C.attained]
    exact scheme_fisher_mem C.scheme
  · rw [← C.attained]
    simpa only [Scheme.totalFisher, mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ)≠0)] using
      scheme_variance_mem C.scheme

def finiteSchemeValues (n : ℕ) : Set ℝ := {r | ∃ k, ∃ S : Scheme n k, r = S.totalFisher}

theorem finiteScheme_isGreatest (n : ℕ) : IsGreatest (finiteSchemeValues n) (sectorFisher n) := by
  refine ⟨⟨n+1, optimalScheme n, (optimalScheme_totalFisher n).symm⟩, ?_⟩
  rintro r ⟨k, S, rfl⟩
  exact (sectorFisher_isGreatest n).2 (scheme_fisher_mem S)

theorem optimalScheme_variance (n : ℕ) :
    (2/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - (optimalScheme n).value =
      commonVarianceRoof n := by
  have h := optimalScheme_totalFisher n
  rw [exact_sector_reduction] at h
  unfold Scheme.totalFisher at h
  linarith

theorem roof_lower (n : ℕ) : NHLowerBound.spinL n ≤ commonVarianceRoof n :=
  commonVarianceRoof_ge_spinL n ⟨_, (commonVarianceRoof_isLeast n).1⟩

theorem roof_upper (n : ℕ) : commonVarianceRoof n ≤ actualGaussianVariance n := by
  have hF := gaussianFisher_le_sectorFisher n (epsilon_pos (spinJ_pos n).le)
  rw [exact_sector_reduction] at hF
  have hG := gaussian_fisher_variance (L := n+3) n (epsilon_pos (spinJ_pos n).le)
    (by omega) (by omega)
  change 2 * gaussianFisher n (epsilon (spinJ n)) =
    (8/3 : ℝ) * ((n : ℝ)/2) * ((n : ℝ)/2+1) - 4 * actualGaussianVariance n at hG
  linarith

theorem commonVarianceRoof_ratio_limit :
    Tendsto (fun n : ℕ => commonVarianceRoof n / n) atTop (𝓝 (1/4 : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le GaussianLimit.actual_lower_limit
    MainTheorem.actualVariance_ratio_limit
  · intro n
    exact div_le_div_of_nonneg_right (roof_lower n) (Nat.cast_nonneg n)
  · intro n
    exact div_le_div_of_nonneg_right (roof_upper n) (Nat.cast_nonneg n)

theorem commonVarianceRoof_littleO :
    (fun n => commonVarianceRoof n - (n : ℝ)/4) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · have h := commonVarianceRoof_ratio_limit.sub_const (1/4)
    norm_num only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    intro hz
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact False.elim (hn0 hz)

end FiniteCopy.Optimization
