import FiniteCopy.GaussianLimit

open scoped Topology
noncomputable section
namespace CopyQuantumMetrology.GaussianLimit

-- 将实际有限误差预算整理为论文中的四项界，统一常数可取40000。
theorem totalBudget_le_paper {J eps delta : ℝ}
    (hJ : 1 ≤ J) (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) :
    totalBudget J eps delta ≤ 40000 *
      ((1 / eps^7) * (delta + 1/J) +
       (1/(eps^2*delta^6) + 1/(eps^12*delta^4)) / Real.sqrt J +
       (1+Real.log (2*J))/J) := by
  have hJp : 0 < J := by linarith
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJp
  have hs1 : 1 ≤ Real.sqrt J := by simpa using Real.sqrt_le_sqrt hJ
  have hss := Real.sq_sqrt hJp.le
  have hsJ : Real.sqrt J ≤ J := by nlinarith
  have he27 : 1/eps^2 ≤ 1/eps^7 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_of_le_one he.le he1 (by omega))
  have he7 : 1 ≤ 1/eps^7 := by
    apply (le_div_iff₀ (by positivity : 0 < eps^7)).mpr
    simpa using pow_le_one₀ he.le he1 (n := 7)
  have hed7 : eps^12*delta^4 ≤ eps^7 :=
    (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hd.le hd1)).trans
      (pow_le_pow_of_le_one he.le he1 (by omega))
  have hed6 : eps^12*delta^4 ≤ eps^6*delta^2 := by
    exact mul_le_mul (pow_le_pow_of_le_one he.le he1 (by omega))
      (pow_le_pow_of_le_one hd.le hd1 (by omega)) (by positivity) (by positivity)
  let A := 1/(eps^2*delta^6*Real.sqrt J)
  let B := 1/(eps^12*delta^4*Real.sqrt J)
  let E := (1/eps^7)*(delta+1/J)
  let H := (1+Real.log (2*J))/J
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hl : 0 ≤ Real.log (2*J) := Real.log_nonneg (by linarith)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hg7 : 1/(eps^7*Real.sqrt J) ≤ B := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right hed7 hs.le
  have hg6 : 1/(eps^6*delta^2*Real.sqrt J) ≤ B := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right hed6 hs.le
  have hgJ : 1/(J*eps^12*delta^4) ≤ B := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hsJ (by positivity : 0 ≤ eps^12*delta^4)]
  have hdiff : differenceBudget J eps delta =
      4096/(eps^7*Real.sqrt J) +
      16384*(1/(J*eps^12*delta^4)+B) := by
    dsimp [differenceBudget, B]
    field_simp
    nlinarith [hss]
  have hgrad : differenceBudget J eps delta + 64/(eps^6*delta^2*Real.sqrt J) ≤
      36928*B := by
    rw [hdiff]
    simp only [div_eq_mul_inv, one_mul] at hg7 hg6 hgJ ⊢
    linarith only [hg7, hg6, hgJ]
  have hep : endpointBudget J eps delta ≤ 8212*E := by
    have hc : 14/eps^2+2+2*(4096/eps^7+2) ≤ 8212*(1/eps^7) := by
      simp only [div_eq_mul_inv, one_mul] at he27 he7 ⊢
      linarith only [he27, he7]
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ delta+1/J)
    dsimp [endpointBudget, E]
    nlinarith only [hm]
  have hmesh : 7/(4*J)+2*(1+Real.log (2*J))/J ≤ (15/4)*H := by
    have hm : (7/4 : ℝ)+2*(1+Real.log (2*J)) ≤ (15/4)*(1+Real.log (2*J)) := by
      linarith
    dsimp only [H]
    convert div_le_div_of_nonneg_right hm hJp.le using 1 <;> ring
  have htotal : totalBudget J eps delta ≤ 6000*A+36928*B+8212*E+(15/4)*H := by
    have hi : 6000/(eps^2*delta^6*Real.sqrt J) = 6000*A := by dsimp [A]; ring
    rw [totalBudget, hi]
    linarith only [hgrad, hep, hmesh]
  have heq : (1 / eps^7) * (delta + 1/J) +
       (1/(eps^2*delta^6) + 1/(eps^12*delta^4)) / Real.sqrt J +
       (1+Real.log (2*J))/J = E+A+B+H := by dsimp [E,A,B,H]; ring
  rw [heq]
  linarith

theorem actual_paper_uniform_error {n : ℕ} {eps delta : ℝ}
    (hn : 1 ≤ n) (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hlargeE : 1/eps ≤ spinJ n) (hlargeD : 1 ≤ spinJ n*delta) :
    |ContinuousEnergy.U n eps / spinJ n - Real.sqrt (1+eps^2)/2| ≤ 40000 *
      ((1 / eps^7) * (delta + 1/spinJ n) +
       (1/(eps^2*delta^6) + 1/(eps^12*delta^4)) / Real.sqrt (spinJ n) +
       (1+Real.log (2*spinJ n))/spinJ n) := by
  apply (actual_total_error hn he he1 hd hd1 hlargeE hlargeD).trans
  apply totalBudget_le_paper _ he he1 hd hd1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [spinJ]
  linarith

end CopyQuantumMetrology.GaussianLimit
