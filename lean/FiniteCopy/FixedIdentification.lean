import FiniteCopy.FixedAssembly
open scoped BigOperators
namespace CopyQuantumMetrology.FixedWidth

lemma width_regularized_eq (J eps m : ℝ) :
    width (GlobalBounds.regularizedWidth eps) J m=Width.width J eps m :=
  (GaussianLimit.width_eq_global J eps m).symm

lemma I_regularized_eq (n : ℕ) (eps : ℝ) (i : ℕ) (hi : i ≤ n) :
    I (GlobalBounds.regularizedWidth eps) (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)=
      ContinuousEnergy.I n eps i := by
  rw [GaussianLimit.I_eq_regularized n eps i hi]
  simp only [I,v,width_regularized_eq,GaussianLimit.spinJ_eq]

lemma G_regularized_eq (n : ℕ) (eps : ℝ) (i : ℕ) (hi : i < n) :
    G (GlobalBounds.regularizedWidth eps) (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)=
      ContinuousEnergy.G n eps i := by
  rw [GaussianLimit.G_eq_regularized n eps i hi]
  simp only [G,v,width_regularized_eq,GaussianLimit.spinJ_eq]

-- 一般b的U在正则化宽度上严格等于已有实际U，验证定义与旧测量链一致。
theorem U_regularized_eq (n : ℕ) (eps : ℝ) :
    U (GlobalBounds.regularizedWidth eps) n=ContinuousEnergy.U n eps := by
  have hi : (∑ i ∈ Finset.range (n+1), I (GlobalBounds.regularizedWidth eps) (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))=
      ∑ i ∈ Finset.range (n+1), ContinuousEnergy.I n eps i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact I_regularized_eq n eps i (by simpa using hi)
  have hg : (∑ i ∈ Finset.range n, G (GlobalBounds.regularizedWidth eps) (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))=
      ∑ i ∈ Finset.range n, ContinuousEnergy.G n eps i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact G_regularized_eq n eps i (by simpa using hi)
  have hr : (∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))=
      ∑ i ∈ Finset.range (n+1), ContinuousEnergy.R n i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (GaussianLimit.R_eq_correction n i (by simpa using hi)).symm
  unfold U ContinuousEnergy.U
  rw [hi,hg,hr]
  simp only [Nat.cast_add,Nat.cast_one]

end CopyQuantumMetrology.FixedWidth
