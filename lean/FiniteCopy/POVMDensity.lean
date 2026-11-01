import Mathlib
import FiniteCopy.RiskTerminal

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder Topology Classical

noncomputable section
namespace FiniteCopy.Risk

/-- 普通矩阵值 POVM：可数可加性包含在 VectorMeasure 中，未预设密度。 -/
structure OperatorPOVM (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] where
  measure : VectorMeasure Ω (Matrix ι ι ℂ)
  positive : ∀ s, MeasurableSet s → (measure s).PosSemidef
  normalized : measure Set.univ = 1

namespace OperatorPOVM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- 任意通常的集合函数只需在可测集合上满足 POVM 公理。 -/
def ofSetFunction (F : Set Ω → Matrix ι ι ℂ) (h0 : F ∅ = 0)
    (hp : ∀ s, MeasurableSet s → (F s).PosSemidef) (h1 : F Set.univ = 1)
    (hadd : ∀ s : ℕ → Set Ω, (∀ k, MeasurableSet (s k)) →
      Pairwise (fun i j => Disjoint (s i) (s j)) → HasSum (fun k => F (s k)) (F (⋃ k, s k))) :
    OperatorPOVM ι Ω where
  measure := {
    measureOf' := fun s => if MeasurableSet s then F s else 0
    empty' := by simp [h0]
    not_measurable' := by intro s hs; simp [hs]
    m_iUnion' := by
      intro s hs hd
      simpa only [hs, ite_true, MeasurableSet.iUnion hs] using hadd s hs hd }
  positive := by
    intro s hs
    change (if MeasurableSet s then F s else 0).PosSemidef
    simpa only [ite_eq_left hs] using hp s hs
  normalized := by
    change (if MeasurableSet Set.univ then F Set.univ else 0) = 1
    simpa only [ite_eq_left MeasurableSet.univ] using h1

theorem ofSetFunction_apply (F : Set Ω → Matrix ι ι ℂ) (h0 hp h1 hadd)
    (s : Set Ω) (hs : MeasurableSet s) :
    (ofSetFunction F h0 hp h1 hadd).measure s = F s := by
  exact ite_eq_left hs

def entryHom (i j : ι) : Matrix ι ι ℂ →+ ℂ where
  toFun A := A i j
  map_zero' := rfl
  map_add' _ _ := rfl

def entryMeasure (M : OperatorPOVM ι Ω) (i j : ι) : ComplexMeasure Ω :=
  M.measure.mapRange (entryHom i j) (by exact (continuous_apply j).comp (continuous_apply i))

@[simp] theorem entryMeasure_apply (M : OperatorPOVM ι Ω) (i j : ι) (s : Set Ω) :
    entryMeasure M i j s = M.measure s i j := rfl

/-- 有限个实、虚条目总变差的和，自动为有限标量测度。 -/
def dominatingMeasure (M : OperatorPOVM ι Ω) : Measure Ω :=
  ∑ i, ∑ j, ((entryMeasure M i j).re.totalVariation + (entryMeasure M i j).im.totalVariation)

instance dominatingMeasure_finite (M : OperatorPOVM ι Ω) : IsFiniteMeasure M.dominatingMeasure := by
  unfold dominatingMeasure
  infer_instance

theorem variation_re_le (M : OperatorPOVM ι Ω) (i j : ι) :
    (entryMeasure M i j).re.totalVariation ≤ M.dominatingMeasure := by
  apply (le_add_of_nonneg_right (Measure.zero_le (entryMeasure M i j).im.totalVariation)).trans
  unfold dominatingMeasure
  exact (Finset.single_le_sum (fun k _ => (show 0 ≤
    ((entryMeasure M i k).re.totalVariation + (entryMeasure M i k).im.totalVariation) from Measure.zero_le _))
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Measure.zero_le (∑ l,
      ((entryMeasure M k l).re.totalVariation + (entryMeasure M k l).im.totalVariation)))
      (Finset.mem_univ i))

theorem variation_im_le (M : OperatorPOVM ι Ω) (i j : ι) :
    (entryMeasure M i j).im.totalVariation ≤ M.dominatingMeasure := by
  apply (le_add_of_nonneg_left (Measure.zero_le (entryMeasure M i j).re.totalVariation)).trans
  unfold dominatingMeasure
  exact (Finset.single_le_sum (fun k _ => (show 0 ≤
    ((entryMeasure M i k).re.totalVariation + (entryMeasure M i k).im.totalVariation) from Measure.zero_le _))
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Measure.zero_le (∑ l,
      ((entryMeasure M k l).re.totalVariation + (entryMeasure M k l).im.totalVariation)))
      (Finset.mem_univ i))

theorem signed_integral_rnDeriv (s : SignedMeasure Ω) (μ : Measure Ω) [SigmaFinite μ]
    (hle : s.totalVariation ≤ μ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ z in A, s.rnDeriv μ z ∂μ) = s A := by
  have hac : s ≪ᵥ μ.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    exact hle.absolutelyContinuous
  have h := congrArg (fun v : SignedMeasure Ω => v A)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq s μ hac)
  rwa [MeasureTheory.withDensityᵥ_apply (s.integrable_rnDeriv μ) hA] at h

def rawDensity (M : OperatorPOVM ι Ω) (z : Ω) : Matrix ι ι ℂ :=
  fun i j => (entryMeasure M i j).rnDeriv M.dominatingMeasure z

theorem rawDensity_integrable (M : OperatorPOVM ι Ω) (i j : ι) :
    Integrable (fun z => M.rawDensity z i j) M.dominatingMeasure :=
  ComplexMeasure.integrable_rnDeriv _ _

theorem rawDensity_integral (M : OperatorPOVM ι Ω) (A : Set Ω) (hA : MeasurableSet A)
    (i j : ι) : (∫ z in A, M.rawDensity z i j ∂M.dominatingMeasure) = M.measure A i j := by
  apply Complex.ext
  · calc
      (∫ z in A, M.rawDensity z i j ∂M.dominatingMeasure).re =
          ∫ z in A, (M.rawDensity z i j).re ∂M.dominatingMeasure :=
        (integral_re (M.rawDensity_integrable i j).integrableOn).symm
      _ = (M.measure A i j).re :=
        signed_integral_rnDeriv _ _ (M.variation_re_le i j) A hA
  · calc
      (∫ z in A, M.rawDensity z i j ∂M.dominatingMeasure).im =
          ∫ z in A, (M.rawDensity z i j).im ∂M.dominatingMeasure :=
        (integral_im (M.rawDensity_integrable i j).integrableOn).symm
      _ = (M.measure A i j).im :=
        signed_integral_rnDeriv _ _ (M.variation_im_le i j) A hA

theorem rawDensity_hermitian_ae (M : OperatorPOVM ι Ω) :
    ∀ᵐ z ∂M.dominatingMeasure, (M.rawDensity z).IsHermitian := by
  have hij (i j : ι) : (fun z => star (M.rawDensity z j i)) =ᵐ[M.dominatingMeasure]
      (fun z => M.rawDensity z i j) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq
    · exact Complex.conjCLE.integrable_comp_iff.mpr (M.rawDensity_integrable j i)
    · exact M.rawDensity_integrable i j
    · intro A hA hfin
      simp only [Complex.star_def]
      rw [integral_conj, M.rawDensity_integral A hA j i, M.rawDensity_integral A hA i j]
      exact congrFun (congrFun (M.positive A hA).isHermitian i) j
  have hall : ∀ᵐ z ∂M.dominatingMeasure, ∀ i j, star (M.rawDensity z j i) = M.rawDensity z i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hij i j
  filter_upwards [hall] with z hz
  ext i j
  exact hz i j

def quadratic (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℂ := star x ⬝ᵥ (A *ᵥ x)

theorem quadratic_integrable (M : OperatorPOVM ι Ω) (x : ι → ℂ) :
    Integrable (fun z => quadratic (M.rawDensity z) x) M.dominatingMeasure := by
  simp only [quadratic, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => ((M.rawDensity_integrable i j).mul_const (x j)).const_mul (star (x i))))

theorem quadratic_integral (M : OperatorPOVM ι Ω) (x : ι → ℂ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ z in A, quadratic (M.rawDensity z) x ∂M.dominatingMeasure) = quadratic (M.measure A) x := by
  have hint (i j : ι) : Integrable (fun z => star (x i) * (M.rawDensity z i j * x j))
      (M.dominatingMeasure.restrict A) :=
    ((M.rawDensity_integrable i j).integrableOn.mul_const _).const_mul _
  simp only [quadratic, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, integral_mul_const, M.rawDensity_integral A hA]
    · intro j hj
      exact hint i j
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => hint i j)

theorem quadratic_re_nonneg_ae (M : OperatorPOVM ι Ω) (x : ι → ℂ) :
    ∀ᵐ z ∂M.dominatingMeasure, 0 ≤ (quadratic (M.rawDensity z) x).re := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (M.quadratic_integrable x).re
  intro A hA hfin
  rw [integral_re (M.quadratic_integrable x).integrableOn, M.quadratic_integral x A hA]
  exact (Complex.nonneg_iff.mp ((M.positive A hA).dotProduct_mulVec_nonneg x)).1

/-- 可数稠密测试向量给同一个满测度集，连续性再推广到全部向量。 -/
theorem rawDensity_positive_ae (M : OperatorPOVM ι Ω) :
    ∀ᵐ z ∂M.dominatingMeasure, (M.rawDensity z).PosSemidef := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (ι → ℂ)
  have hall : ∀ᵐ z ∂M.dominatingMeasure, ∀ k : ℕ, 0 ≤ (quadratic (M.rawDensity z) (d k)).re :=
    ae_all_iff.mpr fun k => M.quadratic_re_nonneg_ae (d k)
  filter_upwards [hall, M.rawDensity_hermitian_ae] with z hz hh
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro x
  apply Complex.nonneg_iff.mpr
  constructor
  · have hc : IsClosed {x : ι → ℂ | 0 ≤ (quadratic (M.rawDensity z) x).re} := by
      apply isClosed_le continuous_const
      unfold quadratic dotProduct mulVec
      simp only [Pi.star_apply]
      fun_prop
    exact isClosed_property hd hc hz x
  · have h := congrArg Complex.im (hh.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith

/-- 在唯一坏零集上置零，得到处处 PSD 的真实密度。 -/
def density (M : OperatorPOVM ι Ω) (z : Ω) : Matrix ι ι ℂ :=
  if (M.rawDensity z).PosSemidef then M.rawDensity z else 0

theorem density_positive (M : OperatorPOVM ι Ω) (z : Ω) : (M.density z).PosSemidef := by
  unfold density
  split_ifs with h
  · exact h
  · exact Matrix.PosSemidef.zero

theorem density_ae_eq (M : OperatorPOVM ι Ω) : M.density =ᵐ[M.dominatingMeasure] M.rawDensity := by
  filter_upwards [M.rawDensity_positive_ae] with z hz
  simp [density, hz]

theorem density_integrable (M : OperatorPOVM ι Ω) (i j : ι) :
    Integrable (fun z => M.density z i j) M.dominatingMeasure := by
  apply (M.rawDensity_integrable i j).congr
  filter_upwards [M.density_ae_eq] with z hz
  exact congrFun (congrFun hz.symm i) j

theorem density_integral (M : OperatorPOVM ι Ω) (A : Set Ω) (hA : MeasurableSet A) (i j : ι) :
    (∫ z in A, M.density z i j ∂M.dominatingMeasure) = M.measure A i j := by
  calc
    _ = ∫ z in A, M.rawDensity z i j ∂M.dominatingMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae M.density_ae_eq] with z hz
      exact congrFun (congrFun hz i) j
    _ = _ := M.rawDensity_integral A hA i j

theorem density_complete (M : OperatorPOVM ι Ω) (i j : ι) :
    (∫ z, M.density z i j ∂M.dominatingMeasure) = (1 : Matrix ι ι ℂ) i j := by
  simpa [M.normalized] using M.density_integral Set.univ MeasurableSet.univ i j

theorem density_matrix_integrable (M : OperatorPOVM ι Ω) :
    Integrable (fun z => (fun i j => M.density z i j)) M.dominatingMeasure :=
  Integrable.of_eval fun i => Integrable.of_eval fun j => M.density_integrable i j

theorem density_matrix_integral (M : OperatorPOVM ι Ω) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ z in A, (fun i j => M.density z i j) ∂M.dominatingMeasure) = M.measure A := by
  ext i j
  rw [eval_integral (fun k => (M.density_matrix_integrable.eval k).integrableOn) i,
    eval_integral (fun k => (M.density_integrable i k).integrableOn) j]
  exact M.density_integral A hA i j

/-- 直接交给风险模块的密度型 POVM，全部字段来自原始矩阵值测度。 -/
def toDensityPOVM (M : OperatorPOVM ι Ω) : DensityPOVM ι Ω M.dominatingMeasure where
  effect := M.density
  positive := M.density_positive
  integrable := M.density_integrable
  complete := M.density_complete

theorem toDensityPOVM_operatorMeasure (M : OperatorPOVM ι Ω) (A : Set Ω)
    (hA : MeasurableSet A) :
    M.toDensityPOVM.operatorMeasure M.dominatingMeasure A = M.measure A := by
  ext i j
  exact M.density_integral A hA i j

end OperatorPOVM

/-- 任意结果空间的普通 POVM 都被 035 的 DensityPOVM 完整表示。 -/
theorem exists_density_of_operator_povm
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (F : Set Ω → Matrix ι ι ℂ) (h0 : F ∅ = 0)
    (hp : ∀ s, MeasurableSet s → (F s).PosSemidef) (h1 : F Set.univ = 1)
    (hadd : ∀ s : ℕ → Set Ω, (∀ k, MeasurableSet (s k)) →
      Pairwise (fun i j => Disjoint (s i) (s j)) → HasSum (fun k => F (s k)) (F (⋃ k, s k))) :
    ∃ (μ : Measure Ω), IsFiniteMeasure μ ∧ ∃ P : DensityPOVM ι Ω μ,
      ∀ A, MeasurableSet A → P.operatorMeasure μ A = F A := by
  let M := OperatorPOVM.ofSetFunction F h0 hp h1 hadd
  refine ⟨M.dominatingMeasure, inferInstance, M.toDensityPOVM, ?_⟩
  intro A hA
  exact (M.toDensityPOVM_operatorMeasure A hA).trans
    (OperatorPOVM.ofSetFunction_apply F h0 hp h1 hadd A hA)

end FiniteCopy.Risk


