import FiniteCopy.DiscreteBounds
import FiniteCopy.ExplicitGlobal

open scoped BigOperators
open MeasureTheory

namespace CopyQuantumMetrology.GlobalBounds

-- 端区列以真实自旋中心定义；端区边包括至少一个端点在端区的所有边。
noncomputable def endpointColumns (n : ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun i => (1 - δ) * spinJ n < |spinM n i|)

noncomputable def endpointEdges (n : ℕ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => i ∈ endpointColumns n δ ∨ i + 1 ∈ endpointColumns n δ)

lemma spinJ_pos (n : ℕ) : 0 < spinJ n := by
  dsimp [spinJ]
  positivity

lemma mem_endpointColumns {n i : ℕ} {δ : ℝ} :
    i ∈ endpointColumns n δ ↔ i ≤ n ∧ (1 - δ) * spinJ n < |spinM n i| := by
  classical
  simp only [endpointColumns, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma endpoint_index_near_end {n i : ℕ} {δ : ℝ} (hi : i ∈ endpointColumns n δ) :
    i < ⌈δ * spinJ n⌉₊ ∨ n - i < ⌈δ * spinJ n⌉₊ := by
  obtain ⟨hin, hiδ⟩ := mem_endpointColumns.mp hi
  by_cases hm : 0 ≤ spinM n i
  · right
    apply Nat.lt_ceil.mpr
    rw [Nat.cast_sub hin]
    rw [abs_of_nonneg hm] at hiδ
    dsimp [spinM, spinJ] at hiδ ⊢
    nlinarith
  · left
    apply Nat.lt_ceil.mpr
    rw [abs_of_neg (lt_of_not_ge hm)] at hiδ
    dsimp [spinM, spinJ] at hiδ ⊢
    nlinarith

theorem endpointColumns_card_le_ceil (n : ℕ) (δ : ℝ) :
    (endpointColumns n δ).card ≤ 2 * ⌈δ * spinJ n⌉₊ := by
  classical
  let s := Finset.range ⌈δ * spinJ n⌉₊
  have hsub : endpointColumns n δ ⊆ s ∪ s.image (fun i => n - i) := by
    intro i hi
    rcases endpoint_index_near_end hi with hl | hr
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hl)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨n - i, Finset.mem_range.mpr hr, ?_⟩
      have := (mem_endpointColumns.mp hi).1
      omega
  calc
    _ ≤ (s ∪ s.image (fun i => n - i)).card := Finset.card_le_card hsub
    _ ≤ s.card + (s.image (fun i => n - i)).card := Finset.card_union_le _ _
    _ ≤ s.card + s.card := Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by simp [s]; omega

theorem endpointColumns_card_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ((endpointColumns n δ).card : ℝ) ≤ 2 * δ * spinJ n + 2 := by
  have hc : ((endpointColumns n δ).card : ℝ) ≤ 2 * (⌈δ * spinJ n⌉₊ : ℝ) := by
    exact_mod_cast endpointColumns_card_le_ceil n δ
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hδ (spinJ_pos n).le)
  nlinarith

theorem endpointEdges_card_le_twice (n : ℕ) (δ : ℝ) :
    (endpointEdges n δ).card ≤ 2 * (endpointColumns n δ).card := by
  classical
  have hsub : endpointEdges n δ ⊆ endpointColumns n δ ∪
      (endpointColumns n δ).image Nat.pred := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with hl | hr
    · exact Finset.mem_union_left _ hl
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i + 1, hr, by simp⟩)
  calc
    _ ≤ (endpointColumns n δ ∪ (endpointColumns n δ).image Nat.pred).card :=
      Finset.card_le_card hsub
    _ ≤ (endpointColumns n δ).card + ((endpointColumns n δ).image Nat.pred).card :=
      Finset.card_union_le _ _
    _ ≤ (endpointColumns n δ).card + (endpointColumns n δ).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by omega

theorem endpointEdges_card_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ((endpointEdges n δ).card : ℝ) ≤ 4 * δ * spinJ n + 4 := by
  have hc : ((endpointEdges n δ).card : ℝ) ≤ 2 * (endpointColumns n δ).card := by
    exact_mod_cast endpointEdges_card_le_twice n δ
  nlinarith [endpointColumns_card_le hδ n]

theorem sum_endpointColumns_le {δ C : ℝ} {f : ℕ → ℝ} (n : ℕ)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hf : ∀ i ∈ endpointColumns n δ, f i ≤ C) :
    (∑ i ∈ endpointColumns n δ, f i) ≤ (2 * δ * spinJ n + 2) * C := by
  calc
    _ ≤ ∑ i ∈ endpointColumns n δ, C := Finset.sum_le_sum hf
    _ = ((endpointColumns n δ).card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (endpointColumns_card_le hδ n) hC

theorem sum_endpointEdges_le {δ C : ℝ} {f : ℕ → ℝ} (n : ℕ)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hf : ∀ i ∈ endpointEdges n δ, f i ≤ C) :
    (∑ i ∈ endpointEdges n δ, f i) ≤ (4 * δ * spinJ n + 4) * C := by
  calc
    _ ≤ ∑ i ∈ endpointEdges n δ, C := Finset.sum_le_sum hf
    _ = ((endpointEdges n δ).card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (endpointEdges_card_le hδ n) hC

-- 归一化与实际 U/J 一致，维数恰为 n+1=2J。
theorem normalized_endpointColumns_le {δ C : ℝ} {f : ℕ → ℝ} (n : ℕ)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hf : ∀ i ∈ endpointColumns n δ, f i ≤ C * spinJ n) :
    (∑ i ∈ endpointColumns n δ, f i) / ((n + 1 : ℕ) * spinJ n) ≤
      C * (δ + 1 / spinJ n) := by
  have hJ := spinJ_pos n
  have hs := sum_endpointColumns_le n hδ (mul_nonneg hC hJ.le) hf
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ) * spinJ n)).2
  calc
    _ ≤ (2 * δ * spinJ n + 2) * (C * spinJ n) := hs
    _ = _ := by
      have hn : ((n + 1 : ℕ) : ℝ) = 2 * spinJ n := by simp [spinJ]; ring
      rw [hn]
      field_simp
      <;> ring

theorem normalized_endpointEdges_le {δ C : ℝ} {f : ℕ → ℝ} (n : ℕ)
    (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hf : ∀ i ∈ endpointEdges n δ, f i ≤ C * spinJ n) :
    (∑ i ∈ endpointEdges n δ, f i) / ((n + 1 : ℕ) * spinJ n) ≤
      2 * C * (δ + 1 / spinJ n) := by
  have hJ := spinJ_pos n
  have hs := sum_endpointEdges_le n hδ (mul_nonneg hC hJ.le) hf
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ) * spinJ n)).2
  calc
    _ ≤ (4 * δ * spinJ n + 4) * (C * spinJ n) := hs
    _ = _ := by
      have hn : ((n + 1 : ℕ) : ℝ) = 2 * spinJ n := by simp [spinJ]; ring
      rw [hn]
      field_simp
      <;> ring

theorem gaussian_endpoint_energy_regularized {n : ℕ} {ε δ : ℝ}
    (hn : 1 ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) :
    (∑ i ∈ endpointColumns n δ, ∫ t,
      (k (spinJ n) (spinM n i) - q (spinJ n) t) ^ 2 *
      column (spinM n i) (width (spinJ n) (spinM n i)
        (regularizedWidth ε (spinM n i / spinJ n))) t ^ 2) /
      ((n + 1 : ℕ) * spinJ n) ≤
        (14 / ε ^ 2) * (δ + 1 / spinJ n) := by
  apply normalized_endpointColumns_le n hδ (by positivity)
  intro i hi
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact gaussian_energy_regularized (by dsimp [spinJ]; linarith) hε hε1
    (spinM_abs_le (mem_endpointColumns.mp hi).1)

end CopyQuantumMetrology.GlobalBounds

