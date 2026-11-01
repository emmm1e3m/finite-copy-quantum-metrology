import FiniteCopy.Ladder

open scoped BigOperators
noncomputable section
namespace CopyQuantumMetrology.ClebschGordan

lemma sqrt_times_sqrt (x y : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x*y) * Real.sqrt x = x * Real.sqrt y := by
  rw [Real.sqrt_mul hx]
  calc
    _ = Real.sqrt x ^ 2 * Real.sqrt y := by ring
    _ = _ := by rw [Real.sq_sqrt hx]

lemma edge_a_plus (n i : ℕ) :
    edge n i * a n i = edge (n+1) i * a n (i+1) := by
  have he : ((n : ℝ)+1 - ((i : ℝ)+1)) = (n : ℝ)-i := by ring
  simp only [edge, a, Nat.cast_add, Nat.cast_one, he]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+1),
    Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+1)]
  ring

lemma edge_b_plus (n i : ℕ) :
    edge n i * b n (i+1) + a n (i+1) = edge (n+1) (i+1) * b n (i+2) := by
  have he : ((n : ℝ)+1 - ((i : ℝ)+1)) = (n : ℝ)-i := by ring
  simp only [edge, a, b, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, he]
  rw [← mul_div_assoc, sqrt_times_sqrt _ _ (by positivity)]
  have ht : ((i : ℝ)+1+1) = (i : ℝ)+2 := by ring
  rw [ht, ← mul_div_assoc, sqrt_times_sqrt _ _ (by positivity)]
  ring

lemma edge_plus_zero (n : ℕ) : a n 0 = edge (n+1) 0 * b n 1 := by
  simp [a, b, edge, div_eq_mul_inv]

lemma edge_b_minus (n i : ℕ) :
    edge (n+1) (i+1) * b (n+1) (i+1) = edge n i * b (n+1) (i+2) := by
  have he : ((n : ℝ)+1 - ((i : ℝ)+1)) = (n : ℝ)-i := by ring
  have ht : ((i : ℝ)+1+1) = (i : ℝ)+2 := by ring
  simp only [edge, b, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, he, ht]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+2),
    Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+1)]
  ring

lemma edge_a_minus (n i : ℕ) (hi : i ≤ n) :
    edge (n+1) i * a (n+1) (i+1) - b (n+1) (i+1) =
      edge n i * a (n+1) (i+2) := by
  have h₁ : ((n : ℝ)+1+1 - ((i : ℝ)+1)) = (n : ℝ)+1-i := by ring
  have h₂ : ((n : ℝ)+1+1 - ((i : ℝ)+2)) = (n : ℝ)-i := by ring
  simp only [edge, a, b, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, h₁, h₂]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+1),
    Real.sqrt_mul (by positivity : 0 ≤ (i : ℝ)+1)]
  have hq : 0 ≤ (n : ℝ)-i := sub_nonneg.mpr (by exact_mod_cast hi)
  have hp : 0 ≤ (n : ℝ)+1-i := by linarith
  have hs₁ := Real.sq_sqrt hp
  have hs₂ := Real.sq_sqrt hq
  calc
    _ = Real.sqrt ((i : ℝ)+1) * (Real.sqrt ((n : ℝ)+1-i)^2 - 1) /
        Real.sqrt ((n : ℝ)+1+1) := by ring
    _ = Real.sqrt ((i : ℝ)+1) * ((n : ℝ)-i) / Real.sqrt ((n : ℝ)+1+1) := by
      rw [hs₁]
      ring
    _ = Real.sqrt ((i : ℝ)+1) * Real.sqrt ((n : ℝ)-i)^2 /
        Real.sqrt ((n : ℝ)+1+1) := by rw [hs₂]
    _ = _ := by ring

end CopyQuantumMetrology.ClebschGordan

