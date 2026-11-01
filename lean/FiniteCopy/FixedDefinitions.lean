import FiniteCopy.GlobalBounds
import FiniteCopy.DiscreteBounds
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace CopyQuantumMetrology.FixedWidth

/-- 固定轮廓的真实方差 S_b(s)。 -/
def width (b : ℝ → ℝ) (J s : ℝ) : ℝ := GlobalBounds.width J s (b (s/J))
/-- 论文原始归一高斯列。 -/
def v (b : ℝ → ℝ) (J s t : ℝ) : ℝ := column s (width b J s) t
/-- 实际位置能量。 -/
def I (b : ℝ → ℝ) (J m : ℝ) : ℝ :=
  ∫ t, (GlobalBounds.k J m-GlobalBounds.q J t)^2 * v b J m t^2
/-- 实际相邻列有限差分能量。 -/
def G (b : ℝ → ℝ) (J m : ℝ) : ℝ :=
  GlobalBounds.q J (m+1/2) * ∫ t, GlobalBounds.q J t * (v b J (m+1) t-v b J m t)^2
/-- n=2j；含全部 n+1 列、n 条边及真实离散系数修正。 -/
def U (b : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range (n+1), I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))+
    (∑ i ∈ Finset.range n, G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))+
    (∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)))/(n+1 : ℕ)

def positionProfile (b : ℝ → ℝ) (x : ℝ) : ℝ := x^2*b x
def gradientProfile (b : ℝ → ℝ) (x : ℝ) : ℝ := 1/(4*b x)
def rate (b : ℝ → ℝ) (x : ℝ) : ℝ := positionProfile b x+gradientProfile b x

lemma I_nonneg (b : ℝ → ℝ) (J m : ℝ) : 0 ≤ I b J m :=
  integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)
lemma G_nonneg (b : ℝ → ℝ) (J m : ℝ) : 0 ≤ G b J m :=
  mul_nonneg (GlobalBounds.q_nonneg J _) (integral_nonneg fun t =>
    mul_nonneg (GlobalBounds.q_nonneg J t) (sq_nonneg _))

end CopyQuantumMetrology.FixedWidth
