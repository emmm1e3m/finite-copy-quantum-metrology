import FiniteCopy.FixedPosition
import FiniteCopy.GaussianLimit
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CopyQuantumMetrology.FixedWidth

lemma continuousOn_rate {b : ℝ → ℝ} (hb : ContinuousOn b (Icc (-1:ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 < b x) : ContinuousOn (rate b) (Icc (-1:ℝ) 1) := by
  have hp : ContinuousOn (positionProfile b) (Icc (-1:ℝ) 1) := (continuousOn_id.pow 2).mul hb
  have hg : ContinuousOn (gradientProfile b) (Icc (-1:ℝ) 1) := by
    exact continuousOn_const.div (continuousOn_const.mul hb) (fun x hx => by have := hpos x hx; positivity)
  exact hp.add hg

lemma profile_bounds {b : ℝ → ℝ} {x L M : ℝ} (hL : 0 < L)
    (hx : x ∈ Icc (-1:ℝ) 1) (hbL : L ≤ b x) (hbM : b x ≤ M) :
    0 ≤ positionProfile b x ∧ positionProfile b x ≤ M ∧
    0 ≤ gradientProfile b x ∧ gradientProfile b x ≤ 1/(4*L) := by
  have hb : 0 < b x := hL.trans_le hbL
  have hx2 : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  refine ⟨mul_nonneg (sq_nonneg _) hb.le,?_,by unfold gradientProfile; positivity,?_⟩
  · exact (mul_le_mul_of_nonneg_right hx2 hb.le).trans (by simpa using hbM)
  · unfold gradientProfile
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma U_normalize (b : ℝ → ℝ) (n : ℕ) :
    U b n / GlobalBounds.spinJ n =
      (∑ i ∈ Finset.range (n+1), I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i) / GlobalBounds.spinJ n)/(n+1:ℕ)+
      (∑ i ∈ Finset.range n, G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i) / GlobalBounds.spinJ n)/(n+1:ℕ)+
      (∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))/
        ((n+1:ℕ)*GlobalBounds.spinJ n) := by
  have he := RateFunctional.raw_energy_normalize (n+1) (GlobalBounds.spinJ n)
    (fun i => I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))
    (fun i => G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))
    (fun i => GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))
  simpa only [U,Nat.add_sub_cancel,add_div] using he

lemma rateAverage_split (b : ℝ → ℝ) (n : ℕ) :
    RateFunctional.spinAverage (rate b) (n+1)=
      (∑ i ∈ Finset.range (n+1), positionProfile b (RateFunctional.spinPoint (n+1) i))/(n+1:ℕ)+
      (∑ i ∈ Finset.range n, gradientProfile b (RateFunctional.spinPoint (n+1) i))/(n+1:ℕ)+
      gradientProfile b (RateFunctional.spinPoint (n+1) n)/(n+1:ℕ) := by
  unfold RateFunctional.spinAverage rate
  rw [Finset.sum_add_distrib,Finset.sum_range_succ (f := fun i => gradientProfile b (RateFunctional.spinPoint (n+1) i))]
  ring

lemma correction_error {n : ℕ} (hn : 1 ≤ n) :
    |(∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))/
      ((n+1:ℕ)*GlobalBounds.spinJ n)| ≤ 2*(1+Real.log (n+1:ℕ))/GlobalBounds.spinJ n := by
  have hJ := GlobalBounds.spinJ_pos n
  rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun i hi => GlobalBounds.correction_nonneg _ _)) (by positivity))]
  exact GlobalBounds.normalized_correction_le_log hn

-- 这里只是有限和引理；终端定理会将所有输入实例化为真实高斯积分证明。
theorem energy_midpoint_error {b : ℝ → ℝ} {n : ℕ} {L M CI CG delta etaI etaG : ℝ}
    (hn : 1 ≤ n) (hL : 0 < L) (hM : 0 ≤ M) (hCI : 0 ≤ CI) (hCG : 0 ≤ CG)
    (hb : ∀ x ∈ Icc (-1:ℝ) 1, L ≤ b x ∧ b x ≤ M)
    (hd : 0 ≤ delta) (hIeta : 0 ≤ etaI) (hGeta : 0 ≤ etaG)
    (hIglobal : ∀ i ≤ n, I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n ≤ CI)
    (hGglobal : ∀ i < n, G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n ≤ CG)
    (hIbulk : ∀ i ≤ n, i ∉ GlobalBounds.endpointColumns n delta →
      |I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
        positionProfile b (RateFunctional.spinPoint (n+1) i)| ≤ etaI)
    (hGbulk : ∀ i < n, i ∉ GlobalBounds.endpointEdges n delta →
      |G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
        gradientProfile b (RateFunctional.spinPoint (n+1) i)| ≤ etaG) :
    |U b n/GlobalBounds.spinJ n-RateFunctional.spinAverage (rate b) (n+1)| ≤
      etaI+etaG+(CI+M+2*(CG+1/(4*L)))*(delta+1/GlobalBounds.spinJ n)+
      (1/(4*L))/(n+1:ℕ)+2*(1+Real.log (n+1:ℕ))/GlobalBounds.spinJ n := by
  have hJ := GlobalBounds.spinJ_pos n
  have hip (i : ℕ) (hi : i ≤ n) :=
    profile_bounds hL (GaussianLimit.spinPoint_mem n i hi) (hb _ (GaussianLimit.spinPoint_mem n i hi)).1
      (hb _ (GaussianLimit.spinPoint_mem n i hi)).2
  have hiBad (i : ℕ) (hi : i < n+1) (_ : i ∈ GlobalBounds.endpointColumns n delta) :
      |I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
        positionProfile b (RateFunctional.spinPoint (n+1) i)| ≤ CI+M := by
    have hnI := div_nonneg (I_nonneg b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)) hJ.le
    obtain ⟨hp0,hpM,-,-⟩ := hip i (by omega)
    have hu := hIglobal i (by omega)
    exact abs_le.2 ⟨by linarith,by linarith⟩
  have hgBad (i : ℕ) (hi : i < n) (_ : i ∈ GlobalBounds.endpointEdges n delta) :
      |G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
        gradientProfile b (RateFunctional.spinPoint (n+1) i)| ≤ CG+1/(4*L) := by
    have hnG := div_nonneg (G_nonneg b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)) hJ.le
    obtain ⟨-,-,hp0,hpM⟩ := hip i (by omega)
    have hu := hGglobal i hi
    exact abs_le.2 ⟨by linarith,by linarith⟩
  have hi := RateFunctional.partial_average_error (n := n+1) (d := n+1)
    (GlobalBounds.endpointColumns n delta) (Nat.succ_pos n) le_rfl hIeta
    (fun i hi he => hIbulk i (by omega) he) hiBad
  have hg := RateFunctional.partial_average_error (n := n) (d := n+1)
    (GlobalBounds.endpointEdges n delta) (Nat.succ_pos n) (by omega) hGeta
    hGbulk hgBad
  have hci : (CI+M)*(((Finset.range (n+1)).filter (fun i => i ∈ GlobalBounds.endpointColumns n delta)).card:ℝ)/(n+1:ℕ) ≤
      (CI+M)*(delta+1/GlobalBounds.spinJ n) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (GaussianLimit.endpoint_column_fraction hd) (by positivity)
  have hcg : (CG+1/(4*L))*(((Finset.range n).filter (fun i => i ∈ GlobalBounds.endpointEdges n delta)).card:ℝ)/(n+1:ℕ) ≤
      (CG+1/(4*L))*(2*(delta+1/GlobalBounds.spinJ n)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (GaussianLimit.endpoint_edge_fraction hd) (by positivity)
  have hilast := hip n le_rfl
  have hlast : |gradientProfile b (RateFunctional.spinPoint (n+1) n)/(n+1:ℕ)| ≤ (1/(4*L))/(n+1:ℕ) := by
    rw [abs_of_nonneg (div_nonneg hilast.2.2.1 (by positivity))]
    exact div_le_div_of_nonneg_right hilast.2.2.2 (by positivity)
  have hR := correction_error hn
  let A := (∑ i ∈ Finset.range (n+1), I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n)/(n+1:ℕ)
  let B := (∑ i ∈ Finset.range n, G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n)/(n+1:ℕ)
  let P := (∑ i ∈ Finset.range (n+1), positionProfile b (RateFunctional.spinPoint (n+1) i))/(n+1:ℕ)
  let Q := (∑ i ∈ Finset.range n, gradientProfile b (RateFunctional.spinPoint (n+1) i))/(n+1:ℕ)
  let R := (∑ i ∈ Finset.range (n+1), GlobalBounds.correction (GlobalBounds.spinJ n) (GlobalBounds.spinM n i))/((n+1:ℕ)*GlobalBounds.spinJ n)
  let T := gradientProfile b (RateFunctional.spinPoint (n+1) n)/(n+1:ℕ)
  have he : U b n/GlobalBounds.spinJ n-RateFunctional.spinAverage (rate b) (n+1)=(A-P)+(B-Q)+R-T := by
    rw [U_normalize,rateAverage_split]
    dsimp [A,B,P,Q,R,T]
    ring
  rw [he]
  have ht : |(A-P)+(B-Q)+R-T| ≤ |A-P|+|B-Q|+|R|+|T| := by
    have hab := abs_add_le (A-P) (B-Q)
    have habr := (abs_add_le ((A-P)+(B-Q)) R).trans (add_le_add hab le_rfl)
    exact (abs_sub _ _).trans (add_le_add habr le_rfl)
  have hi' : |A-P| ≤ etaI+(CI+M)*(delta+1/GlobalBounds.spinJ n) := hi.trans (add_le_add le_rfl hci)
  have hg' : |B-Q| ≤ etaG+(CG+1/(4*L))*(2*(delta+1/GlobalBounds.spinJ n)) := hg.trans (add_le_add le_rfl hcg)
  calc
    _ ≤ |A-P|+|B-Q|+|R|+|T| := ht
    _ ≤ (etaI+(CI+M)*(delta+1/GlobalBounds.spinJ n))+
      (etaG+(CG+1/(4*L))*(2*(delta+1/GlobalBounds.spinJ n)))+
      2*(1+Real.log (n+1:ℕ))/GlobalBounds.spinJ n+(1/(4*L))/(n+1:ℕ) :=
      add_le_add (add_le_add (add_le_add hi' hg') hR) hlast
    _ = _ := by ring

-- 先固定内区、再将端区宽度降至零的单一epsilon证明。
lemma tendsto_zero_of_cutoff {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop, |a n| ≤ C*delta+r n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  let delta := min 1 (eps/(2*(C+1)))
  have hd : 0 < delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hde : delta ≤ eps/(2*(C+1)) := min_le_right _ _
  have hCd : C*delta ≤ eps/2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).1 hde
    nlinarith only [hmul,hd]
  obtain ⟨r,hr,hbound⟩ := hb delta hd hd1
  have hrsmall : ∀ᶠ n : ℕ in atTop, r n < eps/2 := hr.eventually (gt_mem_nhds (by positivity : (0:ℝ)<eps/2))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hbound.and hrsmall)
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨hbn,hrn⟩ := hN n hn
  rw [Real.dist_eq,sub_zero]
  linarith

end CopyQuantumMetrology.FixedWidth
