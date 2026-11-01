import FiniteCopy.FixedAssembly
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace CopyQuantumMetrology.FixedWidth

lemma spinM_succ (n i : ℕ) : GlobalBounds.spinM n (i+1)=GlobalBounds.spinM n i+1 := by
  unfold GlobalBounds.spinM
  push_cast
  ring

lemma spinJ_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ GlobalBounds.spinJ n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold GlobalBounds.spinJ
  linarith

-- 一般梯度的解析证明在调用端接入；位置项、端区计数、离散修正与黎曼和在此实际证明。
theorem U_limit_of_gradient_bounds {b : ℝ → ℝ} {L M CG : ℝ}
    (hbc : ContinuousOn b (Icc (-1:ℝ) 1)) (hL : 0 < L) (hM : 1 ≤ M)
    (hb : ∀ x ∈ Icc (-1:ℝ) 1, L ≤ b x ∧ b x ≤ M) (hCG : 0 ≤ CG)
    (hGglobal : ∀ J : ℝ, 1 ≤ J → ∀ m : ℝ, |m| ≤ J-1/2 → |m+1| ≤ J-1/2 → G b J m ≤ CG*J)
    (hGbulk : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∃ KG : ℝ, 0 ≤ KG ∧
      ∀ J : ℝ, 1 ≤ J → ∀ m : ℝ, |m| ≤ J-1/2 → |m+1| ≤ J-1/2 →
        |m/J| ≤ 1-delta → |(m+1)/J| ≤ 1-delta →
        |G b J m/J-gradientProfile b (m/J)| ≤ KG/Real.sqrt J) :
    Tendsto (fun n : ℕ => U b n/GlobalBounds.spinJ n) atTop
      (𝓝 ((∫ x in (-1:ℝ)..1, rate b x)/2)) := by
  let CI := 5/2+16*M+12*M^2
  let C := CI+M+2*(CG+1/(4*L))
  have hM0 : 0 ≤ M := by linarith
  have hCI : 0 ≤ CI := by dsimp [CI]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hJlim : Tendsto GlobalBounds.spinJ atTop atTop := GaussianLimit.spinJ_atTop
  have hsrJ : Tendsto (fun n : ℕ => Real.sqrt (GlobalBounds.spinJ n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hJlim
  have hcorr : Tendsto (fun n : ℕ => 2*(1+Real.log (2*GlobalBounds.spinJ n))/GlobalBounds.spinJ n) atTop (𝓝 0) :=
    GaussianLimit.correctionBudget_limit.comp hJlim
  have hz : Tendsto (fun n : ℕ => U b n/GlobalBounds.spinJ n-RateFunctional.spinAverage (rate b) (n+1)) atTop (𝓝 0) := by
    apply tendsto_zero_of_cutoff hC
    intro delta hd hd1
    obtain ⟨KG,hKG,hGB⟩ := hGbulk delta hd hd1
    let r : ℕ → ℝ := fun n => 6000*M^2/(delta^6*Real.sqrt (GlobalBounds.spinJ n))+
      KG/Real.sqrt (GlobalBounds.spinJ n)+(C+1/(8*L))/GlobalBounds.spinJ n+
      2*(1+Real.log (2*GlobalBounds.spinJ n))/GlobalBounds.spinJ n
    have hIlim : Tendsto (fun n : ℕ => 6000*M^2/(delta^6*Real.sqrt (GlobalBounds.spinJ n))) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.div_atTop hsrJ : Tendsto (fun n : ℕ => (6000*M^2/delta^6)/Real.sqrt (GlobalBounds.spinJ n)) atTop (𝓝 0)) using 1
      ext n
      ring
    have hGlim : Tendsto (fun n : ℕ => KG/Real.sqrt (GlobalBounds.spinJ n)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hsrJ
    have hsmall : Tendsto (fun n : ℕ => (C+1/(8*L))/GlobalBounds.spinJ n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hJlim
    refine ⟨r,?_,?_⟩
    · simpa only [zero_add,add_zero] using ((hIlim.add hGlim).add hsmall).add hcorr
    · filter_upwards [eventually_ge_atTop (1:ℕ),hJlim.eventually (eventually_ge_atTop M),
        hJlim.eventually (eventually_ge_atTop (1/(delta*L)))] with n hn hJM hJL
      have hJ := GlobalBounds.spinJ_pos n
      have hJ1 := spinJ_ge_one hn
      have hJL' : 1 ≤ GlobalBounds.spinJ n*delta*L := by
        have hh := (div_le_iff₀ (mul_pos hd hL)).1 hJL
        simpa only [mul_assoc] using hh
      have hIg (i : ℕ) (hi : i ≤ n) : I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n ≤ CI := by
        exact (div_le_iff₀ hJ).2 (I_global hJ1 hL hb (GlobalBounds.spinM_abs_le hi))
      have hGg (i : ℕ) (hi : i < n) : G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n ≤ CG := by
        apply (div_le_iff₀ hJ).2
        apply hGglobal _ hJ1 _ (GlobalBounds.spinM_abs_le (by omega))
        rw [← spinM_succ]
        exact GlobalBounds.spinM_abs_le (by omega)
      have hIb (i : ℕ) (hi : i ≤ n) (he : i ∉ GlobalBounds.endpointColumns n delta) :
          |I b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
            positionProfile b (RateFunctional.spinPoint (n+1) i)| ≤ 6000*M^2/(delta^6*Real.sqrt (GlobalBounds.spinJ n)) := by
        have hx : |GlobalBounds.spinM n i/GlobalBounds.spinJ n| ≤ 1-delta := by
          simpa only [GaussianLimit.spinJ_eq] using GaussianLimit.good_column_scaled hi he
        have hxi : GlobalBounds.spinM n i/GlobalBounds.spinJ n ∈ Icc (-1:ℝ) 1 := by
          simpa only [GaussianLimit.spinPoint_eq,GaussianLimit.spinJ_eq] using GaussianLimit.spinPoint_mem n i hi
        have hbb := hb _ hxi
        have heq : GlobalBounds.spinJ n*(GlobalBounds.spinM n i/GlobalBounds.spinJ n)=GlobalBounds.spinM n i := by field_simp
        have hbound := I_bulk (b := b) hJ1 hL hM hd hd1 hx hbb.1 hbb.2 hJM hJL'
        rw [heq] at hbound
        simpa only [GaussianLimit.spinPoint_eq,GaussianLimit.spinJ_eq] using hbound
      have hGb (i : ℕ) (hi : i < n) (he : i ∉ GlobalBounds.endpointEdges n delta) :
          |G b (GlobalBounds.spinJ n) (GlobalBounds.spinM n i)/GlobalBounds.spinJ n-
            gradientProfile b (RateFunctional.spinPoint (n+1) i)| ≤ KG/Real.sqrt (GlobalBounds.spinJ n) := by
        obtain ⟨hei,hei1⟩ := GaussianLimit.good_edge_columns hi he
        have hm := GlobalBounds.spinM_abs_le (n := n) (i := i) (by omega)
        have hm1 : |GlobalBounds.spinM n i+1| ≤ GlobalBounds.spinJ n-1/2 := by
          rw [← spinM_succ]
          exact GlobalBounds.spinM_abs_le (by omega)
        have hmi := GaussianLimit.good_column_scaled (show i ≤ n by omega) hei
        have hmi1 : |(GlobalBounds.spinM n i+1)/GlobalBounds.spinJ n| ≤ 1-delta := by
          rw [← spinM_succ]
          exact GaussianLimit.good_column_scaled (by omega) hei1
        have hbound := hGB _ hJ1 _ hm hm1 hmi hmi1
        simpa only [GaussianLimit.spinPoint_eq,GaussianLimit.spinJ_eq] using hbound
      have he := energy_midpoint_error hn hL hM0 hCI hCG hb hd.le (by positivity) (by positivity) hIg hGg hIb hGb
      have hcast : ((n+1:ℕ):ℝ)=2*GlobalBounds.spinJ n := by simp [GlobalBounds.spinJ]; ring
      calc
        _ ≤ 6000*M^2/(delta^6*Real.sqrt (GlobalBounds.spinJ n))+KG/Real.sqrt (GlobalBounds.spinJ n)+
            (CI+M+2*(CG+1/(4*L)))*(delta+1/GlobalBounds.spinJ n)+
            (1/(4*L))/(n+1:ℕ)+2*(1+Real.log (n+1:ℕ))/GlobalBounds.spinJ n := he
        _ = C*delta+r n := by
          rw [hcast]
          dsimp [C,r]
          ring
  have hrate : ContinuousOn (rate b) (Icc (-1:ℝ) 1) :=
    continuousOn_rate hbc (fun x hx => hL.trans_le (hb x hx).1)
  have hmid := RateFunctional.half_integer_spinAverage_tendsto hrate
  simpa only [sub_add_cancel,zero_add] using hz.add hmid

lemma spinJ_div_spin_limit :
    Tendsto (fun n : ℕ => GlobalBounds.spinJ n/((n:ℝ)/2)) atTop (𝓝 1) := by
  have hh := GaussianLimit.spinJ_div_nat_limit.const_mul 2
  convert hh using 1
  · ext n
    unfold GlobalBounds.spinJ CopyQuantumMetrology.spinJ
    ring
  · norm_num

lemma U_spin_limit_of_scale_limit {b : ℝ → ℝ} {A : ℝ}
    (hU : Tendsto (fun n : ℕ => U b n/GlobalBounds.spinJ n) atTop (𝓝 A)) :
    Tendsto (fun n : ℕ => U b n/((n:ℝ)/2)) atTop (𝓝 A) := by
  have hh := hU.mul spinJ_div_spin_limit
  convert hh using 1
  · ext n
    symm
    exact div_mul_div_cancel₀ (GlobalBounds.spinJ_pos n).ne'
  · simp only [mul_one]

end CopyQuantumMetrology.FixedWidth
