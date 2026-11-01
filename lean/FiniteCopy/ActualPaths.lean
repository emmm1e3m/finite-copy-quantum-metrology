import FiniteCopy.EndpointCounting
import FiniteCopy.Paths
open scoped BigOperators
open Finset

namespace FiniteCopy.EndpointCounting
open CopyQuantumMetrology.SpinPaths

noncomputable def pathCount (N n : ℕ) : ℕ :=
  ∑ b : B N, if spin N b = n then 1 else 0

theorem sum_subtype_indicator {α β : Type*} [Fintype α] [AddCommMonoid β]
    (p : α → Prop) [DecidablePred p] (f : α → β) :
    (∑ b : {b : α // p b}, f b.val) = ∑ b : α, if p b then f b else 0 := by
  classical
  rw [← Finset.sum_subtype (univ.filter p) (by simp)]
  exact sum_filter _ _

theorem pathCount_fiber_card (N n : ℕ) :
    pathCount N n = Fintype.card {b : B N // spin N b=n} := by
  simpa [pathCount] using (sum_subtype_indicator
    (fun b : B N => spin N b=n) (fun _ => (1 : ℕ))).symm

@[simp] theorem pathCount_zero (n : ℕ) : pathCount 0 n = if n=0 then 1 else 0 := by
  have hcard : Fintype.card (B 0) = 1 := by change Fintype.card PUnit = 1; simp
  simp [pathCount, spin_zero, eq_comm, hcard]

theorem pathCount_succ_zero (N : ℕ) : pathCount (N+1) 0 = pathCount N 1 := by
  unfold pathCount
  rw [sum_succ]
  simp only [spin_up, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    sum_const_zero, zero_add, spin_down]
  change (∑ b : {b : B N // 0 < spin N b}, if spin N b.val-1=0 then 1 else 0) =
    ∑ b : B N, if spin N b=1 then 1 else 0
  rw [sum_subtype_indicator (fun b : B N => 0 < spin N b)
    (fun b => if spin N b-1=0 then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro b _
  split_ifs <;> omega

theorem pathCount_succ_succ (N n : ℕ) :
    pathCount (N+1) (n+1) = pathCount N n + pathCount N (n+2) := by
  unfold pathCount
  rw [sum_succ]
  simp only [spin_up, spin_down, Nat.add_right_cancel_iff]
  congr 1
  change (∑ b : {b : B N // 0 < spin N b}, if spin N b.val-1=n+1 then 1 else 0) =
    ∑ b : B N, if spin N b=n+2 then 1 else 0
  rw [sum_subtype_indicator (fun b : B N => 0 < spin N b)
    (fun b => if spin N b-1=n+1 then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro b _
  split_ifs <;> omega

/-- 由039实际路径类型逐步数出端点；没有计数公式假设。 -/
theorem pathCount_eq (N n : ℕ) : pathCount N n = endpointCount N n := by
  induction N generalizing n with
  | zero => simp [endpointCount]
  | succ N ih =>
      cases n with
      | zero => rw [pathCount_succ_zero, endpointCount, ih]
      | succ n => rw [pathCount_succ_succ, endpointCount, ih, ih]

theorem actual_path_multiplicity (N k : ℕ) (hk : k ≤ N/2) :
    pathCount N (N-2*k) = N.choose k - (if k=0 then 0 else N.choose (k-1)) := by
  rw [pathCount_eq]
  exact endpointCount_legal N k hk

theorem actual_path_zero_of_no_endpoint (N n : ℕ) (h : ¬∃k : ℕ, N=n+2*k) :
    pathCount N n = 0 := by
  rw [pathCount_eq]
  exact endpointCount_zero_of_no_endpoint N n h

theorem actual_path_multiplicity_card (N k : ℕ) (hk : k ≤ N/2) :
    Fintype.card {b : B N // spin N b=N-2*k} =
      N.choose k - (if k=0 then 0 else N.choose (k-1)) := by
  rw [← pathCount_fiber_card]
  exact actual_path_multiplicity N k hk

theorem path_spin_legal (N : ℕ) (b : B N) : ∃ k : ℕ, N = spin N b+2*k := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
      rcases b with b | b
      · obtain ⟨k,hk⟩ := ih b
        exact ⟨k, by rw [spin_up]; omega⟩
      · obtain ⟨k,hk⟩ := ih b.val
        have hb := b.property
        refine ⟨k+1, ?_⟩
        change N+1 = spin N b.val-1+2*(k+1)
        change 0 < spin N b.val at hb
        omega

theorem path_spin_le (N : ℕ) (b : B N) : spin N b ≤ N := by
  obtain ⟨k,hk⟩ := path_spin_legal N b
  omega

/-- 按实际路径端点分组，不先假定多重度。 -/
theorem sum_paths_by_endpoint (N : ℕ) (f : ℕ → ℝ) :
    (∑ b : B N, f (spin N b)) =
      ∑ n ∈ range (N+1), (endpointCount N n : ℝ) * f n := by
  have hcount (n : ℕ) : (endpointCount N n : ℝ) * f n =
      ∑ b : B N, if spin N b=n then f n else 0 := by
    rw [← pathCount_eq]
    unfold pathCount
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro b _
    split_ifs <;> simp_all
  simp_rw [hcount]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  have hb : spin N b ∈ range (N+1) := mem_range.mpr (by have := path_spin_le N b; omega)
  simp [hb]

end FiniteCopy.EndpointCounting
