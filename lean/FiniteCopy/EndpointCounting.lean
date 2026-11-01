import FiniteCopy.Schur

open scoped BigOperators
open Finset

namespace FiniteCopy.EndpointCounting

/-- 不允许自旋0向下的路径端点递推。 -/
def endpointCount : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | N+1, 0 => endpointCount N 1
  | N+1, n+1 => endpointCount N n + endpointCount N (n+2)

def prevChoose (N k : ℕ) : ℕ := if k = 0 then 0 else N.choose (k-1)
def ballot (N k : ℕ) : ℕ := N.choose k - prevChoose N k

@[simp] theorem prevChoose_zero (N : ℕ) : prevChoose N 0 = 0 := by simp [prevChoose]
@[simp] theorem prevChoose_succ (N k : ℕ) : prevChoose N (k+1) = N.choose k := by simp [prevChoose]
@[simp] theorem ballot_zero (N : ℕ) : ballot N 0 = 1 := by simp [ballot]

theorem choose_pascal_prev (N k : ℕ) :
    (N+1).choose k = N.choose k + prevChoose N k := by
  cases k with
  | zero => simp
  | succ k => simp [Nat.choose_succ_succ, add_comm]

theorem choose_le_next {N k : ℕ} (hk : 2*k+1 ≤ N) : N.choose k ≤ N.choose (k+1) := by
  by_cases h : k < N/2
  · exact Nat.choose_le_succ_of_lt_half_left h
  · have hN : N = 2*k+1 := by omega
    rw [hN, Nat.choose_symm_half]

theorem prevChoose_le {N k : ℕ} (hk : 2*k ≤ N+1) : prevChoose N k ≤ N.choose k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [prevChoose_succ]
      exact choose_le_next (by omega)

/-- 合法子端点的Pascal递推，包括奇数N的中央边界。 -/
theorem ballot_succ (N k : ℕ) (hk : 2*(k+1) ≤ N+1) :
    ballot (N+1) (k+1) = ballot N k + ballot N (k+1) := by
  have hp := prevChoose_le (N := N) (k := k) (by omega)
  have hn := choose_le_next (N := N) (k := k) (by omega)
  simp only [ballot, prevChoose_succ, Nat.choose_succ_succ, choose_pascal_prev]
  simp only [Nat.succ_eq_add_one]
  omega

theorem ballot_odd_center (k : ℕ) : ballot (2*k+1) (k+1) = 0 := by
  simp [ballot, Nat.choose_symm_half]

theorem endpointCount_zero_of_no_endpoint (N n : ℕ)
    (h : ¬ ∃ k : ℕ, N = n+2*k) : endpointCount N n = 0 := by
  induction N generalizing n with
  | zero =>
      have hn : n ≠ 0 := by intro hn; apply h; exact ⟨0, by omega⟩
      simp [endpointCount, hn]
  | succ N ih =>
      cases n with
      | zero =>
          apply ih 1
          rintro ⟨k,hk⟩
          apply h
          exact ⟨k+1, by omega⟩
      | succ n =>
          rw [endpointCount]
          have h0 : endpointCount N n = 0 := ih n (by
            rintro ⟨k,hk⟩
            apply h
            exact ⟨k, by omega⟩)
          have h2 : endpointCount N (n+2) = 0 := ih (n+2) (by
            rintro ⟨k,hk⟩
            apply h
            exact ⟨k+1, by omega⟩)
          rw [h0,h2]

theorem endpointCount_ballot (N n k : ℕ) (h : N = n+2*k) :
    endpointCount N n = ballot N k := by
  induction N generalizing n k with
  | zero =>
      have hn : n = 0 := by omega
      have hk : k = 0 := by omega
      simp [hn, hk, endpointCount]
  | succ N ih =>
      cases n with
      | zero =>
          obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
          have hN : N = 2*k+1 := by omega
          rw [endpointCount, ih 1 k (by omega), ballot_succ N k (by omega), hN,
            ballot_odd_center, add_zero]
      | succ n =>
          cases k with
          | zero =>
              have hN : N = n := by omega
              rw [endpointCount, ih n 0 (by omega), ballot_zero,
                endpointCount_zero_of_no_endpoint N (n+2) (by rintro ⟨k,hk⟩; omega),
                add_zero, ballot_zero]
          | succ k =>
              rw [endpointCount, ih n (k+1) (by omega), ih (n+2) k (by omega),
                ballot_succ N k (by omega)]
              omega

theorem endpointCount_legal (N k : ℕ) (hk : k ≤ N/2) :
    endpointCount N (N-2*k) = N.choose k - (if k=0 then 0 else N.choose (k-1)) := by
  exact endpointCount_ballot N (N-2*k) k (by omega)

theorem endpointCount_gt (N n : ℕ) (hn : N < n) : endpointCount N n = 0 :=
  endpointCount_zero_of_no_endpoint N n (by rintro ⟨k,hk⟩; omega)

theorem legal_endpoint_iff (N n : ℕ) :
    (∃ k : ℕ, N=n+2*k) ↔ n ≤ N ∧ N%2=n%2 := by
  constructor
  · rintro ⟨k,hk⟩
    omega
  · rintro ⟨hn,hp⟩
    exact ⟨(N-n)/2, by omega⟩

theorem endpointCount_illegal (N n : ℕ) (h : N<n ∨ N%2 ≠ n%2) : endpointCount N n = 0 := by
  apply endpointCount_zero_of_no_endpoint N n
  rw [legal_endpoint_iff]
  omega

end FiniteCopy.EndpointCounting
