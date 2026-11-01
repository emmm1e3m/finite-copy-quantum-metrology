import FiniteCopy.Compatibility
open scoped BigOperators
noncomputable section
namespace CopyQuantumMetrology.SpinPaths

structure Signature where
  Block : Type
  finite : Fintype Block
  spin : Block → ℕ

attribute [instance] Signature.finite
noncomputable instance (S : Signature) : DecidableEq S.Block := Classical.decEq _

def Signature.next (S : Signature) : Signature where
  Block := S.Block ⊕ {b : S.Block // 0 < S.spin b}
  finite := inferInstance
  spin := Sum.elim (fun b => S.spin b+1) (fun b => S.spin b.val-1)

def signature : ℕ → Signature
  | 0 => ⟨PUnit, inferInstance, fun _ => 0⟩
  | N+1 => (signature N).next

abbrev B (N : ℕ) := (signature N).Block
abbrev spin (N : ℕ) : B N → ℕ := (signature N).spin

instance (N : ℕ) : Fintype (B N) := (signature N).finite
noncomputable instance (N : ℕ) : DecidableEq (B N) := Classical.decEq _

@[simp] theorem spin_zero (b : B 0) : spin 0 b = 0 := rfl
@[simp] theorem spin_up (N : ℕ) (b : B N) : spin (N+1) (Sum.inl b) = spin N b+1 := rfl
@[simp] theorem spin_down (N : ℕ) (b : {b : B N // 0 < spin N b}) :
    spin (N+1) (Sum.inr b) = spin N b.val-1 := rfl

theorem sum_succ {α : Type*} [AddCommMonoid α] (N : ℕ) (f : B (N+1) → α) :
    (∑ b, f b) = (∑ b : B N, f (Sum.inl b)) +
      ∑ b : {b : B N // 0 < spin N b}, f (Sum.inr b) := by
  exact Fintype.sum_sum_type f

abbrev Signature.Space (S : Signature) := Σ b : S.Block, Fin (S.spin b+1)
abbrev Space (N : ℕ) := (signature N).Space

end CopyQuantumMetrology.SpinPaths
