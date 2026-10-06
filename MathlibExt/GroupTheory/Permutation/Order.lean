module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Perm.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Order automorphisms: permutations preserving `<` in both directions. -/
def orderAutSubgroup (α : Type*) [LT α] : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a b, a < b ↔ σ a < σ b}
  one_mem' a b := by simp
  mul_mem' hσ hτ a b := (hτ a b).trans (hσ _ _)
  inv_mem' {σ} h a b := by simpa using (h (σ⁻¹ a) (σ⁻¹ b)).symm

@[simp]
public theorem mem_orderAutSubgroup {α : Type*} [LT α] (σ : Equiv.Perm α) :
    σ ∈ orderAutSubgroup α ↔ ∀ a b, a < b ↔ σ a < σ b :=
  Iff.rfl

end

end MetaMathlibExt
