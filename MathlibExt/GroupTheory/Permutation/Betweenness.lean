module

public import Mathlib.Algebra.Group.Subgroup.Basic

namespace MetaMathlibExt

@[expose] public section

/-- The ternary linear-betweenness relation on a linear order: `b` lies strictly
between `a` and `c` in either direction. -/
def isBetween (α : Type*) [LT α] (a b c : α) : Prop :=
  (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- The subgroup of permutations of a linear order preserving linear betweenness in
both directions. -/
def betweennessAutSubgroup (α : Type*) [LinearOrder α] : Subgroup (Equiv.Perm α) where
  carrier := { σ | ∀ a b c : α, isBetween α a b c ↔ isBetween α (σ a) (σ b) (σ c) }
  mul_mem' := by
    intro σ τ hσ hτ a b c
    change isBetween α a b c ↔
      isBetween α (σ (τ a)) (σ (τ b)) (σ (τ c))
    exact (hτ a b c).trans (hσ (τ a) (τ b) (τ c))
  one_mem' := by
    intro a b c
    simp [Equiv.Perm.coe_one, isBetween]
  inv_mem' := by
    intro σ hσ a b c
    have h := hσ (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c)
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h.symm

end

end MetaMathlibExt
