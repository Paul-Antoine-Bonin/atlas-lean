/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Order.Circular

namespace MetaMathlibExt

@[expose] public section

/-- The quaternary separation relation on a circular order: the pairs
`a, b` and `c, d` separate each other around the circle. -/
def circularSeparates {α : Type*} [CircularOrder α] (a b c d : α) : Prop :=
  (sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a)

/-- The subgroup of permutations of a circular order preserving separation
in both directions. -/
def separationAutSubgroup (α : Type*) [CircularOrder α] : Subgroup (Equiv.Perm α) where
  carrier :=
    {σ | ∀ a b c d, circularSeparates a b c d ↔
      circularSeparates (σ a) (σ b) (σ c) (σ d)}
  one_mem' a b c d := by simp
  mul_mem' {σ τ} hσ hτ a b c d := by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact (hτ a b c d).trans (hσ _ _ _ _)
  inv_mem' {σ} hσ a b c d := by
    have h := (hσ (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c) (σ⁻¹ d)).symm
    simpa [Equiv.apply_symm_apply] using h

@[simp]
theorem mem_separationAutSubgroup {α : Type*} [CircularOrder α] (σ : Equiv.Perm α) :
    σ ∈ separationAutSubgroup α ↔ ∀ a b c d, circularSeparates a b c d ↔
      circularSeparates (σ a) (σ b) (σ c) (σ d) :=
  Iff.rfl

end

end MetaMathlibExt
