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

/-- The subgroup of permutations of a circular order preserving `btw` in both directions. -/
def circularOrderAutSubgroup (α : Type*) [CircularOrder α] : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a b c, btw a b c ↔ btw (σ a) (σ b) (σ c)}
  one_mem' a b c := by simp
  mul_mem' {σ τ} hσ hτ a b c := by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact (hτ a b c).trans (hσ _ _ _)
  inv_mem' {σ} hσ a b c := by
    have h := (hσ (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹ c)).symm
    simpa [Equiv.apply_symm_apply] using h

@[simp]
theorem mem_circularOrderAutSubgroup {α : Type*} [CircularOrder α] (σ : Equiv.Perm α) :
    σ ∈ circularOrderAutSubgroup α ↔ ∀ a b c, btw a b c ↔ btw (σ a) (σ b) (σ c) :=
  Iff.rfl

end

end MetaMathlibExt
