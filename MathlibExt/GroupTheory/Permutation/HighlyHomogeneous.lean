/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

namespace MetaMathlibExt

@[expose] public section

/-- A permutation group is highly homogeneous when it has a single orbit on `k`-element
subsets of `α` for every `k`. -/
def IsHighlyHomogeneous {α : Type*} [DecidableEq α]
    (G : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ k : ℕ, MulAction.IsPretransitive G ↑(Set.powersetCard α k)

/-- The full symmetric group is highly homogeneous: every `k`-element subset can be
carried to any other by some permutation. -/
theorem isHighlyHomogeneous_top {α : Type*} [DecidableEq α] :
    IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm α)) := by
  intro k
  have hbase : MulAction.IsPretransitive (Equiv.Perm α) ↥(Set.powersetCard α k) :=
    Set.powersetCard.isPretransitive
  constructor
  intro x y
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Equiv.Perm α) x y
  exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩

end

end MetaMathlibExt
