/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

example {α : Type*} [AddCommMonoid α] (a : α) : Set.IsSidon ({a} : Set α) := by
  intro x hx y hy z hz w hw _
  subst x
  subst y
  subst z
  subst w
  exact Or.inl ⟨rfl, rfl⟩
